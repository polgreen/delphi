#include "oracle_solver.h"

#include "oracle_response_parser.h"

#include <util/expr.h>
#include <util/format_expr.h>
#include <util/run.h>
#include <util/std_expr.h>
#include <util/string_utils.h>

#include <sstream>

oracle_solvert::oracle_solvert(
  decision_proceduret &__sub_solver,
  message_handlert &__message_handler) :
  sub_solver(__sub_solver),
  log(__message_handler)
{
}

void oracle_solvert::set_to(const exprt &expr, bool value)
{
  PRECONDITION(oracle_fun_map != nullptr);

  // find any oracle function applications
  expr.visit_pre([this](const exprt &src) {
    if(src.id() == ID_function_application)
    {
      const auto &application_expr = to_function_application_expr(src);
      if(application_expr.function().id() == ID_symbol)
      {
        // look up whether it is an oracle
        auto identifier = to_symbol_expr(application_expr.function()).get_identifier();
        auto oracle_fun_map_it = oracle_fun_map->find(identifier);
        if(oracle_fun_map_it != oracle_fun_map->end())
        {
          // yes
          if(applications.find(application_expr) == applications.end())
          {
            // not seen before
            auto &application = applications[application_expr];
            application.binary_name = oracle_fun_map_it->second.binary_name;
            application.handle = handle(application_expr);

            application.argument_handles.reserve(application_expr.arguments().size());

            for(auto &argument : application_expr.arguments())
              application.argument_handles.push_back(handle(argument));
          }
        }
      }
    }
  });

  sub_solver.set_to(expr, value);
}

exprt oracle_solvert::handle(const exprt &expr)
{
  if(expr.id() == ID_symbol || expr.is_constant())
    return expr;
  else
  {
    symbol_exprt symbol_expr("H"+std::to_string(handle_counter++), expr.type());
    set_to_true(equal_exprt(symbol_expr, expr));
    return std::move(symbol_expr);
  }
}

exprt oracle_solvert::get(const exprt &expr) const
{
  return sub_solver.get(expr);
}

void oracle_solvert::print_assignment(std::ostream &out) const
{
  sub_solver.print_assignment(out);
}

std::string oracle_solvert::decision_procedure_text() const
{
  return "oracles + " + sub_solver.decision_procedure_text();
}

oracle_solvert::check_resultt oracle_solvert::check_oracles()
{
  oracle_solvert::check_resultt result = CONSISTENT;

  for(const auto &application : applications)
  {
    switch(check_oracle(application.first, application.second))
    {
    case INCONSISTENT:
      result = INCONSISTENT;
      break;

    case CONSISTENT:
      break;

    case ERROR:
      return ERROR; // abort
    }
  }

  return result;
}

oracle_solvert::check_resultt oracle_solvert::check_oracle(
  const function_application_exprt &application_expr,
  const applicationt &application)
{
  // evaluate the argument handles to get concrete inputs
  std::vector<exprt> inputs;
  inputs.reserve(application.argument_handles.size());

  for(auto &argument_handle : application.argument_handles)
    inputs.push_back(get(argument_handle));

  std::vector<std::string> argv;
  argv.push_back(application.binary_name);

  for(const auto &input : inputs)
  {
    std::ostringstream stream;
    stream << format(input);
    argv.push_back(stream.str());
  }

  log.status() << "Running oracle";
  for(auto &arg : argv)
    log.status() << ' ' << arg;
  log.status() << messaget::eom;

  // run the oracle binary
  std::ostringstream stdout_stream;
  
  auto run_result = run(
    id2string(application.binary_name),
    argv,
    "",
    stdout_stream,
    "");

  if(run_result != 0)
  {
    log.error() << "oracle " << application.binary_name << " has failed" << messaget::eom;
    return ERROR;
  }

  // we assume that the oracle returns the result in SMT-LIB format
  std::istringstream oracle_response_istream(stdout_stream.str());
  auto response = oracle_response_parser(oracle_response_istream);

  // check whether the constraint is already satisfied
  auto response_equality = equal_exprt(application.handle, response);

  if(get(response_equality).is_true())
    return CONSISTENT; // done, SAT

  // add a constraint
  exprt::operandst input_constraints;

  for(auto &argument_handle : application.argument_handles)
    input_constraints.push_back(equal_exprt(argument_handle, get(argument_handle)));

  // add 'all inputs equal' => 'return value equal'
  set_to_true(implies_exprt(
    conjunction(input_constraints),
    response_equality));

  return INCONSISTENT;
}

decision_proceduret::resultt oracle_solvert::dec_solve()
{
  PRECONDITION(oracle_fun_map != nullptr);

  number_of_solver_calls++;

  while(true)
  {
    switch(sub_solver())
    {
    case resultt::D_SATISFIABLE:
      switch(check_oracles())
      {
      case INCONSISTENT:
        break; // constraint added, we'll do another iteration

      case CONSISTENT:
        return resultt::D_SATISFIABLE;

      case ERROR:
        return resultt::D_ERROR;
      }

    case resultt::D_UNSATISFIABLE:
      return resultt::D_UNSATISFIABLE;

    case resultt::D_ERROR:
      return resultt::D_ERROR;
    }
  }
}
