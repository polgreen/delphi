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
  oracle_fun_mapt &__oracle_fun_map,
  message_handlert &__message_handler) :
  sub_solver(__sub_solver),
  oracle_fun_map(__oracle_fun_map),
  log(__message_handler)
{
}

void oracle_solvert::replace_oracle_fun_map(oracle_fun_mapt &new_oracle_fun_map)
{
  oracle_fun_map = new_oracle_fun_map;
}

void oracle_solvert::set_to(const exprt &expr, bool value)
{
  // find any oracle function applications
  expr.visit_pre([this](const exprt &src) {
    if(src.id() == ID_function_application)
    {
      const auto &application = to_function_application_expr(src);
      if(application.function().id() == ID_symbol)
      {
        // look up whether it is an oracle
        auto identifier = to_symbol_expr(application.function()).get_identifier();
        auto oracle_fun_map_it = oracle_fun_map.find(identifier);
        if(oracle_fun_map_it != oracle_fun_map.end())
          applications.insert(application); // yes
      }
    }
  });

  sub_solver.set_to(expr, value);
}

exprt oracle_solvert::handle(const exprt &expr)
{
  return sub_solver.handle(expr);
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
    switch(check_oracle(application))
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
  const function_application_exprt &application)
{
  PRECONDITION(application.function().id() == ID_symbol);

  auto &type = to_mathematical_function_type(application.function().type());

  // evaluate the arguments to get inputs
  std::vector<exprt> inputs;
  inputs.reserve(type.domain().size());

  for(auto &argument : application.arguments())
    inputs.push_back(get(argument));

  // look up the oracle
  auto identifier = to_symbol_expr(application.function()).get_identifier();
  auto oracle_fun_map_it = oracle_fun_map.find(identifier);
  DATA_INVARIANT(oracle_fun_map_it != oracle_fun_map.end(), "oracle not found");

  const auto &oracle = oracle_fun_map_it->second;

  std::vector<std::string> argv;
  argv.push_back(id2string(oracle.binary_name));

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
    id2string(oracle.binary_name),
    argv,
    "",
    stdout_stream,
    "");

  if(run_result != 0)
  {
    log.error() << "oracle " << oracle.binary_name << " has failed" << messaget::eom;
    return ERROR;
  }

  // we assume that the oracle returns the result in SMT-LIB format
  std::istringstream oracle_response_istream(stdout_stream.str());
  auto response = oracle_response_parser(oracle_response_istream);

  // check whether the constraint is already satisfied
  auto response_equality = equal_exprt(application, response);

  if(get(response_equality).is_true())
    return CONSISTENT; // done, SAT

  // add a constraint
  exprt::operandst input_constraints;

  for(auto &argument : application.arguments())
    input_constraints.push_back(equal_exprt(argument, get(argument)));

  // add 'all inputs equal' => 'return value equal'
  set_to_true(implies_exprt(
    conjunction(input_constraints),
    response_equality));

  return INCONSISTENT;
}

exprt oracle_solvert::parse(const std::string &text) const
{
  return true_exprt();
}

decision_proceduret::resultt oracle_solvert::dec_solve()
{
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
