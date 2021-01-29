#include "oracle_solver.h"

#include "oracle_response_parser.h"
#include "../expr2sygus.h"

#include <util/expr.h>
#include <util/format_expr.h>
#include <util/run.h>
#include <util/std_expr.h>
#include <util/string_utils.h>

#include <sstream>
#include <iostream>

oracle_solvert::oracle_solvert(
  decision_proceduret &__sub_solver,
  message_handlert &__message_handler) :
  sub_solver(__sub_solver),
  log(__message_handler)
{
}

exprt oracle_solvert::get_oracle_value(const function_application_exprt &oracle_app, const std::vector<exprt> &inputs)
{
  for(const auto &app : applications)
  {
    if(to_function_application_expr(app.first).function() == oracle_app.function())
    {
      auto history = oracle_call_history.find(app.second.binary_name);
      INVARIANT(history != oracle_call_history.end(), "No history for oracle");
      auto result = history->second.find(inputs);
      if(result==history->second.end())
      {
        return call_oracle(app.second, inputs);        
      }
      return result->second;
    }
  }
  return nil_exprt();
}

void oracle_solvert::set_to(const exprt &expr, bool value)
{
  PRECONDITION(oracle_fun_map != nullptr);

  // find any oracle function applications
  expr.visit_pre([this](const exprt &src) {
    if(src.id() == ID_function_application)
    {
      auto &application_expr = to_function_application_expr(src);
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
  if(expr.is_constant())
    return expr;
  else
  {
    symbol_exprt symbol_expr("H"+std::to_string(handle_counter++), expr.type());
    auto equality = equal_exprt(symbol_expr, expr);
    set_to_true(equality);
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

exprt oracle_solvert::make_oracle_call(const std::string &binary_name, const std::vector<std::string> &argv)
{
  log.status() << "Running oracle (verification), binary name "<< binary_name;
  for (auto &arg : argv)
    log.status() << ' ' << arg;
  log.status() << messaget::eom;

  // run the oracle binary
  std::ostringstream stdout_stream;

  auto run_result = run(
      binary_name,
      argv,
      "",
      stdout_stream,
      "");

  if (run_result != 0)
  {
    log.status() << "oracle " << binary_name << " has failed" << messaget::eom;
    assert(0);
    return nil_exprt();
  }
  // we assume that the oracle returns the result in SMT-LIB format
  std::istringstream oracle_response_istream(stdout_stream.str());
  std::cout<<"Response stream "<< stdout_stream.str()<<std::endl;
  return oracle_response_parser(oracle_response_istream);
}

exprt oracle_solvert::call_oracle(
    const applicationt &application, const std::vector<exprt> &inputs)
{
  if(cache && oracle_call_history.find(application.binary_name) == oracle_call_history.end())
  {
    oracle_call_history[application.binary_name] = oracle_historyt();
  }

  exprt response;

  if (oracle_call_history[application.binary_name].find(inputs) == oracle_call_history[application.binary_name].end() || !cache)
  {
    std::vector<std::string> argv;
    argv.push_back(application.binary_name);

    for (const auto &input : inputs)
    {
      std::ostringstream stream;
      stream << format(input);
      argv.push_back(stream.str());
    }

    response = make_oracle_call(application.binary_name, argv);
    log.status() << "oracle response " << expr2sygus(response) << messaget::eom;
    if (cache)
      oracle_call_history[application.binary_name][inputs] = response;
  }
  else
  {
    response = oracle_call_history[application.binary_name][inputs];
  }

  return response;
}

oracle_solvert::check_resultt oracle_solvert::check_oracle(
  const function_application_exprt &application_expr,
  const applicationt &application)
{
  
  // evaluate the argument handles to get concrete inputs
  std::vector<exprt> inputs;
  inputs.reserve(application.argument_handles.size());

  for(auto &argument_handle : application.argument_handles)
  {
    auto res = get(argument_handle);
    inputs.push_back(res);
  } 

   exprt response = call_oracle(application, inputs);
   if(response==nil_exprt())
     return check_resultt::ERROR;


  // check whether the result is consistent with the model
  if(response == get(application.handle))
  {
    log.debug() << "Response matches " << expr2sygus(get(application.handle))<<messaget::eom;
    return CONSISTENT; // done, SAT
  }
  {

    function_application_exprt func_app(application_expr.function(), inputs);

    log.debug() << "Response does not match " << expr2sygus(get(application.handle)) << messaget::eom;

    // add a constraint that enforces this equality
    auto response_equality = equal_exprt(application.handle, response);
    // auto response_equality = equal_exprt(func_app, response);
    // set_to_true(response_equality);

    exprt::operandst input_constraints;

    for (auto &argument_handle : application.argument_handles)
      input_constraints.push_back(equal_exprt(argument_handle, get(argument_handle)));

    // add 'all inputs equal' => 'return value equal'
    auto implication =
        implies_exprt(
            conjunction(input_constraints),
            response_equality);
    set_to_true(implication);        

  }
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
      break;

    case resultt::D_UNSATISFIABLE:
      return resultt::D_UNSATISFIABLE;

    case resultt::D_ERROR:
      return resultt::D_ERROR;
    }
  }
}
