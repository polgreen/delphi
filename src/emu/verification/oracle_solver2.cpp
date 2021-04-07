#include "oracle_solver2.h"

#include "oracle_response_parser.h"
#include "../expr2sygus.h"

#include <util/expr.h>
#include <util/format_expr.h>
#include <util/run.h>
#include <util/std_expr.h>
#include <util/string_utils.h>

#include <sstream>
#include <iostream>

negation_oracle_solvert::negation_oracle_solvert(
  decision_proceduret &__negation_sub_solver,
    decision_proceduret &__sub_solver,
  message_handlert &__message_handler) :
  oracle_solvert(__sub_solver, __message_handler),
    negation_sub_solver(__negation_sub_solver)
{
}



void negation_oracle_solvert::set_to(const exprt &expr, bool value)
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
  negation_sub_solver.set_to(expr, !value);
}



negation_oracle_solvert::check_resultt negation_oracle_solvert::check_oracle(
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
  if(response == negation_sub_solver.get(application.handle))
  {
    log.debug() << "Response matches " << expr2sygus(get(application.handle))<<messaget::eom;
    return CONSISTENT; // done, SAT
  }
  {

    function_application_exprt func_app(application_expr.function(), inputs);

    log.debug() << "Response does not match " << expr2sygus(get(application.handle)) << messaget::eom;

    // add a constraint that enforces this equality
    auto response_equality = equal_exprt(application.handle, response);

    exprt::operandst input_constraints;

    for (auto &argument_handle : application.argument_handles)
      input_constraints.push_back(equal_exprt(argument_handle, get(argument_handle)));

    // add 'all inputs equal' => 'return value equal'
    auto implication =
        implies_exprt(
            conjunction(input_constraints),
            response_equality);
    sub_solver.set_to_true(implication);
    // this is actually setting to true, because set_to negates the value for the negation sub solver
    negation_sub_solver.set_to_false(implication);
    // set_to_true(implication);        

  }
  return INCONSISTENT;
}



decision_proceduret::resultt negation_oracle_solvert::dec_solve()
{
  PRECONDITION(oracle_fun_map != nullptr);

  number_of_solver_calls++;

  while(true)
  {
    switch(sub_solver())
    {
      case resultt::D_UNSATISFIABLE:
        return resultt::D_UNSATISFIABLE;
      case resultt::D_ERROR:
        return resultt::D_ERROR;
      case resultt::D_SATISFIABLE:
        log.debug()<<"Found satisfing counterexample \n";
      // currently do nothing, but consider calling oracles here
    }

    switch(negation_sub_solver())
    {
    case resultt::D_SATISFIABLE:
      check_oracles();
      break;

    case resultt::D_UNSATISFIABLE:
      return resultt::D_SATISFIABLE;

    case resultt::D_ERROR:
      return resultt::D_ERROR;
    }
  }
}
