#include "negation_oracle_solver.h"

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
    decision_proceduret &__sub_solver,
    decision_proceduret &__negation_sub_solver,
  message_handlert &__message_handler) :
  oracle_solvert(__sub_solver, __message_handler),
    negation_sub_solver(__negation_sub_solver),
    try_positive_model(false)
{
}

exprt negation_oracle_solvert::handle(const exprt &expr)
{
  if(expr.is_constant())
    return expr;
  else
  {
    symbol_exprt symbol_expr("H"+std::to_string(handle_counter++), expr.type());
    auto equality = equal_exprt(symbol_expr, expr);

    sub_solver.set_to(equality, true);
    negation_sub_solver.set_to(equality, true);
    return std::move(symbol_expr);
  }
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
  // we flip everything except the assumptions in the negation solver
  negation_sub_solver.set_to(expr, !value);
}



void negation_oracle_solvert::check_oracle(
  const function_application_exprt &application_expr,
  const applicationt &application,
  bool use_negation_oracle)
{
  log.status()<<"checking oracle app, use negation oracle "<< use_negation_oracle<<log.eom;
    // evaluate the argument handles to get concrete inputs
  std::vector<exprt> inputs;
  inputs.reserve(application.argument_handles.size());

  for(auto &argument_handle : application.argument_handles)
  {
    auto res = use_negation_oracle? negation_sub_solver.get(argument_handle):
      sub_solver.get(argument_handle);
    inputs.push_back(res);
    log.status()<<"input "<< expr2sygus(res)<<log.eom;
  } 

  bool is_new_call = true;
   exprt response = call_oracle(application, inputs, is_new_call);
   // return without adding implication
   if(response==nil_exprt())
     return;

  // // check whether the result is consistent with the model
  // if(response == negation_sub_solver.get(application.handle))
  // {
  //   log.debug() << "Response matches " << expr2sygus(negation_sub_solver.get(application.handle))<<messaget::eom;
  //   // return CONSISTENT; // done, SAT
  // }
  if(is_new_call)
  {
    function_application_exprt func_app(application_expr.function(), inputs);
    // add a constraint that enforces this equality
    auto response_equality = equal_exprt(application.handle, response);

    exprt::operandst input_constraints;

    for (auto &argument_handle : application.argument_handles)
      input_constraints.push_back(equal_exprt(argument_handle, 
      use_negation_oracle ? negation_sub_solver.get(argument_handle):
      sub_solver.get(argument_handle)
      ));
    
    // add 'all inputs equal' => 'return value equal'
    auto implication =
        implies_exprt(
            conjunction(input_constraints),
            response_equality);
    sub_solver.set_to(implication, true);
    negation_sub_solver.set_to(implication, true);
   }
   else
   {
     log.debug()<<"seen this oracle call before"<< log.eom;
     try_positive_model=true;
   }
}

// it doesn't matter whether the oracles are consistent
void negation_oracle_solvert::check_negation_solver_oracles()
{
  for(const auto &application : applications)
    check_oracle(application.first, application.second, true);
}


decision_proceduret::resultt negation_oracle_solvert::get_model()
{
  while(true)
  {
    switch(sub_solver())
    {
      case resultt::D_UNSATISFIABLE:
        return resultt::D_ERROR;
      case resultt::D_ERROR:
        return resultt::D_ERROR;
      case resultt::D_SATISFIABLE:
        log.status()<<"Found satisfing counterexample \n" <<log.eom;
        if(check_oracles()==CONSISTENT)
        {
          log.status()<<"consistent with oracles, problem is sat\n" <<log.eom;
          return resultt::D_SATISFIABLE;
        }
    }
  }
}

decision_proceduret::resultt negation_oracle_solvert::dec_solve()
{
  PRECONDITION(oracle_fun_map != nullptr);

  number_of_solver_calls++;
  if(oracle_fun_map->size()==0)
    try_positive_model = true;

  while(true)
  {
    switch(sub_solver())
    {
      case resultt::D_UNSATISFIABLE:
        return resultt::D_UNSATISFIABLE;
      case resultt::D_ERROR:
        return resultt::D_ERROR;
      case resultt::D_SATISFIABLE:
        log.status()<<"Found satisfing counterexample \n" <<log.eom;
        if(try_positive_model)
          if(check_oracles()==CONSISTENT)
          {
            log.status()<<"consistent with oracles, problem is sat\n" <<log.eom;
            return resultt::D_SATISFIABLE;
          }
    }
 
    switch(negation_sub_solver())
    {
    case resultt::D_SATISFIABLE:
      log.status()<<"negation witness \n"<<log.eom;
      check_negation_solver_oracles();
      break;
    case resultt::D_UNSATISFIABLE:
      log.status()<<"Found no negation subsolver assignment, problem is sat"<<log.eom;
      // call sub solver to get assignment
      if(get_model()==resultt::D_ERROR)
        return resultt::D_ERROR;
      return resultt::D_SATISFIABLE;
    case resultt::D_ERROR:
      return resultt::D_ERROR;
    }
  }
}
