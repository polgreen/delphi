#include "oracle_interface.h"
#include "oracle_response_parser.h"
#include "oracle_solver.h"
#include "../expr2sygus.h"

#include <solvers/smt2/smt2_dec.h>

#include <langapi/language_util.h>

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/boolbv.h>

#include <util/format_expr.h>
#include <util/replace_expr.h>
#include <util/replace_symbol.h>
#include <util/run.h>

#include <iostream>


void oracle_interfacet::replace_synth_fun_parameters(const problemt &problem, std::map <symbol_exprt, exprt> &solution_functions)
{
  for(const auto &sf: problem.synthesis_functions)
  {
    const auto &args = sf.second.parameters;
    auto sol = solution_functions.find(symbol_exprt(sf.first, sf.second.type));
    if(sol==solution_functions.end())
      std::cout<<"warning, no solution for synth fun "<< id2string(sf.first)<<std::endl;

    const auto &domain = to_mathematical_function_type(sf.second.type).domain();
    for(std::size_t i=0; i< domain.size(); i++)
      replace_expr(symbol_exprt(clean_id(args[i]), domain[i]), symbol_exprt("synth::parameter"+integer2string(i),domain[i]),sol->second);
  }

}

void oracle_interfacet::add_problem(const problemt &problem, const solutiont &solution, oracle_solvert &solver)
{
  // add verification problem "/exists x /neg (/alpha \implies \phi"
  verify_encoding.clear();
  verify_encodingt::check_function_bodies(solution.functions);
  verify_encoding.functions = solution.functions;
  replace_synth_fun_parameters(problem, verify_encoding.functions);
  
  verify_encoding.free_variables = problem.free_variables;
  
  const exprt encoded_constraints = (problem.assumptions.size()>1)?
      verify_encoding(implies_exprt(conjunction(problem.assumptions),conjunction(problem.constraints))): 
      verify_encoding(conjunction(problem.constraints));

  solver.set_to_false(encoded_constraints);
}


bool contains_synth_fun_app(const exprt &expr, const problemt &problem)
{
  if(expr.id()==ID_symbol)
  {
    auto func_id = to_symbol_expr(expr).get_identifier();
    if(problem.synthesis_functions.find(func_id)!=problem.synthesis_functions.end())
    {
      return true;
    }
  }
  for(const auto &op: expr.operands())
  {
    if(contains_synth_fun_app(op, problem))
      return true;
  }
  return false;
}

bool oracle_interfacet::replace_oracles(exprt &expr, const problemt &problem, oracle_solvert &solver)
{
  for (auto &op : expr.operands())
    if (!replace_oracles(op, problem, solver))
      return false;


  if (expr.id() == ID_function_application)
  {
    auto &func_app = to_function_application_expr(expr);
    auto &id = to_symbol_expr(func_app.function()).get_identifier();
    // is oracle application
    if (problem.oracle_symbols.find(id) != problem.oracle_symbols.end())
    {
      if (problem.second_order_oracles.find(id) != problem.second_order_oracles.end())
        return false;

      for(const auto &arg: func_app.arguments())
      {
        if(contains_synth_fun_app(arg, problem))
          return false;
        // if(arg.id()==ID_function_application)
        // {
        //   std::cout<<"is a function app"<<std::endl;
        //   return true;
        // }
      }  
      exprt result = solver.get_oracle_value(func_app);
      if (result != nil_exprt())
      {
        expr = result;
      }
    }
  }
  return true;
}

void oracle_interfacet::call_second_order_oracles(oracle_solvert &solver, 
                  const solutiont &solution, const problemt &problem)
{
  // pre-call all oracles that use 
  for(const auto &app: solver.applications)
  {
    for(const auto &arg: app.first.arguments())
    {
      if(arg.type().id()==ID_bool && arg.id()==ID_symbol)
      {
        std::string prefix = "_synthbool_";
        std::string arg_name = id2string(to_symbol_expr(arg).get_identifier());
        if(arg_name.size()<prefix.size())
          continue;

        if(std::string(arg_name, 0, prefix.size())==prefix)
        {
          std::string synth_fun_name(arg_name, prefix.size(), std::string::npos);
          INVARIANT(app.first.arguments().size()==1, "do not support 2nd order oracles with more than one arg");
          // call oracle
          std::vector<std::string> argv;
          argv.push_back(app.second.binary_name);

          for(const auto &func: solution.functions)
            if(synth_fun_name == id2string(func.first.get_identifier()))
            {
              const auto& synth_fun_id = func.first.get_identifier();
  
              argv.push_back(std::string(
                expr2sygus_fun_def(func.first, func.second, problem.synthesis_functions.at(synth_fun_id).parameters)));
              break;
            }

          exprt response = solver.make_oracle_call(app.second.binary_name,argv);
          // std::cout<<"Oracle response "<<expr2sygus(response)<<std::endl;
          // overwrite history for this oracle
          solver.oracle_call_history[app.second.binary_name] = oracle_solvert::oracle_historyt();
          // force response to be correct response regardless of boolean input value
          std::vector<exprt> all_true_inputs = {true_exprt()};
          std::vector<exprt> all_false_inputs = {false_exprt()};
          solver.oracle_call_history[app.second.binary_name][all_true_inputs] = response;
          solver.oracle_call_history[app.second.binary_name][all_false_inputs] = response;
        } 
      }
    }
  }
}


void oracle_interfacet::build_counterexample_constraint(oracle_solvert &solver, 
    const counterexamplet &counterexample, problemt &problem)
{ 
  counterexamplet result;
  // get counterexample
  for(const auto &var : problem.free_variables)
  {
    exprt value=solver.get(var);
    result.assignment[var]=value;
    if(value==nil_exprt() && var.id()==ID_nondet_symbol)
    {
      nondet_symbol_exprt tmp_var=to_nondet_symbol_expr(var);
      tmp_var.set_identifier("nondet_"+id2string(to_nondet_symbol_expr(var).get_identifier()));
      value=solver.get(tmp_var);
      result.assignment[var]=value;
    }
    if(value==nil_exprt())
    {
      std::cout << "Warning: unable to find value for "<< var.pretty()<<std::endl;
      result.assignment[var] = constant_exprt("0", var.type());
      std::cout<<"Assume has been simplified out by solver.\n" <<std::endl;
    }
  }

  // make constraint from counterexample and problem
  for(auto &p: problem.constraints)
  {
    exprt synthesis_constraint = p;
    replace_expr(result.assignment, synthesis_constraint);
    // if(!replace_expr(result.assignment, synthesis_constraint))
      // std::cout<<"warning adding counterexample into constraint did nothing \n";

    if(!replace_oracles(synthesis_constraint, problem, solver))
    {
      std::cout<<"Did not manage to replace oracles "<<std::endl;
      continue;
    }

    if(synthesis_constraint.id()==ID_and)
    {
      for(const auto &op: synthesis_constraint.operands())
        problem.synthesis_constraints.insert(std::move(op));
    }
    else
      problem.synthesis_constraints.insert(std::move(synthesis_constraint));
  }   
}

void oracle_interfacet::get_oracle_constraints(
  const counterexamplet &counterexample,
  const oracle_constraint_gent &oracle,
  problemt &problem,
  const solutiont &solution)
{
  std::vector<std::string> argv;

  argv.push_back(id2string(oracle.binary_name));

  replace_symbolt replace_symbol;

  for(const auto &input_parameter : oracle.input_parameters)
  {
    std::ostringstream stream;

    auto value_it = counterexample.assignment.find(input_parameter);
    if(value_it == counterexample.assignment.end())
    {
      // is this a synthesis function
      if(problem.synthesis_functions.find(input_parameter.get_identifier())!=problem.synthesis_functions.end())
      {
        if(solution.functions.find(input_parameter)==solution.functions.end())
          stream << expr2sygus_fun_def(input_parameter, true_exprt());
        else
          stream << expr2sygus_fun_def(input_parameter, solution.functions.at(input_parameter), problem.synthesis_functions.at(input_parameter.get_identifier()).parameters);
      }
      else
      {
        log.error() << "no value in counterexample for " << format(input_parameter) << messaget::eom;
      }
    }
    else
    {
      replace_symbol.set(to_symbol_expr(input_parameter), value_it->second);
      stream << format(value_it->second);
    }
    
    argv.push_back(stream.str());
  }

  log.debug() << "Running oracle (synthesis)";
  for (auto &arg : argv)
    log.debug() << ' ' << arg;
  log.debug() << messaget::eom;

  // run the oracle binary
  std::ostringstream stdout_stream;

  auto run_result = run(
    id2string(oracle.binary_name),
      argv,
      "",
      stdout_stream,
      "");

  if (run_result != 0 && run_result != 10)
  {
    log.status() << "oracle " << oracle.binary_name << " has failed, run result "<< integer2string(run_result) << messaget::eom;
    assert(0);
  }

  // we assume that the oracle returns the result in SMT-LIB format,
  // separated by spaces
  
  std::istringstream oracle_response_istream(stdout_stream.str());
  std::size_t count=0;
  while(oracle_response_istream )
  {
    if(count > 10)
      break;
    count++;
    for (auto &return_parameter : oracle.return_parameters)
    {
      try{
      auto response = oracle_response_parser(oracle_response_istream);
      log.debug() << "oracle response for " << format(return_parameter)
                  << ": " << expr2sygus(response) << messaget::eom;
      replace_symbol.set(to_symbol_expr(return_parameter), response);
      }
      catch(...){}
    }
      // build constraint
    exprt constraint = oracle.constraint;
    replace_symbol(constraint);

    log.status() << "oracle constraint: "
              << expr2sygus(constraint) << messaget::eom;
    problem.synthesis_constraints.insert(constraint);
  }

}

void oracle_interfacet::call_oracles(
  problemt &problem, 
  const solutiont &solution,
  const counterexamplet &counterexample,
  oracle_solvert &solver)
{
  // call the other oracles here

  // for all problem.oracle_constraint_gen
  // call the oracle and add the constraints to problem.synthesis_constraints
  for(const auto &oracle : problem.oracle_constraint_gens)
  {
    get_oracle_constraints(counterexample, oracle, problem, solution);
  }

  // for all problem.oracle_assumption_gen
  // call the oracle and add the assumptions to problem.assumptions
  for(const auto &oracle : problem.oracle_assumption_gens)
  {
    get_oracle_constraints(counterexample, oracle, problem, solution);
  }
}

void oracle_interfacet::add_assumptions_from_solver(const oracle_solvert &solver, problemt &problem)
{
  for(const auto &oracle: problem.oracle_symbols)
  {
    if(solver.oracle_call_history.find(oracle.second.binary_name)==solver.oracle_call_history.end())
      continue;

    symbol_exprt func_symbol = symbol_exprt(oracle.first, oracle.second.type);
    bool is_second_order=false;
    for(const auto &arg: to_mathematical_function_type(oracle.second.type).domain())
    {
      if(arg.id()==ID_mathematical_function)
        is_second_order=true;
    }
    if (!is_second_order)
    {
      for (const auto &call : solver.oracle_call_history.at(oracle.second.binary_name))
      {
        exprt assumption = equal_exprt(function_application_exprt(func_symbol, call.first),
                                       call.second);
        problem.assumptions.push_back(assumption);
      }
    }
  }
}

oracle_interfacet::resultt oracle_interfacet::operator()(problemt &problem,
                                                         const solutiont &solution)
{
  // get solver
  if(bitblast)
  {
    satcheck_minisat_no_simplifiert satcheck_minisat_no_simplifier(log.get_message_handler());
    boolbvt subsolver(ns, satcheck_minisat_no_simplifier, log.get_message_handler());
    oracle_solvert oracle_solver(subsolver, log.get_message_handler());
    oracle_solver.oracle_fun_map = &problem.oracle_symbols;
    return this->operator()(problem, solution, oracle_solver);
  }
  smt2_dect subsolver(
      ns, "fastsynth", "generated by fastsynth",
      "ALL", smt2_dect::solvert::CVC4, log.get_message_handler());
   oracle_solvert oracle_solver(subsolver, log.get_message_handler());
   oracle_solver.oracle_fun_map=&problem.oracle_symbols; 
  oracle_solver.oracle_call_history = copy_of_solver_history;
  return this->operator()(problem, solution, oracle_solver);
}





void block_previous_solution(problemt &problem, const solutiont &solution)
{
  for(const auto &f: solution.functions)
  {
    if(f.first.type().id()!=ID_mathematical_function)
      continue;
    auto &func = to_mathematical_function_type(f.first.type());
    if(func.domain().size()==0)
    {
      equal_exprt equals(function_application_exprt(f.first,{}),f.second);
      not_exprt blocking_expr(equals);
      problem.synthesis_constraints.insert(blocking_expr);
    }
    // TODO block n-ary funcs as well as 0-ary functions
  }
}

oracle_interfacet::resultt oracle_interfacet::operator()(problemt &problem,
    const solutiont &solution,
    oracle_solvert &solver)
  {

    add_problem(problem, solution, solver);
    call_second_order_oracles(solver, solution, problem);
    decision_proceduret::resultt result = solver();

    switch(result)
    {
      case decision_proceduret::resultt::D_SATISFIABLE:
      {
        counterexample = verify_encoding.get_counterexample(solver);
        build_counterexample_constraint(solver, counterexample, problem);
        add_assumptions_from_solver(solver, problem);
        call_oracles(problem, solution, counterexample, solver);
        block_previous_solution(problem, solution);
        copy_of_solver_history = solver.oracle_call_history;
        return oracle_interfacet::resultt::FAIL; 
      }
      case decision_proceduret::resultt::D_UNSATISFIABLE:
      {
        counterexample.clear();
        return oracle_interfacet::resultt::PASS;
      }

      case decision_proceduret::resultt::D_ERROR:
      default:
      {
        std::cout<<"ERROR oracle interface\n";
        counterexample=
        verify_encoding.get_counterexample(solver);
        call_oracles(problem, solution, counterexample, solver);
        return oracle_interfacet::resultt::FAIL;
      } 
    }
  }

counterexamplet oracle_interfacet::get_counterexample()
{
  return counterexample;
}  