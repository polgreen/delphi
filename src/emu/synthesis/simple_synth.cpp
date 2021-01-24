#include "simple_synth.h"
#include <solvers/smt2/smt2_dec.h>
#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>
#include <util/mathematical_expr.h>
#include "../expr2sygus.h"
#include <algorithm>

void simple_syntht::set_program_size(std::size_t size)
{
  program_size = size;
}

void simple_syntht::increment_synthesis_constraints()
{
  number_synth_constraints+=synth_constraint_increment;
}

bool contains_oracle(exprt expr, const problemt &problem)
{
  // if (expr.type().id() == ID_mathematical_function &&
  //     problem.synthesis_functions.find(to_symbol_expr(expr).get_identifier()) ==
  //         problem.synthesis_functions.end())
  //   return true;
  // else
  //   forall_operands(it, expr) 
  //     if(contains_oracle(*it, problem)) 
  //       return true;

  return false;
}

exprt join_expressions(const std::vector<exprt> &expressions, irep_idt id, const problemt &problem)
{
  INVARIANT(id == ID_or || id == ID_and, "expected ID_and or ID_or for join expressions");
  switch (expressions.size())
  {
  case 0:
    return true_exprt();
  case 1:
    return contains_oracle(expressions[0], problem) ? true_exprt() : expressions[0];
  default:
    std::set<std::size_t> indices;
    for (std::size_t i = 0; i < expressions.size(); i++)
      if (contains_oracle(expressions[i], problem))
        indices.insert(i);

    if (indices.size() == 0)
      if (id == ID_or)
        return or_exprt(expressions);
      else
        return and_exprt(expressions);
    else
    {
      std::vector<exprt> copy_of_expressions;
      for (std::size_t i = 0; i < expressions.size(); i++)
      {
        if (indices.find(i) == indices.end())
          copy_of_expressions.push_back(expressions[i]);
      }
      switch (copy_of_expressions.size())
      {
      case 0:
        return true_exprt();
      case 1:
        return copy_of_expressions[0];
      default:
        if (id == ID_or)
          return or_exprt(copy_of_expressions);
        else
          return and_exprt(copy_of_expressions);
      }
    }
  }
}

void simple_syntht::add_problem(synth_encodingt &encoding, decision_proceduret &solver, const problemt &problem)
{
  std::cout << "Using  " << std::min(number_synth_constraints, problem.synthesis_constraints.size()) 
            << " synthesis constraints"<<std::endl;
  // TODO: use assumptions here as well?
  for(std::size_t i=0; i<number_synth_constraints; i++)
  {
    if(i>= problem.synthesis_constraints.size())
      break;
    const exprt encoded =encoding(problem.synthesis_constraints[i]);
    solver.set_to_true(encoded);
  }

  for(const auto &c : encoding.constraints)
    solver.set_to_true(c);
}


simple_syntht::resultt simple_syntht::operator()(const problemt &problem)
{
  // // get solver
  smt2_dect solver(
      ns, "fastsynth", "generated by fastsynth",
      logic, smt2_dect::solvert::Z3, message_handler);
  // satcheck_minisat_no_simplifiert satcheck_minisat_no_simplifiert(message_handler);
  // boolbvt solver(ns, satcheck_minisat_no_simplifiert, message_handler);   

  return this->operator()(problem, solver);
}

simple_syntht::resultt simple_syntht::operator()(const problemt &problem, decision_proceduret &solver)
{
  // add the problem to the solver (synthesis_assumptions => (assumptions => constraints))
  synth_encoding.program_size = program_size;
  synth_encoding.clear();
  synth_encoding.enable_bitwise = false;

  synth_encoding.suffix = "$ce";
  add_problem(synth_encoding, solver, problem);
  
  // solve
  const decision_proceduret::resultt result = solver();
  switch (result)
  {
  case decision_proceduret::resultt::D_SATISFIABLE:
    last_solution = synth_encoding.get_solution(solver);
    return simple_syntht::resultt::CANDIDATE;

  case decision_proceduret::resultt::D_UNSATISFIABLE:
    return simple_syntht::resultt::NO_SOLUTION;

  case decision_proceduret::resultt::D_ERROR:
  default:
    return simple_syntht::resultt::NO_SOLUTION;
  }
}

exprt simple_syntht::model(exprt expr) const
{
  assert(expr.id()==ID_symbol);
  auto iter = last_solution.functions.find(to_symbol_expr(expr));
  assert(iter!=last_solution.functions.end());
  return iter->second;
}

solutiont simple_syntht::get_solution() const
{
  return last_solution;
}

// void simple_syntht::add_ce(
//   const counterexamplet &counterexample)
// {
//   counterexamples.emplace_back(counterexample);
// }