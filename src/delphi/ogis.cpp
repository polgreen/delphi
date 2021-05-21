/*******************************************************************\
 *       \|/
       -=(')
         ;;
        //
       //
      : '.---.__
      |  --_-_)__)
      `.____,'
         \  \
       ___\  \
      (        \     EMU
               /

 Module: Oracle Guided Inductive Synthesis loop
 Author: Elizabeth Polgreen, epolgreen@gmail.com. 
\*******************************************************************/

#include "ogis.h"
#include "expr2sygus.h"
#include <langapi/language_util.h>

void output_expressions(
  const std::map<symbol_exprt, exprt> &expressions,
  const namespacet &ns,
  std::ostream &out)
{
  for(const auto &e : expressions)
  {
    out << e.first.get_identifier()
        << " -> "
        << from_expr(ns, "", e.second)
        << '\n';
  }
}

ogist::ogist(
  synthesizert &__synthesizer,
  verifyt &__verify,
  problemt &__problem, 
  namespacet &_ns) :
  increase_program_size(true),
  synthesizer(__synthesizer),
  verify(__verify),
  problem(__problem),
  ns(_ns)
{
  // get base problem
  // find correctness requirement, add to verifier
  // add oracle assumptions and constraints to verifier
  // set oracle selection strategy in verifier
  // set synthesis strategy
}
#include <iostream>

void display_solution(const solutiont &solution, std::vector<exprt> synth_fun_helpers)
{
  std::cout<<"SOLUTION:"<<std::endl;
  for(const auto & f: solution.functions)
  {
    if(synth_fun_helpers.size()==0)
      std::cout<<expr2sygus(f.first)<<"  =  "<<expr2sygus(f.second)<<std::endl;
    else
    {
      exprt result = f.second;
      for(const auto &h: synth_fun_helpers)
      {
        result = and_exprt(f.second, h);
      }
      std::cout<<expr2sygus(f.first)<<"  =  "<<expr2sygus(result)<<std::endl;
    }
  }
}

// problem is dynamic
ogist::resultt ogist::doit()
{
  std::cout<<"Start OGIS"<<std::endl;
  // the actual synthesis loop
  std::size_t program_size=1;
  std::size_t iteration=0;
  solutiont solution;
  bool switched_to_alternative_constraints=false;

  while(true)
  {
    iteration++;

    synthesizer.set_program_size(program_size);
    // synthesiser synthesise solution to problem so far
    std::cout<<"SYNTH iteration "<<iteration<<std::endl;
    switch(synthesizer(problem))
    {
    case synthesizert::CANDIDATE:
        std::cout<<"Got solution ";
        output_expressions(synthesizer.get_solution().functions, ns, std::cout);
        // got solution
        // check if solution is the same each time?
      break;
    case synthesizert::NO_SOLUTION:
      if(program_size<10 && increase_program_size)
      {
        program_size+=1;
        std::cout<<"increase program size to "<< program_size << std::endl;
        synthesizer.set_program_size(program_size);
        continue; // do another attempt to synthesize
      }
      else if(problem.alternative_constraints.size()>0 
              && !switched_to_alternative_constraints)
      {
        std::cout<<"switching to alternative constraints"<<std::endl;
        problem.constraints = problem.alternative_constraints;
        problem.synthesis_constraints.clear();
        switched_to_alternative_constraints=true;
        continue;
      }
      else
      {
        std::cout<<"No solution found"<<std::endl;
        return decision_proceduret::resultt::D_UNSATISFIABLE;
      }

      return ogist::resultt::D_ERROR;
    }

    std::cout<<"VERIFY iteration "<< iteration<<std::endl;
    solutiont solution = synthesizer.get_solution();
    std::size_t num_synth_constraints = problem.synthesis_constraints.size();
    switch(verify(problem, solution))
    {
    case verifyt::PASS:
      std::cout<<"Verification passed" <<std::endl;
      display_solution(solution, problem.synth_fun_helpers);
      return decision_proceduret::resultt::D_SATISFIABLE;
    case verifyt::FAIL:
      std::cout<<"Fail: got "<<problem.synthesis_constraints.size()-num_synth_constraints <<" new constraints"<<std::endl;
      synthesizer.increment_synthesis_constraints();
      break;
    }

  }
  return decision_proceduret::resultt::D_UNSATISFIABLE;
} 




