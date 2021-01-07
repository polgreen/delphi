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
         Daniel Kroening, kroening@kroening.com
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
  synthesizer(__synthesizer),
  verify(__verify),
  problem(__problem),
  ns(_ns)
{
  // get base problem
  // find correctness requirement, add to verifier
  // add orcle assumptions and constraints to verifier
  // set oracle selection strategy in verifier
  // set synthesis strategy
}
#include <iostream>
// problem is dynamic
ogist::resultt ogist::doit()
{
  std::cout<<"Start OGIS"<<std::endl;
  // the actual synthesis loop
  std::size_t program_size=1;

  while(true)
  {
    synthesizer.set_program_size(program_size);
    // synthesiser synthesise solution to problem so far

    switch(synthesizer(problem))
    {
    case synthesizert::CANDIDATE:
        std::cout<<"Got solution ";
        output_expressions(synthesizer.get_solution().functions, ns, std::cout);
        // got solution
        // check if solution is the same each time?
      break;
    case synthesizert::NO_SOLUTION:
      std::cout<<"No solution" <<std::endl;
      if(program_size<10)
      {
        program_size+=1;
        continue; // do another attempt to synthesize
      }
      return ogist::resultt::D_ERROR;
    }

    switch(verify(problem, synthesizer.get_solution()))
    {
    case verifyt::PASS:
      std::cout<<"Verification passed" <<std::endl;
      return decision_proceduret::resultt::D_SATISFIABLE;
    case verifyt::FAIL:
     std::cout<<"Verification Failed" <<std::endl;
      synthesizer.add_ce(verify.get_counterexample());
      break;
    }

    // If not correct, are there other oracles to call? If yes, call some
    // and add oracle constraints/assumptions to proble
  }
  return decision_proceduret::resultt::D_UNSATISFIABLE;
} 




