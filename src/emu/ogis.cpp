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

// problem is dynamic
ogist::resultt ogist::doit(namespacet &ns)
{
  // the actual synthesis loop

  while(true)
  {
    // synthesiser synthesise solution to problem so far

    switch(synthesizer(problem))
    {
    case synthesizert::CANDIDATE:
      break;

    case synthesizert::NO_SOLUTION:
      return decision_proceduret::resultt::D_UNSATISFIABLE;
    }

    // verifier: Check correctness. If correct return solution,
    // otherwise 'verify' adds constraints to the problem
    auto model = [this](exprt src) -> exprt { return synthesizer.model(src); };

    switch(verify(problem, model))
    {
    case verifyt::PASS:
      return decision_proceduret::resultt::D_SATISFIABLE;

    case verifyt::FAIL:
      break;
    }

    // If not correct, are there other oracles to call? If yes, call some
    // and add oracle constraints/assumptions to problem
  }
} 




