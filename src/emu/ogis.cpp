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
  problemt &__problem) :
  synthesizer(__synthesizer),
  verify(__verify),
  problem(__problem)
{
  // get base problem
  // find correctness requirement, add to verifier
  // add orcle assumptions and constraints to verifier
  // set oracle selection strategy in verifier
  // set synthesis strategy
}

// problem is dynamic
ogist::resultt ogist::doit()
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
      return ogist::resultt::D_UNSATISFIABLE;
    }

    // verifier: Check correctness. If correct return solution,
    // otherwise 'verify' adds constraints to the problem
    auto model = [this](exprt src) -> exprt { return synthesizer.model(src); };

    switch(verify(problem, model))
    {
    case verifyt::PASS:
      return ogist::resultt::D_SATISFIABLE;

    case verifyt::FAIL:
      break;
    }

    // If not correct, are there other oracles to call? If yes, call some
    // and add oracle constraints/assumptions to problem
  }
} 

void ogist::set_to(const exprt &expr, bool value) { }

exprt ogist::handle(const exprt &expr)
{
  return expr;
}

exprt ogist::get(const exprt &expr) const
{
  return expr;
}

void ogist::print_assignment(std::ostream &out) const { }

std::size_t ogist::get_number_of_solver_calls() const
{
  return 0;
}

ogist::resultt ogist::dec_solve()
{
  return ogist::resultt::D_ERROR;
}

std::string ogist::decision_procedure_text() const
{
  return "ogis";
}
