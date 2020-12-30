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

ogist::ogist(synthesizert &synthesizer,
    verifyt &verifier,
    const problemt &problem)
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
      // the actual synthesis loop:
      // synthesiser synthesise solution to problem so far
      

      // verifier: Check correctness. If correct return solution

      // If not correct, are there other oracles to call? If yes, call some
      // and add oracle constraints/assumptions to problem

      // loop. 


      return ogist::resultt::D_ERROR;
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
