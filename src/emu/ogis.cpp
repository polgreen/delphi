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
    decision_proceduret &verifier,
    const problemt &problem)
    {
        // get base problem
        // find correctness requirement, add to verifier
        // add orcle assumptions and constraints to verifier
        // set oracle selection strategy in verifier
        // set synthesis strategy
    }

// problem is dynamic
ogist::resultt ogist::doit(synthesizert &synthesizer,
    decision_proceduret &verifier, const problemt &problem)
    {
      // the actual synthesis loop:
      // synthesiser synthesise solution to problem so far

      // verifier: Check correctness. If correct return solution

      // If not correct, are there other oracles to call? If yes, call some
      // and add oracle constraints/assumptions to problem

      // loop. 


      return ogist::resultt::D_ERROR;
    } 

