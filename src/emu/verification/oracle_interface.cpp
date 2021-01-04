#include "oracle_interface.h"


void oracle_interfacet::call_oracle_constraint(const problemt::oracle_constraint_gent &oracle,const std::function<exprt(exprt)> &model)
{

}

void oracle_interfacet::call_oracle_assumption(const problemt::oracle_constraint_gent &oracle,const std::function<exprt(exprt)> &model)
{

}


void oracle_interfacet::call_correctness_oracles(problemt & problem,const std::function<exprt(exprt)> &model)
{
  // get correctness oracles in problem
  // call correctness oracles
  // or call smt solver
  // update constraints
}


oracle_interfacet::resultt oracle_interfacet::operator()( problemt &problem,
  const std::function<exprt(exprt)> &model)
  {
    // do something with the model? 
    
    // call additional oracles
    call_correctness_oracles(problem, model);

    // call additional oracles
    for(const auto & oracle: problem.oracle_constraint_gens)
      call_oracle_constraint(oracle, model);

    for(const auto & oracle: problem.oracle_assumption_gens)
      call_oracle_assumption(oracle, model);


    return oracle_interfacet::resultt::FAIL;
  }