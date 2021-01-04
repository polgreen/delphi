#ifndef EMU_ORACLE_INTERFACE_H_
#define EMU_ORACLE_INTERFACE_H_

#include "verify.h"

class oracle_interfacet:public verifyt
{
  protected:
  // initialisation

  // call oracles
  void call_oracle_constraint(const problemt::oracle_constraint_gent &oracle, const std::function<exprt(exprt)> &model);
  void call_oracle_assumption(const problemt::oracle_constraint_gent &oracle, const std::function<exprt(exprt)> &model);
  void call_correctness_oracles(problemt &problem, const std::function<exprt(exprt)> &model);
  
  /// Namespace passed on to decision procedure.

  // snthesis encoding

 public: 
  resultt operator()( problemt &problem,
    const std::function<exprt(exprt)> &model) override;


  /// program size

};

#endif /* EMU_ORACLE_INTERFACE_H_ */

