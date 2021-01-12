#ifndef EMU_ORACLE_INTERFACE_H_
#define EMU_ORACLE_INTERFACE_H_

#include "verify.h"
#include "verify_encoding.h"
#include <solvers/decision_procedure.h>
#include <util/namespace.h>
#include <util/message.h>

class oracle_interfacet : public verifyt
{
 public:
  oracle_interfacet(namespacet &_namespace, 
                message_handlert &_ms) :
                ns(_namespace),
                message_handler(_ms){};

  resultt operator()( problemt &problem,
    const solutiont &solution) override;


  resultt operator()(problemt &problem,
    const solutiont &solution,
    decision_proceduret &solver);
  
  counterexamplet counterexample;

  counterexamplet get_counterexample() override;


  protected:

  namespacet ns;
  message_handlert &message_handler;
  /// Encoding for the verification decision procedure call.
  verify_encodingt verify_encoding;

  std::map<irep_idt, std::size_t> synthfun_to_oracle_map;
  

  void call_oracles(problemt &problem);
  std::set<irep_idt> find_synth_funs (const exprt &expr, const problemt &problem);

  void add_problem(const problemt &problem, const solutiont &solution, decision_proceduret &solver );

};

#endif /* EMU_ORACLE_INTERFACE_H_ */

