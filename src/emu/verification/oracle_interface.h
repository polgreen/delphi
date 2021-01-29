#ifndef EMU_ORACLE_INTERFACE_H_
#define EMU_ORACLE_INTERFACE_H_

#include "verify.h"
#include "verify_encoding.h"
#include "oracle_solver.h"
#include <solvers/decision_procedure.h>
#include <util/namespace.h>
#include <util/message.h>

class oracle_interfacet : public verifyt
{
 public:
  oracle_interfacet(namespacet &_namespace, 
                message_handlert &_ms, bool _bitblast) :
                bitblast(_bitblast),
                ns(_namespace),
                log(_ms){};

  resultt operator()( problemt &problem,
    const solutiont &solution) override;


  resultt operator()(problemt &problem,
    const solutiont &solution,
    oracle_solvert &solver);
  
  counterexamplet counterexample;

  counterexamplet get_counterexample() override;


  protected:
  bool bitblast;

  namespacet ns;
  messaget log;
  /// Encoding for the verification decision procedure call.
  verify_encodingt verify_encoding;

  std::map<irep_idt, std::size_t> synthfun_to_constraint_map;
  std::map<irep_idt, std::size_t> synthfun_to_assume_map;

  void build_counterexample_constraint(oracle_solvert &solver, 
  const counterexamplet &counterexample, problemt &problem);

  bool replace_oracles(exprt &synthesis_constraint, const problemt &problem, oracle_solvert &solver);
  void call_second_order_oracles(oracle_solvert &solver, const solutiont &solution);
  exprt get_oracle_constraints(
    const counterexamplet &,
    const oracle_constraint_gent &);

  void call_oracles(problemt &problem, 
  const solutiont &solution, const counterexamplet &counterexample, oracle_solvert &solver);
  std::set<irep_idt> find_synth_funs (const exprt &expr, const problemt &problem);
  void add_assumptions_from_solver(const oracle_solvert &solver, problemt &problem);

  void add_problem(const problemt &problem, const solutiont &solution, oracle_solvert &solver );

};

#endif /* EMU_ORACLE_INTERFACE_H_ */

