#ifndef EMU_SIMPLE_VERIFY_H_
#define EMU_SIMPLE_VERIFY_H_

#include "verify.h"
#include "verify_encoding.h"
#include "oracle_solver.h"
#include <solvers/decision_procedure.h>
#include <util/namespace.h>
#include <util/message.h>


class simple_verifyt : public verifyt
{
 public:
  simple_verifyt(namespacet &_namespace, 
                message_handlert &_ms, bool _bitblast) :
                bitblast(_bitblast),
                ns(_namespace),
                log(_ms){};

  resultt operator()( problemt &problem,
    const solutiont &solution) override;


  resultt operator()(problemt &problem,
    const solutiont &solution,
    decision_proceduret &solver);
  
  counterexamplet counterexample;
  counterexamplet get_counterexample() override;

  protected:
  bool bitblast;
  namespacet ns;
  messaget log;
  /// Encoding for the verification decision procedure call.
  verify_encodingt verify_encoding;

  void replace_synth_fun_parameters(const problemt &problem, std::map <symbol_exprt, exprt> &solution_functions); 
  void add_problem(const problemt &problem, const solutiont &solution, decision_proceduret &solver );

};

#endif /* EMU_SIMPLE_VERIFY_H_ */

