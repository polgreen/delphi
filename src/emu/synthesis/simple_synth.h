#ifndef EMU_SIMPLE_SYNTH_H_
#define EMU_SIMPLE_SYNTH_H_

#include "synthesizer.h"
#include "synth_encoding.h"
#include <solvers/decision_procedure.h>
#include <util/namespace.h>

class simple_syntht:public synthesizert
{
  protected:
  resultt operator()(const problemt &, decision_proceduret &solver);


  // snthesis encoding
  synth_encodingt synth_encoding;
  void add_problem(synth_encodingt &encoding, decision_proceduret &solver, const problemt &problem);
  std::vector<symbol_exprt> quantified_variables;
  solutiont last_solution;

  /// Namespace passed on to decision procedure.
  namespacet ns;
  std::string logic="LIA";

 public: 
  resultt operator()(const problemt &) override;

  exprt model(exprt) const override;

  /// program size

};

#endif /* EMU_SIMPLE_SYNTH_H_ */

