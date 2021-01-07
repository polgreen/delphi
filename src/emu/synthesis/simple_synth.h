#ifndef EMU_SIMPLE_SYNTH_H_
#define EMU_SIMPLE_SYNTH_H_

#include "synthesizer.h"
#include "synth_encoding.h"
#include <solvers/decision_procedure.h>
#include <util/namespace.h>
#include <util/message.h>

class simple_syntht : public synthesizert
{

public:
  simple_syntht(namespacet &_namespace, 
                message_handlert &_ms) :
                ns(_namespace),
                message_handler(_ms),
                program_size(0){};

  resultt operator()(const problemt &) override;

  exprt model(exprt) const override;

  void add_ce(const counterexamplet &cex) override;
  solutiont get_solution() const override;
  void set_program_size(std::size_t size) override;

protected:
  resultt operator()(const problemt &, decision_proceduret &solver);

  std::vector<counterexamplet> counterexamples;

  void add_counterexample(
  const counterexamplet &ce,
  synth_encodingt &synth_encoding,
  decision_proceduret &solver);

  // snthesis encoding
  synth_encodingt synth_encoding;
  void add_problem(synth_encodingt &encoding, decision_proceduret &solver, const problemt &problem);
  solutiont last_solution;

  /// Namespace passed on to decision procedure.
  namespacet ns;
  std::string logic = "LIA";
  message_handlert &message_handler;
  std::size_t program_size;
};

#endif /* EMU_SIMPLE_SYNTH_H_ */
