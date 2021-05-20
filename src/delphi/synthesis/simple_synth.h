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
                message_handlert &_ms,
                bool _bitblast) :
                number_synth_constraints(0u),
                synth_constraint_increment(2u),
                ns(_namespace),
                message_handler(_ms),
                program_size(0),
                bitblast(_bitblast){};

  resultt operator()(const problemt &) override;

  exprt model(exprt) const override;

  // void add_ce(const counterexamplet &cex) override;
  solutiont get_solution() const override;
  void set_program_size(std::size_t size) override;
  void increment_synthesis_constraints() override;

protected:
  resultt operator()(const problemt &, decision_proceduret &solver);
  // number of synth constraints used so far
  std::size_t number_synth_constraints;
  // maximum number of synth constraints to add each iteration
  std::size_t synth_constraint_increment;

  // snthesis encoding
  synth_encodingt synth_encoding;
  void add_problem(synth_encodingt &encoding, decision_proceduret &solver, const problemt &problem);
  solutiont last_solution;
  void replace_synth_fun_parameters(const problemt &problem, std::map <symbol_exprt, exprt> &solution_functions);
  /// Namespace passed on to decision procedure.
  namespacet ns;
  std::string logic = "LIA";
  message_handlert &message_handler;
  std::size_t program_size;
  bool bitblast;
};

#endif /* EMU_SIMPLE_SYNTH_H_ */
