#ifndef EMU_CVC4_SYNTH_H_
#define EMU_CVC4_SYNTH_H_

#include "synthesizer.h"
#include <solvers/decision_procedure.h>
#include <util/namespace.h>
#include <util/message.h>

class cvc4_syntht : public synthesizert
{

public:
  cvc4_syntht(message_handlert &_ms, bool _magic_constants, bool _usePBE, bool _use_grammar, bool _FP) :
                magic_constants(_magic_constants),
                usePBE(_usePBE),
                use_grammar(_use_grammar),
                FP(_FP),
                number_synth_constraints(0u),
                synth_constraint_increment(2u),
                message_handler(_ms){};

  resultt operator()(const problemt &) override;

  exprt model(exprt) const override;

  // void add_ce(const counterexamplet &cex) override;
  solutiont get_solution() const override;
  void set_program_size(std::size_t size) override;
  void increment_synthesis_constraints() override;
  bool magic_constants;
  bool usePBE;
  bool use_grammar;
  bool FP;

protected:
  // number of synth constraints used so far
  std::size_t number_synth_constraints;
  // maximum number of synth constraints to add each iteration
  std::size_t synth_constraint_increment;
  std::string build_query(const problemt &problem);
  decision_proceduret::resultt read_result(std::istream &in, const problemt &p);
  decision_proceduret::resultt solve(const problemt &problem);
  solutiont last_solution;
  message_handlert &message_handler;
};

#endif /* EMU_CVC4_SYNTH_H_ */
