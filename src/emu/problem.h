#ifndef EMU_PROBLEM_H
#define EMU_PROBLEM_H

#include <util/expr.h>
#include "sygus_parser.h"

class problemt
{
public:
  // explicit problemt(exprt __formula) : formula(std::move(__formula))
  // {
  // }

  // // This is expected not to change
  // const exprt formula;

  // We only ever add assumptions and constraints, we never remove them.
  // assumptions and constraints come from the original spec, and are used for verification
  // Oracle assumption gen and constraint gen may add to the assumptions and constraints
  // Synthesis assumptions are only used by the synthesis phase, and never by the verification phase
  // synthesis assumptions contain the counterexamples obtained so far
  // std::vector<exprt> assumptions, constraints, synthesis_assumptions;
  std::vector<exprt> constraints, assumptions, synthesis_assumptions;
  std::vector<oracle_constraint_gent> oracle_assumption_gens, oracle_constraint_gens;
  // universally quantified variables
  std::vector<symbol_exprt> synthesis_variables;
};

class solutiont
{
  public:
  std::map<symbol_exprt, exprt> functions;
};

#endif /*EMU_PROBLEM_H*/
