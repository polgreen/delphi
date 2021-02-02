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
  // Synthesis constraints are only used by the synthesis phase, and never by the verification phase

  // these are used for verification
  std::vector<exprt> constraints, assumptions;
  // these are used for synthesis
  std::set<exprt> synthesis_constraints;
  // these are the oracles that can generate assumptions and constraints
  std::vector<oracle_constraint_gent> oracle_assumption_gens, oracle_constraint_gens;
  // universally quantified variables
  std::set<exprt> free_variables;
  std::set <symbol_exprt> synthesis_functions;
  // functions with an external oracle implementation
  smt2_parsert::oracle_fun_mapt oracle_symbols;
  std::set<irep_idt> second_order_oracles;
};

class solutiont
{
  public:
  std::map<symbol_exprt, exprt> functions;
};

class counterexamplet
{
public:
  std::unordered_map<exprt, exprt, irep_hash> assignment;
  void clear() { assignment.clear(); }
};


#endif /*EMU_PROBLEM_H*/
