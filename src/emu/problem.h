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

  using oracle_constraint_gent = sygus_parsert::oracle_constraint_gent;
  // We only ever add assumptions and constraints, we never remove them.
  std::vector<exprt> assumptions, constraints;
  std::vector<oracle_constraint_gent> oracle_assumption_gens, oracle_constraint_gens;
};

#endif /*EMU_PROBLEM_H*/
