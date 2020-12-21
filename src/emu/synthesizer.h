#ifndef EMU_SYNTHESIZER_H
#define EMU_SYNTHESIZER_H

#include <functional>

#include <util/expr.h>

class synthesizert
{
public:
  // set up the problem, typcially a formula with quantifiers
  virtual void set_problem(const exprt &) = 0;

  // add a constraint to the problem
  virtual void add_constraint(const exprt &) = 0;

  // build a candidate solution, in the form of a model
  // that can be queried using model()
  using resultt = enum { CANDIDATE, NO_SOLUTION };
  virtual resultt operator()() = 0;
};

#endif /*EMU_SYNTHESIZER_H*/
