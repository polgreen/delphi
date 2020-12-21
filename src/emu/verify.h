#ifndef EMU_VERIFY_H
#define EMU_VERIFY_H

#include <functional>

#include <util/expr.h>

class verifyt
{
public:
  // set up the problem, typically a formula with quantifiers
  virtual void set_problem(const exprt &) = 0;

  // Verify a candidate solution, given in the form of a model for
  // the problem.  Returns 'true' if the model is a solution,
  // and a constraint on the solution otherwise.
  virtual exprt operator()(const std::function<exprt(exprt)> &model) = 0;
};

#endif /*EMU_VERIFY_H*/
