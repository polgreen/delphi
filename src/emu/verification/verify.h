#ifndef EMU_VERIFY_H
#define EMU_VERIFY_H

#include <functional>

#include "../problem.h"

class verifyt
{
public:
  // Verify a candidate solution, given in the form of a model for
  // the problem.  Returns 'PASS' if the model is a solution,
  // and adds constraints or assumptions to the problem otherwise.
  using resultt = enum { PASS, FAIL };
  virtual resultt operator()(
    problemt &problem,
    const std::function<exprt(exprt)> &model) = 0;
};

#endif /*EMU_VERIFY_H*/
