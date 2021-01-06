#ifndef EMU_SYNTHESIZER_H
#define EMU_SYNTHESIZER_H

#include <functional>

#include "../problem.h"

class synthesizert
{
public:
  // build a candidate solution, in the form of a model
  // that can be queried using model()
  using resultt = enum { CANDIDATE, NO_SOLUTION };
  virtual resultt operator()(const problemt &) = 0;

  virtual exprt model(exprt) const = 0;

  virtual void add_ce(const counterexamplet &)=0;
};

#endif /*EMU_SYNTHESIZER_H*/
