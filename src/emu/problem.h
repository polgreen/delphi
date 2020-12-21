#ifndef EMU_PROBLEM_H
#define EMU_PROBLEM_H

#include <util/expr.h>

class problemt
{
public:
  explicit problemt(exprt __formula) : formula(std::move(__formula))
  {
  }

  // This is expected not to change
  const exprt formula;

  // We only ever add assumptions and constraints, we never remove them.
  std::vector<exprt> assumptions, constraints;
};

#endif /*EMU_PROBLEM_H*/
