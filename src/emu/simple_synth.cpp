#include "simple_synth.h"

  simple_syntht::resultt simple_syntht::operator()(const problemt &)
  {
      return simple_syntht::resultt::NO_SOLUTION;
  }

  exprt simple_syntht::model(exprt) const
  {
      exprt result;
      return result;
  }