#include "simple_synth.h"

simple_syntht::resultt simple_syntht::operator()(const problemt &)
{
      // add the problem to the solver (assumptions => constraints)
      // with synthesis encoding in place of synthesis function
      

      // solve

  return simple_syntht::resultt::NO_SOLUTION;
}

exprt simple_syntht::model(exprt) const
{
  return nil_exprt();
}