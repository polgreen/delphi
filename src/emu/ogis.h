#ifndef EMU_OGIS_H_
#define EMU_OGIS_H_

#include "synthesis/synthesizer.h"
#include <solvers/decision_procedure.h>
#include "problem.h"
#include "verification/verify.h"

class ogist
{
public:
  ogist(
    synthesizert &,
    verifyt &,
    problemt &);
 
  decision_proceduret::resultt doit();


protected:
  synthesizert &synthesizer;
  verifyt &verify;
  problemt &problem;
}; 

#endif /*EMU_OGIS_H_*/
