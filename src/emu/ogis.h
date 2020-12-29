#ifndef EMU_OGIS_H_
#define EMU_OGIS_H_

#include "synthesizer.h"
#include <solvers/decision_procedure.h>
#include "problem.h"

class ogist: public decision_proceduret
{
public:
  ogist(
    synthesizert &synthesizer,
    decision_proceduret &verifier,
    const problemt &problem);
 
  resultt doit(synthesizert &synthesizer,
    decision_proceduret &verifier, const problemt &problem);
}; 

#endif /*EMU_OGIS_H_*/