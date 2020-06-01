#ifndef EMU_CEGIS_H_
#define EMU_CEGIS_H_

#include "synthesizer.h"
#include <solvers/decision_procedure.h>
#include "cegis_types.h"

class cegist: public decision_proceduret
{
public:
  cegist(
    synthesizert &synthesizer,
    decision_proceduret &verifier,
    const problemt &problem);
 
  resultt doit(synthesizert &synthesizer,
    decision_proceduret &verifier, const problemt &problem);
}; 

#endif /*EMU_CEGIS_H_*/