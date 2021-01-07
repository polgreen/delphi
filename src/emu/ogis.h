#ifndef EMU_OGIS_H_
#define EMU_OGIS_H_

#include "synthesis/synthesizer.h"
#include <solvers/decision_procedure.h>
#include "problem.h"
#include "verification/verify.h"
#include <util/namespace.h>

class ogist
{
public:
  ogist(
    synthesizert &,
    verifyt &,
    problemt &,
    namespacet &);
 
  using resultt = decision_proceduret::resultt;

  resultt doit();


protected:
  synthesizert &synthesizer;
  verifyt &verify;
  problemt &problem;
  namespacet ns;
  solutiont solution;
}; 

#endif /*EMU_OGIS_H_*/
