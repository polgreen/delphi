#ifndef EMU_OGIS_H_
#define EMU_OGIS_H_

#include "synthesis/synthesizer.h"
#include <solvers/decision_procedure.h>
#include "problem.h"
#include "verification/verify.h"

class ogist: public decision_proceduret
{
public:
  ogist(
    synthesizert &synthesizer,
    verifyt &verifier,
    const problemt &problem);
 
  resultt doit();

  void set_to(const exprt &expr, bool value);  
  exprt handle(const exprt &expr);
  exprt get(const exprt &expr) const;
  void print_assignment(std::ostream &out) const;
  std::size_t get_number_of_solver_calls() const;
  resultt dec_solve();
  std::string decision_procedure_text() const;
}; 

#endif /*EMU_OGIS_H_*/
