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
    synthesizert &,
    verifyt &,
    const problemt &);
 
  resultt doit();

  void set_to(const exprt &expr, bool value) override;
  exprt handle(const exprt &expr) override;
  exprt get(const exprt &expr) const override;
  void print_assignment(std::ostream &out) const override;
  std::size_t get_number_of_solver_calls() const override;
  resultt dec_solve() override;
  std::string decision_procedure_text() const override;
}; 

#endif /*EMU_OGIS_H_*/
