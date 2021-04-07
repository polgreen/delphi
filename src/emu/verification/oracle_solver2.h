#ifndef CPROVER_FASTSYNTH_ORACLE_SOLVER_2_H
#define CPROVER_FASTSYNTH_ORACLE_SOLVER_2_H

#include <solvers/decision_procedure.h>
#include <solvers/smt2/smt2_parser.h>

#include <util/mathematical_expr.h>
#include <util/message.h>

#include <emu/oracle_constraint_gen.h>

#include <unordered_set>
#include "oracle_solver.h"

class negation_oracle_solvert : public oracle_solvert
{
public:
  negation_oracle_solvert(
    decision_proceduret &negation_sub_solver,
    decision_proceduret &sub_solver,
    message_handlert &);

  void set_to(const exprt &expr, bool value) override;


protected:
  resultt dec_solve() override;
  decision_proceduret &negation_sub_solver;
  check_resultt check_oracle(const function_application_exprt &, const applicationt &);


};

#endif // CPROVER_FASTSYNTH_ORACLE_SOLVER_2_H
