#ifndef CPROVER_FASTSYNTH_ORACLE_SOLVER_2_H
#define CPROVER_FASTSYNTH_ORACLE_SOLVER_2_H

#include <solvers/decision_procedure.h>
#include <solvers/smt2/smt2_parser.h>

#include <util/mathematical_expr.h>
#include <util/message.h>

#include <delphi/oracle_constraint_gen.h>

#include <unordered_set>
#include "oracle_solver.h"

class negation_oracle_solvert : public oracle_solvert
{
public:
  negation_oracle_solvert(
    decision_proceduret &sub_solver,
    decision_proceduret &negation_sub_solver,
    message_handlert &);

  void set_to(const exprt &expr, bool value) override;
  exprt handle(const exprt &expr) override;



protected:
  resultt dec_solve() override;
  decision_proceduret &negation_sub_solver;
  void check_oracle(const function_application_exprt &, const applicationt &, bool use_negation_solver);
  void check_negation_solver_oracles();
  decision_proceduret::resultt get_model();
  bool try_positive_model;

};

#endif // CPROVER_FASTSYNTH_ORACLE_SOLVER_2_H
