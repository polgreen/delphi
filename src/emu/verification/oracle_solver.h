#ifndef CPROVER_FASTSYNTH_ORACLE_SOLVER_H
#define CPROVER_FASTSYNTH_ORACLE_SOLVER_H

#include <solvers/decision_procedure.h>
#include <solvers/smt2/smt2_parser.h>

#include <util/mathematical_expr.h>
#include <util/message.h>

#include <emu/oracle_constraint_gen.h>

#include <unordered_set>

class oracle_solvert : public decision_proceduret
{
public:
  using oracle_funt = smt2_parsert::oracle_funt;
  using oracle_fun_mapt = smt2_parsert::oracle_fun_mapt; 

  oracle_solvert(
    decision_proceduret &sub_solver,
    message_handlert &);

  const oracle_fun_mapt *oracle_fun_map = nullptr;  

  // overloads
  void set_to(const exprt &expr, bool value) override;
  exprt handle(const exprt &expr) override;
  exprt get(const exprt &expr) const override;
  void print_assignment(std::ostream &out) const override;
  std::string decision_procedure_text() const override;

  std::size_t get_number_of_solver_calls() const override
  {
    return number_of_solver_calls;
  }


protected:
  resultt dec_solve() override;

  decision_proceduret &sub_solver;
  messaget log;
  std::size_t number_of_solver_calls = 0;

  using check_resultt = enum { INCONSISTENT, CONSISTENT, ERROR };
  check_resultt check_oracles();
  check_resultt check_oracle(const function_application_exprt &);

  exprt parse(const std::string &) const;

  using applicationst = std::unordered_set<function_application_exprt, irep_hash>;
  applicationst applications;
};

#endif // CPROVER_FASTSYNTH_ORACLE_SOLVER_H
