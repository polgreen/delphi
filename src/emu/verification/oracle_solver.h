#ifndef CPROVER_FASTSYNTH_ORACLE_SOLVER_H
#define CPROVER_FASTSYNTH_ORACLE_SOLVER_H

#include <solvers/decision_procedure.h>

#include <util/message.h>

#include <emu/oracle_constraint_gen.h>

class oracle_solvert : public decision_proceduret
{
public:
  oracle_solvert(
    decision_proceduret &sub_solver,
    const std::vector<oracle_constraint_gent> &,
    message_handlert &);

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
  const std::vector<oracle_constraint_gent> &oracles;
  messaget log;
  std::size_t number_of_solver_calls = 0;

  using check_resultt = enum { INCONSISTENT, CONSISTENT, ERROR };
  check_resultt check_oracles();
  check_resultt check_oracle(std::size_t);

  void setup_oracle_equalities();
  exprt parse(const std::string &) const;
};

#endif // CPROVER_FASTSYNTH_ORACLE_SOLVER_H
