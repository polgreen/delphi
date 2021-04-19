
#ifndef CPROVER_FASTSYNTH_VERIFY_ENCODING_H_
#define CPROVER_FASTSYNTH_VERIFY_ENCODING_H_

#include <set>

#include <util/mathematical_expr.h>
#include <util/mathematical_types.h>

#include <solvers/decision_procedure.h>

#include "../problem.h"


class verify_encodingt
{
public:

  exprt operator()(const exprt &) const;

    /// Candidate solution to verify.
  std::map<symbol_exprt, exprt> functions;

    /// Free input variables by which to test.
  std::set<exprt> free_variables;

  counterexamplet get_counterexample(
    const decision_proceduret &) const;

  static void check_function_bodies(const std::map<symbol_exprt, exprt>  &);  

  void clear();


private:
  // check that the function body uses symbols that
  // are consistent with the signature of the function
  static void check_function_body(
    const mathematical_function_typet &signature,
    const exprt &body);

  exprt instantiate(
    const exprt &expr,
    const function_application_exprt &e) const;
};

#endif /* CPROVER_FASTSYNTH_VERIFY_ENCODING_H_ */