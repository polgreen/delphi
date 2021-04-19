#ifndef _EMU_SYGUS_PARSER_H_
#define _EMU_SYGUS_PARSER_H_

#include <set>
#include <solvers/smt2/smt2_parser.h>

#include <util/mathematical_expr.h>
#include <util/mathematical_types.h>

#include "oracle_constraint_gen.h"

class sygus_parsert: public smt2_parsert
{
public:
  explicit sygus_parsert(std::istream &_in):
    smt2_parsert(_in)
  {
    setup_commands();
  }

  using smt2_errort = smt2_tokenizert::smt2_errort;

  enum invariant_variablet { PRIMED, UNPRIMED };
  enum invariant_constraint_functiont { PRE, INV, TRANS, POST };

  exprt::operandst constraints;
  exprt::operandst assumptions;
  std::vector<oracle_constraint_gent> oracle_assumption_gens;
  std::vector<oracle_constraint_gent> oracle_constraint_gens;
  std::string logic, action;

  std::set<symbol_exprt> synth_fun_set;
  std::set<symbol_exprt> variable_set;

  signature_with_parameter_idst inv_function_signature();
  void expand_function_applications(exprt &);
  void generate_invariant_constraints();

  oracle_constraint_gent oracle_signature();

  function_application_exprt apply_function_to_variables(
    invariant_constraint_functiont id,
    invariant_variablet variable_use);
  
  void replace_higher_order_logic();

protected:
  // commands
  void setup_commands();

  // grammars
  void NTDef_seq();
  void GTerm_seq();
  void NTDef();
  void GTerm();
  void replace_higher_order_logic(exprt &expr);

};

#endif /*_EMU_SYGUS_PARSER_H_*/