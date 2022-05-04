#ifndef _EMU_SYGUS_PARSER_H_
#define _EMU_SYGUS_PARSER_H_

#include <set>
#include <solvers/smt2/smt2_parser.h>

#include <util/mathematical_expr.h>
#include <util/mathematical_types.h>

#include "oracle_constraint_gen.h"

#include "syntactic_template.h"

class sygus_parsert: public smt2_parsert
{
public:
  explicit sygus_parsert(std::istream &_in):
    smt2_parsert(_in)
  {
    setup_commands();
  }

  void parse_model();

  using smt2_errort = smt2_tokenizert::smt2_errort;

  enum invariant_variablet { PRIMED, UNPRIMED };

  exprt::operandst constraints, alternative_constraints;
  exprt::operandst assumptions;
  std::vector<oracle_constraint_gent> oracle_assumption_gens;
  std::vector<oracle_constraint_gent> oracle_constraint_gens;
  std::string logic, action;

  // std::set<symbol_exprt> synth_fun_set;
  std::map<irep_idt, synth_functiont> synthesis_functions;
  std::set<symbol_exprt> variable_set;

  signature_with_parameter_idst inv_function_signature();
  void expand_function_applications(exprt &);
  void generate_invariant_constraints(const irep_idt &inv, const irep_idt &pre, const irep_idt &trans, const irep_idt &post);

  oracle_constraint_gent oracle_signature();

  function_application_exprt apply_function_to_variables(
    irep_idt id,
    invariant_variablet variable_use);
  
  std::vector<exprt> synth_fun_helpers;
  void replace_higher_order_logic();

protected:
  // commands
  void setup_commands();

  // grammars
  syntactic_templatet NTDef_seq();
  std::vector<exprt> GTerm_seq(const symbol_exprt &nonterminal);
  symbol_exprt NTDef();
  void replace_higher_order_logic(exprt &expr);

};

#endif /*_EMU_SYGUS_PARSER_H_*/