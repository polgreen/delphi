#include "sygus_frontend.h"
#include "synthesis/simple_synth.h"
#include "synthesis/cvc4_synth.h"
#include "verification/oracle_interface.h"
#include "ogis.h"
#include "sygus_parser.h"
#include "expr2sygus.h"
#include "problem.h"
#include "literals.h"

#include <util/cout_message.h>
#include <util/expr_initializer.h>
#include <util/namespace.h>
#include <util/symbol_table.h>
#include <util/config.h>
#include <util/std_expr.h>

#include <ansi-c/ansi_c_language.h>

#include <solvers/smt2/smt2_conv.h>

#include <langapi/language_util.h>
#include <langapi/mode.h>

#include <fstream>

problemt build_problem(sygus_parsert &parser)
{
  problemt problem;
  for(const auto &v : parser.variable_set)
    problem.free_variables.insert(v);

  // for(const auto &v: parser.full_let_variable_map)
  //   problem.free_variables.insert(symbol_exprt(v.first, v.second));

  problem.synthesis_functions = parser.synthesis_functions;
  for(auto &sf: problem.synthesis_functions)
    for(auto &rule_list: sf.second.grammar.production_rules)
      for(auto &e: rule_list.second)
      {
        parser.expand_function_applications(e);
      }
  

  problem.oracle_symbols = parser.oracle_symbols;
  for(const auto &symbol: parser.oracle_symbols)
  {
    for(const auto &d: symbol.second.type.domain())
      if(d.id()==ID_mathematical_function)
        problem.second_order_oracles.insert(symbol.first);
  }

  problem.constraints=parser.constraints;
  problem.assumptions=parser.assumptions;

  for (const auto &c : parser.oracle_constraint_gens)
    problem.oracle_constraint_gens.push_back(c);

  for (const auto &c : parser.oracle_assumption_gens)
    problem.oracle_assumption_gens.push_back(c);

  for(auto &c : problem.constraints)
    parser.expand_function_applications(c);

  for(auto &c : problem.assumptions)
    parser.expand_function_applications(c);

  problem.literals=find_literals(problem);
  
  for(auto &o : problem.oracle_constraint_gens)
    parser.expand_function_applications(o.constraint);

  for(auto &o : problem.oracle_assumption_gens)
    parser.expand_function_applications(o.constraint);

  return problem;
}

int sygus_frontend(const cmdlinet &cmdline)
{
  assert(cmdline.args.size() == 1);

  register_language(new_ansi_c_language);
  config.ansi_c.set_32();

  console_message_handlert message_handler;
  messaget message(message_handler);

  // this is our default verbosity
  unsigned int v = messaget::M_STATISTICS;

  if (cmdline.isset("verbosity"))
  {
    v = std::stol(
        cmdline.get_value("verbosity"));
    ;
    if (v > 10)
      v = 10;
  }

  message_handler.set_verbosity(v);

  std::ifstream in(cmdline.args.front());

  if (!in)
  {
    message.error() << "Failed to open input file" << messaget::eom;
    return 10;
  }

  // parse problem
  sygus_parsert parser(in);

  try
  {
    parser.parse();
    parser.replace_higher_order_logic();
  }
  catch (const sygus_parsert::smt2_errort &e)
  {
    message.error() << e.get_line_no() << ": "
                    << e.what() << messaget::eom;
    return 20;
  }

  // build problem
  problemt problem = build_problem(parser);

  // get synthesiser and verifier

  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  if(cmdline.isset("cvc4"))
  {
    cvc4_syntht synthesizer(message_handler, cmdline.isset("constants"), cmdline.isset("grammar"));  
    oracle_interfacet verifier(ns, message_handler, cmdline.isset("bitblast"));
    ogist ogis(synthesizer, verifier, problem, ns);
    ogis.doit();
  }
  else
  {
    simple_syntht synthesizer(ns, message_handler, cmdline.isset("bitblast"));
    oracle_interfacet verifier(ns, message_handler, cmdline.isset("bitblast"));
    ogist ogis(synthesizer, verifier, problem, ns);
    ogis.doit();
  }

  return 0;
}
