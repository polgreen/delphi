#include "sygus_frontend.h"
#include "synthesis/simple_synth.h"
#include "verification/oracle_interface.h"
#include "ogis.h"
#include "sygus_parser.h"
#include "expr2sygus.h"
#include "problem.h"

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

problemt build_problem(const sygus_parsert &parser)
{
  problemt problem;
  for (const auto &v : parser.variable_set)
    problem.synthesis_variables.push_back(v);
  if (parser.assumptions.size() > 1)
    problem.assumptions = and_exprt(parser.assumptions);
  else if (parser.assumptions.size() == 1)
    problem.assumptions = parser.assumptions[0];
  else
    problem.assumptions = true_exprt();

  if (parser.constraints.size() > 1)
    problem.constraints = and_exprt(parser.constraints);
  else if (problem.constraints.size() == 1)
    problem.constraints = parser.constraints[0];
  else
    problem.constraints = true_exprt();

  for (const auto &c : parser.oracle_constraint_gens)
    problem.oracle_constraint_gens.push_back(c);
  for (const auto &c : parser.oracle_assumption_gens)
    problem.oracle_assumption_gens.push_back(c);
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
  }
  catch (const sygus_parsert::smt2_errort &e)
  {
    message.error() << e.get_line_no() << ": "
                    << e.what() << messaget::eom;
    return 20;
  }

  // build problem
  problemt problem = build_problem(parser);

  // get synthesiser

  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  simple_syntht synthesizer(ns, message_handler);
  oracle_interfacet verifier;

  ogist ogis(synthesizer, verifier, problem, ns);
  ogis.doit();

  return 0;
}
