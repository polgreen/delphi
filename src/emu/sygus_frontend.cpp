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

#include <ansi-c/ansi_c_language.h>

#include <solvers/smt2/smt2_conv.h>

#include <langapi/language_util.h>
#include <langapi/mode.h>

#include <fstream>



int sygus_frontend(const cmdlinet &cmdline)
{
  assert(cmdline.args.size()==1);

  register_language(new_ansi_c_language);
  config.ansi_c.set_32();

  console_message_handlert message_handler;
  messaget message(message_handler);

  // this is our default verbosity
  unsigned int v=messaget::M_STATISTICS;

  if(cmdline.isset("verbosity"))
  {
    v=std::stol(
        cmdline.get_value("verbosity"));;
    if(v>10)
      v=10;
  }

  message_handler.set_verbosity(v);

  std::ifstream in(cmdline.args.front());

  if(!in)
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
  catch(const sygus_parsert::smt2_errort &e)
  {
    message.error() << e.get_line_no() << ": "
                    << e.what() << messaget::eom;
    return 20;
  }

  // build problem
  problemt problem;
  for(const auto &c: parser.constraints)
    problem.constraints.push_back(c);
  for(const auto &c: parser.assumptions)
    problem.assumptions.push_back(c);
  for(const auto &c: parser.oracle_constraint_gens)
    problem.oracle_constraint_gens.push_back(c);   
  for(const auto &c: parser.oracle_assumption_gens)
    problem.oracle_assumption_gens.push_back(c);  

  // get synthesiser
  simple_syntht synthesizer;
  oracle_interfacet verifier;

  ogist ogis(synthesizer, verifier, problem);
  ogis.doit();  

 
  return 0;
}


