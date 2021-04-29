/*******************************************************************\
 Module: Delphi Main Module
 Author: Elizabeth Polgreen, epolgreen@gmail.com. 
\*******************************************************************/

#include <util/cmdline.h>
#include <util/suffix.h>
#include "sygus_frontend.h"
#include "smt2_frontend.h"

#include <iostream>

#define DELPHI_OPTIONS                                                    \
  "(verbosity): "                                                         \
  "(smt) "                                                                \
  "(bitblast) "                                                           \
  "(simplify) "                                                           \
  "(cvc4) "                                                               \
  "(constants) "                                                          \
  "(grammar) "                                                            \
  "(no-negation-solver) "                                                 \
  "(negation-solver) "                                                    \
  "(symo) "                                                               \
  "(smto)"                                                                \
  "(smt)"                                                                 \
/// File ending of SMT2 files. Used to determine the language frontend that
/// shall be used.
#define SMT2_FILE_ENDING ".smt2"

/// File ending of Sygus files. Used to determine the language frontend that
/// shall be used.
#define SYGUS_FILE_ENDING ".sl"

void help(std::ostream &out)
{
  // clang-format off
  out <<
     "\n"
     "* *                          DELPHI                            * *\n"
     "* *        Synthesis and Satisfiability modulo oracles         * *\n"
     "* *                                                            * *\n"
     "* * Delphi supports SyMO and SMTO for bitvectors and integers  * *\n"
     "* *                                                            * *\n";
  out  <<
     "* *                                                            * *\n"
     "\n"
     "Usage:                           Purpose:\n"
     "\n"
     " delphi [-?] [-h] [--help]       show help\n"
     " delphi file.sl ...              source file names\n"
     "\n"
     "\n"
     "Command line options\n"
     " --smt                           use Z3 solver as oracle solver subsolver (default) \n"
     " --bitblast                      use bitblasting solver as oracle solver subsolver\n"
     " --cvc4                          use cvc4 for synthesis\n"
     " --symo                          input is in SyMO format\n"
     " --smto                          input is in SMTO format\n"
     "\n"
     "\n";
    // clang-format on
}

int main(int argc, const char *argv[])
{
  cmdlinet cmdline;

  if(cmdline.parse(argc, argv, DELPHI_OPTIONS))
  {
    std::cerr << "Usage error\n";
    help(std::cerr);
    return 1;
  }

  if(cmdline.args.size() != 1)
  {
    if(cmdline.isset("symo"))
      return sygus_frontend(cmdline, std::cin);
    else if(cmdline.isset("smto"))
      return smt2_frontend(cmdline, std::cin);
    else
    {
     help(std::cout);
     return 1;
    }
  }

  if(cmdline.isset("help") || cmdline.isset("h") || cmdline.isset("?"))
  {
    help(std::cout);
    return 1;
  }

  try
  {
    if(has_suffix(cmdline.args.back(), SYGUS_FILE_ENDING))
      return sygus_frontend(cmdline);
    else if(has_suffix(cmdline.args.back(), SMT2_FILE_ENDING))
      return smt2_frontend(cmdline);
    else
    {
      std::cerr<<"Unknown file type \n";
    }
    

  }
  catch(const char *s)
  {
    std::cerr << "Error: " << s << '\n';
  }
  catch(const std::string &s)
  {
    std::cerr << "Error: " << s << '\n';
  }
}
