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
  "(symbolic-bitblast)"                                                   \
  "(symbolic-synth)"                                                      \
  "(simplify) "                                                           \
  "(cvc4) "                                                               \
  "(constants) "                                                          \
  "(grammar) "                                                            \
  "(no-negation-solver) "                                                 \
  "(negation-solver) "                                                    \
  "(symo) "                                                               \
  "(smto)"                                                                \
  "(smt)"                                                                 \
  "(pbe)"                                                                 \
  "(fp)"                                                                  \
  "(dump-problem-as-smt)"                                                 \
  "(dump-problem)"                                                        \
  "(print-check-file):"                                                   \
  "(check-solution):"                                                     \
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
     "  Oracle SMTO subsolver:         default uses CVC4\n"
     " --bitblast                      use bitblasting solver as oracle solver subsolver\n"
     " --simplify                      enables simplifcation in bitblasting solver\n"
     " --negation-solver               enables solving algorithm that searches for negation of model\n\n"
     "  Synthesis solver               default uses CVC4\n"
     " --fp                            enables floating points of arbitrary size\n"
     " --pbe                           enables PBE mode in CVC4 (not recommended unless using a grammar)\n"
     " --grammar                       adds a default grammar to all synthesis functions (overrides any existing grammar)\n"
     " --constants                     collects constants from benchmark and adds to grammar\n"
     " --symbolic-synth                use symbolic encoding for synthesis (does not support grammars)\n"
     " --symbolic-bitblast             use bitblaster with symbolic encoding\n\n\n"
     " --symo                          interactive mode, input is in SyMO format\n"
     " --smto                          interactive mode, input is in SMTO format\n\n"
     " --verbosity N                   increase verbosity (10 gives maximum verbosity)\n\n"
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
    {
      return smt2_frontend(cmdline, std::cin);
    }
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
    {
      if(cmdline.isset("dump-problem")|| cmdline.isset("dump-problem-as-smt") || cmdline.isset("print-check-file"))
        std::cerr << "Cannot dump or print check file for SMT problem\n";
        return 1;

      return smt2_frontend(cmdline);
    }
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
