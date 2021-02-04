/*******************************************************************\
 *       \|/
       -=(')
         ;;
        //
       //
      : '.---.__
      |  --_-_)__)
      `.____,'
         \  \
       ___\  \
      (        \     EMU
               /

 Module: EMU Main Module
 Author: Elizabeth Polgreen, epolgreen@gmail.com. 
         Daniel Kroening, kroening@kroening.com
\*******************************************************************/

#include <util/cmdline.h>
#include <util/suffix.h>
#include "sygus_frontend.h"
#include "smt2_frontend.h"

#include <iostream>

#define EMU_OPTIONS                                                      \
  "(verbosity): "                                                         \
  "(smt) "                                                                \
  "(bitblast) "                                                           \
  "(simplify) "                                                           \
  "(cvc4) "                                                           \
  "(constants) "                                                           \
  "(grammar) "                                                           \
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
     "* *                       EMU-Synt                          * *\n "
     "* *         Elizabeth's Minimalist Universal Synthesize     * *\n ";
  out  <<
     "* *                                                          * *\n"
     "\n"
     "Usage:                       Purpose:\n"
     "\n"
     " emu [-?] [-h] [--help]       show help\n"
     " emu file.sl ...              source file names\n"
     "\n"
     "\n"
     "Command line options\n"
     " --smt                          use Z3 solver as oracle solver subsolver (default) \n"
     " --bitblast                     use bitblasting solver as oracle solver subsolver\n"
     " --cvc4                         use cvc4 for synthesis\n"
     "\n"
     "\n";
    // clang-format on
}

int main(int argc, const char *argv[])
{
  cmdlinet cmdline;
  if(cmdline.parse(argc, argv, EMU_OPTIONS))
  {
    std::cerr << "Usage error\n";
    help(std::cerr);
    return 1;
  }

  if(cmdline.args.size() != 1)
  {
    std::cerr << "Usage error, file must be given\n";
    help(std::cerr);
    return 1;
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
