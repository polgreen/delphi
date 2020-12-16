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

#include <iostream>

#define EMU_OPTIONS                                                      \
  "(verbosity): "                                                        \


/// File ending of Siemens STL source files. Used to determine the language
/// frontend that shall be used.
#define STATEMENT_LIST_FILE_ENDING ".awl"

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
     " emu [-?] [-h] [--help]      show help\n"
     " emu file.sl ...              source file names\n"
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
    return sygus_frontend(cmdline);
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