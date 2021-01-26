#include <util/cmdline.h>

#include <iostream>

#include "../../src/emu/verification/oracle_response_parser.h"

#include <ansi-c/expr2c.h>

#include <util/exception_utils.h>
#include <util/symbol_table.h>
#include <util/namespace.h>

#define CBMC_ORACLE_OPTIONS ""

void help(std::ostream &out)
{
  out << "no help yet\n";
}

int main(int argc, const char *argv[])
{
  cmdlinet cmdline;
  if(cmdline.parse(argc, argv, CBMC_ORACLE_OPTIONS))
  {
    std::cerr << "Usage error\n";
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
    // parse the arguments and output as #define
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);
    expr2c_configurationt configuration = expr2c_configurationt::default_configuration;

    std::size_t count = 0;
    for(const auto &arg : cmdline.args)
    {
      std::istringstream arg_stream(arg);
      auto arg_parsed = oracle_response_parser(arg_stream);
      exprt expr = arg_parsed;
      std::cout << "#define E" << (++count) << " " << expr2c(expr, ns, configuration) << "\n";
    }
  }
  catch(const cprover_exception_baset &error)
  {
    std::cerr << "Error: " << error.what() << '\n';
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
