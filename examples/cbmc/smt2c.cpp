#include "define_fun_parser.h"

#include <util/cmdline.h>
#include <util/mathematical_types.h>

#include <iostream>

#include <ansi-c/expr2c.h>

#include <util/exception_utils.h>
#include <util/symbol_table.h>
#include <util/namespace.h>

#define CBMC_ORACLE_OPTIONS ""

void help(std::ostream &out)
{
  out << "no help yet\n";
}

void output_function(const define_fun_resultt &define_fun, std::ostream &out)
{
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  expr2c_configurationt configuration = expr2c_configurationt::default_configuration;

  // return type
  if(define_fun.type.id() == ID_mathematical_function)
    out << type2c(to_mathematical_function_type(define_fun.type).codomain(), ns, configuration);
  else
    out << type2c(define_fun.type, ns, configuration);

  out << ' ';

  // name of function
  out << define_fun.id;

  // parameters, if any, or void
  out << '(';

  if(define_fun.type.id() == ID_mathematical_function)
  {
    auto &function_type = to_mathematical_function_type(define_fun.type);
    for(std::size_t index = 0; index < function_type.domain().size(); index++)
    {
      if(index != 0)
        out << ", ";
      out << type2c(function_type.domain()[index], ns, configuration);
      out << ' ';
      out << define_fun.parameters[index];
    }
  }
  else
    out << "void";

  out << ')';

  // body
  out << " {\n";
  out << "  return " << expr2c(define_fun.body, ns, configuration) << ";\n";
  out << "}\n\n";
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
    for(const auto &arg : cmdline.args)
    {
      std::istringstream arg_stream(arg);
      auto arg_parsed = define_fun_parser(arg_stream);
      output_function(arg_parsed, std::cout);
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
