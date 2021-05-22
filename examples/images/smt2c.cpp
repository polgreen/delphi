#include "define_fun_parser.h"

#include <util/cmdline.h>
#include <util/mathematical_types.h>

#include <iostream>

#include <ansi-c/expr2c.h>

#include <util/config.h>
#include <util/exception_utils.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>
#include <util/namespace.h>

#define CBMC_ORACLE_OPTIONS ""

void help(std::ostream &out)
{
  out << "no help yet\n";
}

irep_idt tweak_identifier(irep_idt src)
{
  std::string new_identifier = id2string(src);

  for(auto &ch : new_identifier)
    if(ch == '#')
      ch = '$';

  return new_identifier;
}

exprt tweak_symbols(exprt src)
{
  exprt dest = src;

  dest.visit_pre([](exprt &node) {
    if(node.id() == ID_symbol)
    {
      auto &symbol = to_symbol_expr(node);
      symbol.set_identifier(tweak_identifier(symbol.get_identifier()));
    }
  });

  return dest;
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
      auto parameter_name = tweak_identifier(define_fun.parameters[index]);
      out << parameter_name;
    }
  }
  else
    out << "void";

  out << ')';

  // body
  exprt body_tweaked = tweak_symbols(define_fun.body);

  out << " {\n";
  out << "  return " << expr2c(body_tweaked, ns, configuration) << ";\n";
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
    // configure, to get the architecture-specifics of the standard C types
    config.set(cmdline);

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
