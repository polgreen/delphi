#include <util/expr.h>
#include <util/std_expr.h>
#include <iosfwd>
#include <map>

struct define_fun_resultt
{
  irep_idt id;
  typet type;
  std::vector<irep_idt> parameters;
  exprt body;
};

define_fun_resultt define_fun_parser(std::istream &);

std::map<irep_idt, exprt> model_parser(std::istream &);