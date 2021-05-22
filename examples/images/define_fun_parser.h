#include <util/expr.h>

#include <iosfwd>

struct define_fun_resultt
{
  irep_idt id;
  typet type;
  std::vector<irep_idt> parameters;
  exprt body;
};

define_fun_resultt define_fun_parser(std::istream &);
