#include <util/expr.h>

#include <iosfwd>
#include <map>

class symbol_exprt;

std::map<symbol_exprt, exprt> oracle_response_parser(std::istream &);

