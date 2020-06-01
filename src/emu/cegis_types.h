#ifndef EMU_CEGIS_TYPES_H_
#define EMU_CEGIS_TYPES_H_

#include <set>
#include <map>

class problemt
{
public:
  std::set<exprt> free_variables;
  exprt::operandst side_conditions, constraints;
};




#endif /*EMU_CEGIS_TYPES_H_*/