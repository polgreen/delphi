#include "problem.h"

#include <util/expr_iterator.h>

/// Finds constant literals in an expression container.
/// \tparam containert Expression container type.
/// \param result Container into which to insert found literals.
/// \param expressions Expressions in which to search for constants.
template <class containert>
static void
find_literals(std::set<constant_exprt> &result, const containert &expressions)
{
  for(const exprt &e : expressions)
    for(auto it(e.unique_depth_cbegin()); it != e.unique_depth_cend(); ++it)
    {
      const constant_exprt *const c =
        expr_try_dynamic_cast<constant_exprt>(*it);
      if(!c)
        continue;
      const irep_idt &id = c->type().id();
      if(ID_signedbv == id || ID_unsignedbv == id || ID_integer == id)
        result.insert(*c);
    }
}

std::set<constant_exprt> find_literals(const problemt &problem)
{
  std::set<constant_exprt> result;
  find_literals(result, problem.constraints);
  find_literals(result, problem.free_variables);

  return result;
}