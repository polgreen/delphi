#ifndef CPROVER_FASTSYNTH_LITERALS_H_
#define CPROVER_FASTSYNTH_LITERALS_H_

#include <util/std_expr.h>

#include <set>

/// Collects all constant literals explicitly used in the problem description.
/// \param problem Problem in which to search for literals.
/// \return All constant literals located in the given problem.
std::set<constant_exprt> find_literals(const class problemt &problem);

#endif /* CPROVER_FASTSYNTH_LITERALS_H_ */