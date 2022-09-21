#ifndef EMU_PRINT_SMT_CHECK_H
#define EMU_PRINT_SMT_CHECK_H
#include "../problem.h"
#include <util/expr.h>

void print_smt_solution_check(const problemt &, const std::string &solution);
void print_sygus_problem(const problemt &);
void print_smt_problem(const problemt &);

#endif /*EMU_PRINT_SMT_CHECK_H*/