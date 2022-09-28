#ifndef EMU_PRINT_CHECK_SOLUTION_H
#define EMU_PRINT_CHECK_SOLUTION_H

#include "define_fun_parser.h"
#include "../verification/verify.h"
#include "../problem.h"


int check_solution( problemt &problem, 
                    const std::string sol_string, 
                    const namespacet &ns,
                    verifyt& verify);

#endif /*EMU_PRINT_CHECK_SOLUTION_H*/