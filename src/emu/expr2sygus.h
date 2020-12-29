#ifndef EMU_EXPR2SYGUS
#define EMU_EXPR2SYGUS

#include <util/expr.h>
#include <iostream>

std::string expr2sygus(const exprt &expr);
std::string expr2sygus(const exprt &expr, bool use_integers);

#endif /* EMU_EXPR2SYGUS*/