#ifndef EMU_EXPR2SYGUS
#define EMU_EXPR2SYGUS

#include <util/expr.h>
#include <util/std_expr.h>
#include <iostream>
#include "syntactic_template.h"


std::string clean_id(const irep_idt &id);
void clean_symbols(exprt &expr);
std::string type2sygus(const typet &type);
std::string expr2sygus(const exprt &expr);
std::string expr2sygus_fun_dec(const symbol_exprt &function);
std::string synth_fun_dec(const irep_idt &id, const synth_functiont &definition);
std::string synth_fun_dec(const symbol_exprt &function, std::string grammar);
std::string expr2sygus_fun_def(const symbol_exprt &function, const exprt&body);
std::string expr2sygus_var_dec(const symbol_exprt &symbol);
#endif /* EMU_EXPR2SYGUS*/