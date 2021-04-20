#ifndef _EMU_SYNTACTIC_TEMPLATE_H_
#define _EMU_SYNTACTIC_TEMPLATE_H_

#include <util/expr.h>
#include <map>
#include <solvers/smt2/smt2_parser.h>

struct syntactic_templatet
{
    std::vector<irep_idt> nt_ids;
    std::map<irep_idt, std::vector<exprt>> production_rules;
};

struct synth_functiont
{
    typet type;
    std::vector<irep_idt> parameters;
    syntactic_templatet grammar;

    explicit synth_functiont(const typet &_type) : type(_type)
    {
    }

    synth_functiont(
      const syntactic_templatet &_grammar,
      const typet &_type,
      const std::vector<irep_idt> &_parameters)
      : type(_type), parameters(_parameters),grammar(_grammar)
    {
      PRECONDITION(
        (_type.id() == ID_mathematical_function &&
         to_mathematical_function_type(_type).domain().size() ==
           _parameters.size()) ||
        (_type.id() != ID_mathematical_function && _parameters.empty()));
    }
};


#endif /*_EMU_SYNTACTIC_TEMPLATE_H_*/