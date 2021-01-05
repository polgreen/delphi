#ifndef _EMU_ORACLE_CONSTRAINT_GEN_H_
#define _EMU_ORACLE_CONSTRAINT_GEN_H_

#include <util/expr.h>

struct oracle_constraint_gent
{
  irep_idt binary_name;
  std::vector<exprt> input_parameters;
  std::vector<exprt> return_parameters;
  exprt constraint;
  
  oracle_constraint_gent(
    const irep_idt _binary_name,
    const std::vector<exprt> & _input_parameters,
    const std::vector<exprt> & _output_parameters,
    const exprt &_constraint)
    : binary_name(_binary_name), 
      input_parameters(_input_parameters), 
      return_parameters(_output_parameters), 
      constraint(_constraint)
  {
  }
};

#endif /*_EMU_ORACLE_CONSTRAINT_GEN_H_*/
