#include "dump_problems.h"
#include <util/namespace.h>
#include <util/message.h>
#include "../problem.h"
#include <iostream>
#include "../expr2sygus.h"
#include <util/expr.h>
#include <string.h>


std::string convert_type(typet &type)    
{
    if(type.id()==ID_unsignedbv || type.id()==ID_signedbv)
    {
       return  "(_ BitVec " + 
        std::to_string(to_bitvector_type(type.subtype()).get_width()) + ")";
    }
    else if(type.id()==ID_bool)
    {
        return "Int";
    }
    else if(type.id()==ID_integer)
    {
        return "Int";
    }
    else
    {
        return "UNKNOWNTYPE";
    }

}

std::string print_synth_fun(const irep_idt &id, const synth_functiont &definition)
{
    std::string result = "(declare-fun " + clean_id(id) + " ";

    if(definition.type.id()!=ID_mathematical_function)
    {
        result += "()" + type2sygus(definition.type);
    }
    else
    {
        result += "(";
        const auto &func_type = to_mathematical_function_type(definition.type);
        for (std::size_t i = 0; i < definition.parameters.size(); i++)
        {
            result += type2sygus(func_type.domain()[i]) + " ";
        }
        result += ")  " + type2sygus(func_type.codomain());
    }
    return result += ")\n";
}

void print_sygus_problem(const problemt &problem)
{
  std::cout<< "(set-logic " << problem.logic << ")" << std::endl;
  for(const auto &f: problem.synthesis_functions)
  {
    std::cout<< synth_fun_dec(f.first, f.second) << std::endl;
  }

  for(const auto &v: problem.free_variables)
  {
    std::cout<<"(declare-var " << id2string(to_symbol_expr(v).get_identifier())
            <<" " <<convert_type(v.type()) << ")" << std::endl;
  }
  // the alternative constraints are used when we want the proper invariant constraints
  if(problem.alternative_constraints.size()==0)
    for(const auto &c: problem.constraints)
         std::cout<<"( constraint  "<<expr2sygus(c)<<" ) "<<std::endl;
  else
  {
    for(const auto &c: problem.alternative_constraints)
         std::cout<<"( constraint  "<<expr2sygus(c)<<" ) "<<std::endl;
  }
      std::cout<<"(check-synth)"<<std::endl;
}

void print_smt_problem(const problemt &problem)
{
    std::cout<< "(set-logic " << problem.logic << ")" << std::endl;
    std::cout<< "(set-option :produce-models true)" << std::endl;


    for(const auto &f: problem.synthesis_functions)
    {
        std::cout<< print_synth_fun(f.first, f.second) << std::endl;
    }

    // constraints
    std::cout<<"(assert (forall (";
    for(const auto &v: problem.free_variables)
    {   
        std::cout<<"(" << id2string(to_symbol_expr(v).get_identifier())<< " " <<convert_type(v.type()) << ")";
    }
    std::cout<<") "; 

    if(problem.constraints.size()>1)
        std::cout<<" (and ";

    for(const auto &c: problem.constraints)
    {
        std::cout<<" "<<expr2sygus(c)<<" "<<std::endl;
    }

    if(problem.constraints.size()>1)
        std::cout<<" )";//close conjunction

    std::cout<<"))"<<std::endl;//close forall body and assert 
    std::cout<<"(check-sat)"<<std::endl;
    std::cout<<"(get-model)"<<std::endl;
}

void print_smt_solution_check(const problemt &problem, 
                              const std::string &solution)
{
    std::cout<< "(set-logic " << problem.logic << ")" << std::endl;
    std::cout<< "(set-option :produce-models true)" << std::endl;

    std::cout<<solution<<std::endl;
    
    for(const auto &v: problem.free_variables)
    {
        std::cout<<"(declare-fun " << id2string(to_symbol_expr(v).get_identifier())
            <<" () " <<convert_type(v.type()) << ")" << std::endl;
    }

    // constraints
    std::cout<<"(assert (not  ";

    const auto& problem_constraints = 
        (problem.alternative_constraints.size()==0)?
            problem.constraints:problem.alternative_constraints;
        
    if(problem_constraints.size()>1)
        std::cout<<" (and ";
    
    for(const auto &c: problem_constraints)
        std::cout<<" "<<expr2sygus(c)<<" "<<std::endl;


    if(problem_constraints.size()>1)
        std::cout<<" )";//close conjunction
    
    std::cout<<"))"<<std::endl;//close not and assert 

    std::cout<<"(check-sat)"<<std::endl;
    std::cout<<"(get-model)"<<std::endl;
}

