#include <util/namespace.h>
#include <util/message.h>
#include "../problem.h"
#include <iostream>
#include "../expr2sygus.h"
#include <util/expr.h>
#include <string.h>
#include "check_solution.h"



int check_solution( problemt &problem, 
                    const std::string sol_string, 
                    const namespacet &ns,
                    verifyt& verify)
{
    std::istringstream arg_stream(sol_string);
    auto arg_parsed = define_fun_parser(arg_stream);
    
    solutiont solution;
    solution.functions[symbol_exprt(arg_parsed.id, arg_parsed.type)] = arg_parsed.body;

    switch(verify(problem, solution))
    {
    case verifyt::PASS:
      std::cout<<"Verification passed" <<std::endl;
      return 1;
    case verifyt::FAIL:
        std::cout<<"Verification failed" <<std::endl; 
        return 0;    
    }
}