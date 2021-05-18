#include "cvc4_synth.h"
#include <util/mathematical_expr.h>
#include <util/arith_tools.h>
#include <util/expr.h>
#include <iostream>
#include <util/tempfile.h>
#include <util/run.h>
#include <fstream>
#include "../expr2sygus.h"
#include <algorithm>

void replace_local_var(exprt &expr, const irep_idt &target, exprt &replacement)
{
  if (expr.id() == ID_symbol)
  {
    if (to_symbol_expr(expr).get_identifier() == target)
      expr = replacement;
  }
  for (auto &op : expr.operands())
    replace_local_var(op, target, replacement);
}


void expand_let_expressions(exprt &expr)
{
  if (expr.id() == ID_let)
  {
    auto &let_expr = to_let_expr(expr);
    for (unsigned int i = 0; i < let_expr.variables().size(); i++)
    {
      INVARIANT(let_expr.variables()[i].id() == ID_symbol,
                "Let expression should have list of symbols, not " + let_expr.variables()[i].pretty());
      replace_local_var(let_expr.where(), to_symbol_expr(let_expr.variables()[i]).get_identifier(), let_expr.values()[i]);
    }
    expr = let_expr.where();
    expand_let_expressions(expr);
  }
  for (auto &op : expr.operands())
    expand_let_expressions(op);
}

void cvc4_syntht::set_program_size(std::size_t size)
{
  // do nothing
}

void cvc4_syntht::increment_synthesis_constraints()
{
  number_synth_constraints+=synth_constraint_increment;
}



std::string nonterminalID(const typet &type)
{
  if(type.id()==ID_unsignedbv || type.id()==ID_integer)
    return "NTnonbool";
  if(type.id()==ID_bool)
    return "NTbool";

  return "NTunknown";    
}


std::string production_rule(const typet &type, const mathematical_function_typet &functype, bool bitvecs)
{
  std::string NTid = nonterminalID(type);
  std::string result = "("+NTid+" "+type2sygus(type) +"(";
  std::size_t count=0;
  for(const auto &d: functype.domain())
  {
   if(d==type)
    result+="parameter"+integer2string(count, 10u)+" ";
   count++; 
  }
  if(type.id()!=ID_bool)
    result += expr2sygus(from_integer(0, type)) +" "+ 
              expr2sygus(from_integer(1, type))+" "+ 
              expr2sygus(from_integer(2, type))+" "+ 
              expr2sygus(from_integer(3, type)) + " "
              +"(Constant "+type2sygus(type)+")";

  if(type.id()==ID_unsignedbv)
  {
    result += "(bvadd "+NTid +" "+NTid+")";
    result += "(bvsub "+NTid +" "+NTid+")";
    result += "(bvshl "+NTid +" "+NTid+")";
    result += "(bvlshr "+NTid +" "+NTid+")";
    result += "(bvurem "+NTid +" "+NTid+")";
    // result += "(bvmul "+NTid +" "+NTid+")";
    // result += "(bvdiv "+NTid +" "+NTid+")";
    result += "(ite "+ nonterminalID(bool_typet())+ " "+NTid +" "+NTid+")";
    result+="))\n";
  }
  else if(type.id()==ID_bool)
  {
    std::string nonbool = nonterminalID(integer_typet());
    result+="(and " + NTid +" "+NTid+")";
    result+="(or " + NTid +" "+NTid+")";
    result+="(not " +NTid+")"; 
    result+="(= " + nonbool +" "+nonbool+")";
    if (bitvecs)
    {
      result += "(bvuge " + nonbool + " " + nonbool + ")";
      result += "(bvugt " + nonbool + " " + nonbool + ")";
    }
    else
    {
      result += "(>= " + nonbool + " " + nonbool + ")";
      result += "(> " + nonbool + " " + nonbool + ")";
    }
    result+="))\n";  
  }
  else if(type.id()==ID_integer)
  {
    result += "(+ "+NTid +" "+NTid+")";
    result += "(- "+NTid +" "+NTid+")";
    result += "(- "+NTid +")";
    result += "(ite "+ nonterminalID(bool_typet())+ " "+NTid +" "+NTid+")";
    result+="))\n";
  }

return result;
}

std::string production_rule(const typet &type, bool bitvecs)
{
  std::vector<typet> domain;
  mathematical_function_typet dummy_func_type(domain, type);
  return production_rule(type, dummy_func_type , bitvecs);
}

std::string build_grammar(const symbol_exprt &function)
{
  std::set<typet> types;
  bool integer=false;
  bool bv=false;
  bool hasbool=false;

  INVARIANT(function.type().id()==ID_mathematical_function, "expected function type");
  auto func = to_mathematical_function_type(function.type());
  for (const auto &t : func.domain())
  {
    if(t.id()==ID_integer)
      integer=true;
    if(t.id()==ID_unsignedbv) 
      bv=true;
    if(t.id()==ID_bool)
      hasbool=true;  
    if(t!=func.codomain())
      types.insert(t);
  }
  INVARIANT(!(bv & integer), "do not support grammars with both bv and int");
  INVARIANT(types.size()<=2, "do not support more than 2 types in a grammar");

  std::string nonterminals = "(( "+ nonterminalID(func.codomain())+ " "  + type2sygus(func.codomain()) + ")";
  std::string grammar = "(" + production_rule(func.codomain(), func,bv);

  for(const auto &t: types)
  {
    nonterminals += "("+ nonterminalID(t) +" " + type2sygus(t)+ ")";
    grammar += production_rule(t, func,bv) + "\n";
  }
  if(!hasbool && func.codomain().id()!=ID_bool)
  {
    nonterminals += "("+ nonterminalID(bool_typet()) +" " + type2sygus(bool_typet())+ ")";
    grammar += production_rule(bool_typet(),bv) + "\n";
  }

  grammar +=")\n";
  nonterminals +=")\n";
  return nonterminals + grammar;
}

std::string cvc4_syntht::build_query(const problemt &problem)
{
  std::string query = "(set-logic ALL)\n";

  // std::string grammar = "\n((Start Bool) (StartInt Int))\n";
  // grammar +="((Start Bool ((and Start Start)(or Start Start)(>= StartInt StartInt)(= StartInt StartInt)(not Start))) \n";
  // grammar +="(StartInt Int (parameter0 parameter1 0 1 2 3 (- StartInt) (+ StartInt StartInt)(- StartInt StartInt)(ite Start StartInt StartInt))\n";
  // grammar += "))\n";
  // grammar = "";


  // declare function
  for(const auto &f: problem.synthesis_functions)
  {
    // std::string grammar = use_grammar ? build_grammar(f) : " ";
    query += synth_fun_dec(f.first, f.second) + "\n";
  }


  std::size_t count=0;
  for(const auto &c: problem.synthesis_constraints)
  {  

    query += "(constraint " + expr2sygus(c)+ ")\n";
    count++;  
  }  

  query +="(check-synth)\n";
  return query;
}


decision_proceduret::resultt cvc4_syntht::read_result(std::istream &in, const problemt &problem)
{
  if (!in)
  {
    std::cout << "Failed to open input file";
    return decision_proceduret::resultt::D_ERROR;
  }
  std::string firstline;
  std::getline(in, firstline);
  if (firstline == "unknown")
  {
    // std::cout << "SyGuS solver says unknown \n"
    //           << std::endl;
    return decision_proceduret::resultt::D_UNSATISFIABLE;
  }

  sygus_parsert result_parser(in);
  try
  {
    result_parser.parse();
  }
  catch (const sygus_parsert::smt2_errort &e)
  {
    std::cout << e.get_line_no() << ": "
              << e.what() << std::endl;
    return decision_proceduret::resultt::D_ERROR;
  }
  if (result_parser.id_map.size() == 0)
  {
    // std::cout << "Inner synthesis phase failed or timed-out. ";
    return decision_proceduret::resultt::D_ERROR;
  }


  for (auto &id : result_parser.id_map)
  {
    std::cout<<"Results "<< id2string(id.first) <<std::endl;
    if(problem.synthesis_functions.find(id.first)!=problem.synthesis_functions.end())
    {
      if (id.second.type.id() == ID_mathematical_function)
      {
        symbol_exprt symbol = symbol_exprt(id.second.type);
        symbol.set_identifier(id.first);
        expand_let_expressions(id.second.definition);
        clean_symbols(id.second.definition);
        last_solution.functions[symbol] = id.second.definition;
      }
      else
      {
        symbol_exprt symbol = symbol_exprt(mathematical_function_typet({}, id.second.type));
        symbol.set_identifier(id.first);
        expand_let_expressions(id.second.definition);
        clean_symbols(id.second.definition);
        last_solution.functions[symbol] = id.second.definition;
      }
    }
  }
  return decision_proceduret::resultt::D_SATISFIABLE;
}


decision_proceduret::resultt cvc4_syntht::solve(const problemt &problem)
{
  const std::string query = build_query(problem);
// #ifdef DEBUG
  std::cout
      << "Solving query:\n"
      << query << std::endl;
// #endif

  temporary_filet
      temp_file_problem("sygus_problem_", ""),
      temp_file_stdout("sygus_stdout_", ""),
      temp_file_stderr("sygus_stderr_", "");
  {
    // we write the problem into a file
    std::ofstream problem_out(
        temp_file_problem(), std::ios_base::out | std::ios_base::trunc);
    problem_out << query;
  }

  std::vector<std::string> argv;
  std::string stdin_filename;


  // argv = {"cvc4", "--lang", "sygus2", "--sygus-active-gen=enum", "--no-sygus-pbe", temp_file_problem()};
  if(magic_constants)
    argv = {"cvc4", "--lang", "sygus2", "--sygus-active-gen=enum", "--sygus-grammar-cons=any-const", "--no-sygus-pbe", "--sygus-repair-const", temp_file_problem()};
  else
    argv = {"cvc4", "--lang", "sygus2", "--sygus-active-gen=enum", "--no-sygus-pbe", temp_file_problem()};
  
  int res =
      run(argv[0], argv, stdin_filename, temp_file_stdout(), temp_file_stderr());
  if (res < 0)
  {
    return decision_proceduret::resultt::D_ERROR;
  }
  else
  {
    std::ifstream in(temp_file_stdout());
    return read_result(in, problem);
  }
}

cvc4_syntht::resultt cvc4_syntht::operator()(const problemt &problem)
{

  const decision_proceduret::resultt result = solve(problem);

  switch (result)
  {
  case decision_proceduret::resultt::D_SATISFIABLE:
    if (last_solution.functions.empty())
    {
      for (const auto &f : problem.synthesis_functions)
      {
        last_solution.functions[symbol_exprt(f.first, f.second.type)] =
            from_integer(0, to_mathematical_function_type(f.second.type).codomain());
        
      }
    }
    return cvc4_syntht::resultt::CANDIDATE;

  case decision_proceduret::resultt::D_UNSATISFIABLE:
    return cvc4_syntht::resultt::NO_SOLUTION;

  case decision_proceduret::resultt::D_ERROR:
  default:
    return cvc4_syntht::resultt::NO_SOLUTION;
  }
}

exprt cvc4_syntht::model(exprt expr) const
{
  assert(expr.id()==ID_symbol);
  auto iter = last_solution.functions.find(to_symbol_expr(expr));
  assert(iter!=last_solution.functions.end());
  return iter->second;
}

solutiont cvc4_syntht::get_solution() const
{
  return last_solution;
}

// void cvc4_syntht::add_ce(
//   const counterexamplet &counterexample)
// {
//   counterexamples.emplace_back(counterexample);
// }