#include "define_fun_parser.h"

#include "../../src/emu/expr2sygus.h"
#include "../../src/emu/sygus_parser.h"

#include <util/cmdline.h>
#include <util/mathematical_types.h>

#include <vector>
#include <string>
#include <random>
#include <iostream>
#include <cassert>
#include <sstream>
#include <fstream>
#include <cstdlib>

#include <ansi-c/expr2c.h>

#include <util/config.h>
#include <util/exception_utils.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>
#include <util/namespace.h>

#define CBMC_ORACLE_OPTIONS                                               \
  "(oracle) "                                                             \
  "(pos)"                                                                 \
  "(neg)"                                                                 \
  "(impl)"                                                                \
  "(all)"                                                                \

std::string ssystem (const char *command) 
{
    char tmpname [L_tmpnam];
    std::tmpnam ( tmpname );
    std::string scommand = command;
    std::string cmd = scommand + " >> " + tmpname;
    std::system(cmd.c_str());
    std::ifstream file(tmpname, std::ios::in );
    std::string result;
        if (file) {
      while (!file.eof()) result.push_back(file.get());
          file.close();
    }
    remove(tmpname);
    return result;
}


void implication(std::ostream &out, std::string candidate, std::string transf, std::string variable_decls)
{
	out << variable_decls;
  out << transf;
	out << candidate << "\n";
	out << "(assert (and (inv-f x y)(trans-f x y x! y!)(not (inv-f x! y!))))\n";
	out << "(check-sat)\n";
	out << "(get-model)\n";
}

void positive(std::ostream &out, std::string candidate, std::string pref, std::string variable_decls)
{
	out << variable_decls;
	out << pref;
	out << candidate << "\n";
	out << "(assert (and (not (inv-f x y))(pre-f x y)))\n";
	out << "(check-sat)\n";
	out << "(get-model)\n";
}

void negative(std::ostream &out, std::string candidate, std::string postf, std::string variable_decls)
{
	out << variable_decls;
	out << postf;
	out << candidate << "\n";
	out << "(assert (and (inv-f x y)(not (post-f x y))))\n";
	out << "(check-sat)\n";
	out << "(get-model)\n";
}


bool model_exists(std::string &input)
{

	std::size_t success = input.find("unsat");
	std::size_t fail = input.find("sat");
	if(success!=std::string::npos)
	{
		return true;
	}
	else if(fail!=std::string::npos)
	{
		return false;
	}
	else
	{
		std::cerr<<"SMT solver error: \n";
		assert(0);
	}
}

std::string remove_unsat_prefix(std::string input)
{
  std::string unsat;
  std::string::size_type c_pos = input.find("unsat\n");
  if (c_pos != std::string::npos &&
      input.rfind("unsat\n") == c_pos)
    input.erase(0, c_pos + 6);
  std::string::size_type c_pos2 = input.find("sat\n");
  if (c_pos2 != std::string::npos &&
      input.rfind("sat\n") == c_pos2)
    input.erase(0, c_pos2 + 4);

  return input;
}



std::pair<bool,std::string> call_smt_solver(std::string candidate, 
  std::string pref, std::string postf, std::string transf, 
  std::set<symbol_exprt> variable_set, cmdlinet cmdline)
{
  std::string variable_declarations;
  std::pair<bool, std::string> result;
  for (const auto &v : variable_set)
    variable_declarations += expr2sygus_var_dec(v);
  if (cmdline.isset("pos") || cmdline.isset("all"))
  {
    std::ofstream posfile("pos-file.smt2");

    if (!posfile)
    {
      throw std::exception();
    }
    positive(posfile, candidate, pref, variable_declarations);
    posfile.close();
    std::string command("z3 pos-file.smt2");
    result.second = ssystem(command.c_str());
    result.first = model_exists(result.second);
    if(cmdline.isset("pos")|| !result.first)
      return result;
  }
  if (cmdline.isset("neg") || cmdline.isset("all"))
  {
    std::ofstream negfile("neg-file.smt2");
    if (!negfile)
    {
      throw std::exception();
    }
    negative(negfile, candidate, postf, variable_declarations);
    negfile.close();
    std::string command = "z3 neg-file.smt2";
    result.second = ssystem(command.c_str());
    result.first = model_exists(result.second);
    if(cmdline.isset("neg")|| !result.first)
      return result;
  }
  if (cmdline.isset("impl") || cmdline.isset("all"))
  {
    std::ofstream implicationfile("imp-file.smt2");
    if (!implicationfile)
    {
      throw std::exception();
    }
    implication(implicationfile, candidate, transf, variable_declarations);
    implicationfile.close();
    std::string command = "z3 imp-file.smt2";
    result.second = ssystem(command.c_str());
    result.first = model_exists(result.second);
    return result;
  }
  return result;
}

int main(int argc, const char *argv[])
{
  cmdlinet cmdline;
  if(cmdline.parse(argc, argv, CBMC_ORACLE_OPTIONS))
  {
    std::cerr << "Usage error\n";
    return 1;
  }

  try
  {
    define_fun_resultt input_fun;
    std::size_t arg_size = cmdline.args.size();
    // parse old spec
    std::ifstream in(cmdline.args[arg_size-2]);
    sygus_parsert parser(in);
    parser.parse();

    std::string pref_string, postf_string, transf_string;

    auto transf = parser.id_map.find("trans-f");
    auto pref = parser.id_map.find("pre-f");
    auto postf = parser.id_map.find("post-f");

    if(transf==parser.id_map.end())
    {
      std::cerr<<"unable to find trans-f";
      assert(0);
    }
    if(pref==parser.id_map.end())
    {
      std::cerr<<"unable to find pre-f";
      assert(0);
    }
    if(postf==parser.id_map.end())
    {
      std::cerr<<"unable to find post-f";
      assert(0);
    }


    transf_string = expr2sygus_fun_def(symbol_exprt(transf->first, transf->second.type),transf->second.definition);
    pref_string = expr2sygus_fun_def(symbol_exprt(pref->first, pref->second.type),pref->second.definition);
    postf_string = expr2sygus_fun_def(symbol_exprt(postf->first, postf->second.type),postf->second.definition);  

    std::istringstream arg_stream(cmdline.args[arg_size-1]);
    input_fun = define_fun_parser(arg_stream);

    // call smt solver
    std::pair<bool, std::string> result = call_smt_solver(
      expr2sygus_fun_def(symbol_exprt(input_fun.id, input_fun.type),input_fun.body),
      pref_string, postf_string, transf_string,
      parser.variable_set, cmdline);
    std::istringstream stream(remove_unsat_prefix(result.second));

    std::map<irep_idt, exprt> arg_parsed; 

    if(result.first==true)
    {
     std::cout<<"true ";
    }
    else
    {
      std::cout<<"false ";
      arg_parsed = model_parser(stream);
    }

    std::vector<std::string> arg_ids = {"x","y"};

    for(const auto &input: arg_ids)
    {
      if(arg_parsed.find(input)==arg_parsed.end())
        std::cout <<" 1 ";
      else
      {
        std::cout << expr2sygus(arg_parsed[input]) << " ";
      }
    }
    if (cmdline.isset("impl"))
    {
      for (const auto &input : arg_ids)
      {
        std::string id = input + "!";
        if (arg_parsed.find(input) == arg_parsed.end())
          std::cout << " 1 ";
        else
        {
          std::cout << expr2sygus(arg_parsed[input]) << " ";
        }
      }
    }
    std::cout<<std::endl;
  }
  catch(const cprover_exception_baset &error)
  {
    std::cerr << "Error: " << error.what() << '\n';
  }
  catch(const char *s)
  {
    std::cerr << "Error: " << s << '\n';
  }
  catch(const std::string &s)
  {
    std::cerr << "Error: " << s << '\n';
  }
}
