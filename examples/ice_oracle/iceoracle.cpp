#include "define_fun_parser.h"

#include "../../src/delphi/expr2sygus.h"
#include "../../src/delphi/sygus_parser.h"

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
  "(constraints)"                                                        \

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


void implication(std::ostream &out, const define_fun_resultt &candidate, const std::string &transf)
{
  out << transf;
  out << expr2sygus_fun_def(symbol_exprt(candidate.id, candidate.type),candidate.body) << "\n";
  out << "(assert (and (inv-f ";
  for(const auto &p: candidate.parameters)
    out << clean_id(p)<<" ";
  out <<")(trans-f ";

  for(const auto &p: candidate.parameters)
    out << clean_id(p)<<" ";

  for(const auto &p: candidate.parameters)
    out << clean_id(p)<<"! ";

  out <<") (not (inv-f ";
  for(const auto &p: candidate.parameters)
    out << clean_id(p)<<"! ";

  out << "))))\n";
  out << "(check-sat)\n";
  out << "(get-model)\n";
}

void positive(std::ostream &out, const define_fun_resultt &candidate, const std::string &pref )
{
	out << pref;
	out << expr2sygus_fun_def(symbol_exprt(candidate.id, candidate.type),candidate.body) << "\n";
	out << "(assert (and (not (inv-f ";
  for(const auto &p: candidate.parameters)
    out << clean_id(p)<<" ";
  out <<"))(pre-f ";

  for(const auto &p: candidate.parameters)
    out << clean_id(p)<<" ";
  out <<")))\n";
	out << "(check-sat)\n";
	out << "(get-model)\n";
}


void negative(std::ostream &out, const define_fun_resultt &candidate, const std::string &postf)
{
  out << postf;
  out << expr2sygus_fun_def(symbol_exprt(candidate.id, candidate.type),candidate.body) << "\n";
  out << "(assert (and (not (post-f ";
  for(const auto &p: candidate.parameters)
    out << clean_id(p)<<" ";
  out <<"))(inv-f ";

  for(const auto &p: candidate.parameters)
    out << clean_id(p)<<" ";
  out <<")))\n";
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



std::pair<bool,std::string> call_smt_solver(define_fun_resultt candidate, 
  std::string pref, std::string postf, std::string transf, cmdlinet cmdline)
{
  std::pair<bool, std::string> result;
  std::string variable_declarations;
  const auto &domain = to_mathematical_function_type(candidate.type).domain();
  for(std::size_t i=0; i< domain.size(); i++)
    variable_declarations += expr2sygus_fun_dec(symbol_exprt(candidate.parameters[i], domain[i]));


  if (cmdline.isset("pos") || cmdline.isset("all"))
  {
    std::ofstream posfile("pos-file.smt2");

    if (!posfile)
    {
      throw std::exception();
    }
    posfile << variable_declarations;
    positive(posfile, candidate, pref);
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
    negfile << variable_declarations;
    negative(negfile, candidate, postf);
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
    implicationfile << variable_declarations;
    implication(implicationfile, candidate, transf);
    implicationfile.close();
    std::string command = "z3 imp-file.smt2";
    result.second = ssystem(command.c_str());
    result.first = model_exists(result.second);
    return result;
  }
  return result;
}

int output_oracle_constraints(std::vector<irep_idt> params, std::vector<typet> domain, std::string oracle_suffix)
{
  // only works for ints
  std::string input1string = "(inv-f (-> ";
  for(const auto &d: domain)
    input1string+=type2sygus(d)+" ";
  input1string+=" Bool))";

  std::string output1string = "(B Bool)";
  std::string output2string;

  for(std::size_t i=0; i<params.size(); i++)
  {
    output1string+="("+ clean_id(params[i]) + " ";
    output1string+=type2sygus(domain[i])+")";
    output2string+="("+ clean_id(params[i]) + "! ";
    output2string+=type2sygus(domain[i])+")";
  }

// positive constraint
  std::cout<<"(oracle-constraint iceoracle_pos"<<oracle_suffix<<" ("
          << input1string <<")("
          << output1string <<")";
  std::cout<<"\n(=> (not B)(= (inv-f ";
  for(const auto &p: params)
      std::cout<<clean_id(p)<<" ";
  std::cout<<") true )))\n"; 

  std::cout<<"(oracle-constraint iceoracle_neg"<<oracle_suffix<<" ("
          << input1string <<")("
          << output1string <<")";
  std::cout<<"\n(=> (not B)(= (inv-f ";
  for(const auto &p: params)
      std::cout<<clean_id(p)<<" ";
  std::cout<<") false )))\n";      

  std::cout<<"(oracle-constraint iceoracle_impl"<<oracle_suffix<<" ("
          << input1string <<")("
          << output1string << output2string<<")";
  std::cout<<"\n(=> (not B)(=> (inv-f ";
  for(const auto &p: params)
      std::cout<<clean_id(p)<<" ";
  std::cout<<")(inv-f ";
  for(const auto &p: params)
      std::cout<<clean_id(p)<<"! ";  
  std::cout<<"))))\n";
  return 1;
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
    std::size_t arg_size = cmdline.args.size();
    std::size_t file_location=2;
    std::ifstream in(cmdline.args[arg_size-file_location]);

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

    if(cmdline.isset("constraints"))
    {

      return output_oracle_constraints(pref->second.parameters,
        to_mathematical_function_type(pref->second.type).domain(), cmdline.args.back());
    }

    transf_string = expr2sygus_fun_def(symbol_exprt(transf->first, transf->second.type),transf->second.definition);
    pref_string = expr2sygus_fun_def(symbol_exprt(pref->first, pref->second.type),pref->second.definition);
    postf_string = expr2sygus_fun_def(symbol_exprt(postf->first, postf->second.type),postf->second.definition); 


    std::istringstream arg_stream(cmdline.args[arg_size-1]);
    define_fun_resultt input_fun = define_fun_parser(arg_stream);


    // call smt solver
    std::pair<bool, std::string> result = call_smt_solver(input_fun,
      pref_string, postf_string, transf_string, cmdline);
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


    for(const auto &input: input_fun.parameters)
    {
      auto res = arg_parsed.find(clean_id(input));
      if(res==arg_parsed.end())
        std::cout <<" 1 ";
      else
      {
        std::cout << expr2sygus(res->second) << " ";
      }
    }
    if (cmdline.isset("impl"))
    {
      for (const auto &input : input_fun.parameters)
      {
        std::string id = clean_id(input) + "!";
        auto res = arg_parsed.find(id);
        if (res == arg_parsed.end())
          std::cout << " 1 ";
        else
        {
          std::cout << expr2sygus(res->second) << " ";
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
