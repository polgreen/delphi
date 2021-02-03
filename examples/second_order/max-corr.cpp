
#include <vector>
#include <string>
#include <random>
#include <iostream>
#include <cassert>
#include <sstream>
#include <fstream>
#include <cstdlib>

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


void outputSMTFile(std::ostream &out, std::string candidate)
{
	out << "(set-logic BV)\n";
	out << "(declare-fun x () (_ BitVec 32)) \n";
	out << "(declare-fun y () (_ BitVec 32)) \n";
	out << candidate << "\n";
	out << "(assert (or (not (bvuge (max x y) x))\n";
	out << "(not (bvuge (max x y) y))\n"; 
	out << "(not(or (= x (max x y)) (= y (max x y))))))\n";
	out << "(check-sat)\n";

}

int parse_result(std::string &input)
{
	std::size_t success = input.find("unsat");
	std::size_t fail = input.find("sat");
	if(success!=std::string::npos)
	{
		std::cerr<<"Result is definitely unsat"<<std::endl;
		std::cout<<"true \n";
		return 0;
	}
	else if(fail!=std::string::npos)
	{
	//	input.erase(0, input.find("(model"));
		std::cout<<"false \n";//<<input;
		return 0;
	}
	else
	{
		std::cout<<"SMT solver error: \n";
		std::cout<<input<<std::endl;
		return 1;
	}
}

int main(int argc, const char *argv[])
{
	if(argc!=2)
	{
		std::cout<<"This is a correctness oracle for the function\n"
		<< "(synth-fun max ((x Int)(y Int))(z Int)).";
		std::cout<<"The oracle takes a candidate implementation for max\n"
		<< "as an SMTlib string and returns true if the implementation is correct \n"
		<< "or a counterexample as an SMTlib model if the implementation is incorrect.\n"
		<< "For example: max-corr \"(define-fun max ((x Int) (y Int)) Int (ite (= x y) y x))\"\n";
		return 1;
	}

	std::string candidate = std::string(argv[1]);
	std::cerr<<"Got argument "<< candidate<<std::endl;

	std::ofstream smtfile ("corr-file.smt2");
	if(!smtfile) {throw std::exception();}
	outputSMTFile(smtfile, candidate);
	smtfile.close();
	std::string command ("z3 corr-file.smt2");
	std::string result = ssystem(command.c_str());
	std::cerr<<"Got result "<< result<<std::endl;
	return parse_result(result);
}