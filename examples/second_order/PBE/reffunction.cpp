
#include <cassert>
#include <iostream>
#include <sstream>
#include <stdlib.h>  
#define WIDTH 32

// put the reference function in here
int answer (unsigned int a)
{
  return a + 7;
}

int main(int argc, const char *argv[])
{

	if(argc!=3 || !(isdigit(*argv[1])))
	{
		std::cout<<"This is the oracle for rand\n"
		<< "it takes 1 inputs, the bitvec value";
		std::cout
		<< "It returns a single bitvec value\n";
		return 1;
	}

	unsigned int a;

	// arg 1 is x
	std::istringstream ssA(argv[1]);
	if(!(ssA >> a))
		std::cerr<<"Unable to parse input value"<<std::endl;


	std::cout<< "(_ bv" <<answer(a)<< " " << WIDTH <<")\n"; 

	return 0;

}