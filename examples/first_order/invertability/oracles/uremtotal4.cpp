
#include <cassert>
#include <iostream>
#include <sstream>
#define WIDTH 32

  // (ite (= b (_ bv0 32)) a (bvurem a b))


int answer (unsigned int a, unsigned int b)
{
  if(b==0)
  {
  	return a;
  }	
  assert(a<(2^WIDTH));
  assert(b<(2^WIDTH));
  return a%b;
}

int main(int argc, const char *argv[])
{

	if(argc!=3 || !(isdigit(*argv[1])))
	{
		std::cout<<"This is the oracle for udivtotal\n"
		<< "it takes 2 inputs, the bitvec value";
		std::cout
		<< "It returns a single bitvec value\n";
		return 1;
	}

	unsigned int a, b;

	// arg 1 is x
	std::istringstream ssA(argv[1]);
	if(!(ssA >> a))
		std::cerr<<"Unable to parse input value"<<std::endl;

		std::istringstream ssB(argv[2]);
	if(!(ssB >> b))
		std::cerr<<"Unable to parse input value"<<std::endl;



	std::cout<< "(_ bv" <<answer(a, b)<< " " << WIDTH <<")\n"; 

	return 0;

}