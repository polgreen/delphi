
#include <cassert>
#include <iostream>
#include <sstream>
#define WIDTH 9

//(bvand x (bvsub x (_ bv1 9))))

int answer (int x)
{
	// std::cout<<"width is "<< WIDTH << "and max value is " << (1u << 9) << "!";
  return x+10;
}

int main(int argc, const char *argv[])
{

	if(argc!=2 || !(isdigit(*argv[1])))
	{
		std::cout<<"This is the oracle for binaryhelperbinary\n"
		<< "it takes 1 input, the bitvec value";
		std::cout
		<< "It returns a single bitvec value\n";
		return 1;
	}

	int x;

	// arg 1 is x
	std::istringstream ssX(argv[1]);
	if(!(ssX >> x))
		std::cerr<<"Unable to parse input value"<<std::endl;



	std::cout<< "(_ bv" <<answer(x)<< " 32)\n"; 

	return 0;

}