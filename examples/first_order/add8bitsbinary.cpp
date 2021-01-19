
#include <cassert>
#include <iostream>
#include <sstream>
#define WIDTH 8

int answer(int x, int y)
{
  return (x+y) % (1<<(WIDTH-1));
}

int main(int argc, const char *argv[])
{
	if(argc!=3 || !(isdigit(*argv[1])) || !(isdigit(*argv[2])))
	{
		std::cout<<"This is the oracle for add8bitsbinary\n"
		<< "it takes 2 inputs, which are bitvector values\n";
		std::cout
		<< "It returns the sum\n";
		return 1;
	}

	int x, y;

	// arg 1 is x
	std::istringstream ssX(argv[1]);
	if(!(ssX >> x))
		std::cerr<<"Unable to parse input value"<<std::endl;

	// arg 2 is y
	std::istringstream ssY(argv[2]);
	if(!(ssY >> y))
		std::cerr<<"Unable to parse input value"<<std::endl;

	std::cout<< "(_ bv" << answer(x, y) << " " << WIDTH << ")\n"; 

	return 0;
}
