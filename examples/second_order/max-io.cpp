
#include <cassert>
#include <iostream>
#include <sstream>

int max(int x, int y)
{
	if(x>y)
		return x;
	else 
		return y;
}

int main(int argc, const char *argv[])
{

	if(argc!=3 || !(isdigit(*argv[1]) && isdigit(*argv[2])))
	{
		std::cout<<"This is an input-output oracle for the function\n"
		<< "(synth-fun max ((x Int)(y Int))(z Int)).";
		std::cout<<"The oracle takes two input arguments: a value for x and y. \n"
		<< "It returns the correct assignment for z "
		<< "as an SMTlib model.\n";
		return 1;
	}

	int x;
	int y;

	// arg 1 is x
	std::istringstream ssX(argv[1]);
	if(!(ssX >> x))
		std::cerr<<"Unable to parse X "<<std::endl;

	std::istringstream ssY(argv[2]);
	if(!(ssY >> y))
		std::cerr<<"Unable to parse y "<<std::endl;

	std::cout<<"(_ bv"<< max(x,y)<< " 32)\n"; 

	return 0;

}