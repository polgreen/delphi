
#include <cassert>
#include <iostream>
#include <sstream>


int main(int argc, const char *argv[])
{

	if(argc!=2 || !(isdigit(*argv[1])))
	{
		std::cout<<"This is the oracle for the constant oracle\n";
		std::cout<<"The oracle takes one input arguments. \n"
		<< "It returns a correct assignment for z "
		<< "as an SMTlib model.\n";
		return 1;
	}

	int x;


	// arg 1 is x
	std::istringstream ssX(argv[1]);
	if(!(ssX >> x))
		std::cerr<<"Unable to parse X "<<std::endl;


	if(x==5)
		std::cout<<"true\n";
	else
		std::cout<<"false \n";


	return 0;

}