
#include <cassert>
#include <iostream>
#include <sstream>
#include <random>

int max(int x, int y)
{
	if(x>y)
		return x;
	else 
		return y;
}

int main(int argc, const char *argv[])
{
	if(argc!=1)
	{
		std::cout<<"This is a positive witness oracle for the function\n"
		<< "(synth-fun max ((x Int)(y Int))(z Int)).";
		std::cout<<"The oracle takes no input arguments and \n"
		<< "returns a single positive witness assignment to x, y and z\n"
		<< "as an SMTlib model.\n";
		return 1;
	}
	srand (time(NULL));
	int x = rand();
	int y = rand();


	std::cout<< x << " "
	<< y << " "<<
	max(x,y)<< "\n"; 

	return 0;

}