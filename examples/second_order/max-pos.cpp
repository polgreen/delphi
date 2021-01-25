
#include <cassert>
#include <iostream>
#include <sstream>
#include <random>

bool randomBool() {
   return rand() > (RAND_MAX / 2);
}

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
	int x,y;

	if(randomBool)
	{
		x = rand()%50+100;
		y = 

	}
	int x = rand();
	int y = rand();

	std::cout<<x <<" "<< y <<" "<< max(x,y)<<std::endl;

	// std::cout<<"(model \n" 
	// << "(define-fun x () Int "<< x << ")\n"
	// << "(define-fun y () Int "<< y << ")\n"
	// << "(define-fun z () Int "<< max(x,y)<< "))\n"; 

	return 0;

}