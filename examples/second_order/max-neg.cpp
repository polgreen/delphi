
#include <cassert>
#include <iostream>
#include <sstream>
#include <random>
#include <time.h>


int max(int x, int y)
{
	if(x>y)
		return y;
	else if(x==y)
	{
		while(1)
		{
			int z=rand();
			if(z!=y && z!=x)
				return z;
		}
	}
	else
		return x;
}

int main(int argc, const char *argv[])
{
	if(argc!=1)
	{
		std::cout<<"This is a negative witness oracle for the function\n"
		<< "(synth-fun max ((x Int)(y Int))(z Int)).";
		std::cout<<"The oracle takes no input arguments and \n"
		<< "returns a single negative witness assignment to x, y and z\n"
		<< "as an SMTlib model.\n";
		return 1;
	}

	srand (time(NULL));
	int x = rand();
	int y = rand();


	std::cout<<"(model \n" 
	<< "(define-fun x () Int "<< x << ")\n"
	<< "(define-fun y () Int "<< y << ")\n"
	<< "(define-fun z () Int "<< max(x,y)<< "))\n"; 

	return 0;

}