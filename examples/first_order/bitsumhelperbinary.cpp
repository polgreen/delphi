
#include <cassert>
#include <iostream>
#include <sstream>

//(bvand x (bvsub x (_ bv1 9))))

int answer (int width, int x)
{
	if(x!=0)
		x = x%(1 << width); // wrap
  return x&(x-1);

}

int main(int argc, const char *argv[])
{

	if(argc!=3 || !(isdigit(*argv[1]) && isdigit(*argv[2])))
	{
		std::cout<<"This is the oracle for binaryhelperbinary\n"
		<< "it takes 2 inputs, the first specifies the width of the bitvec, the second is the bitvec value";
		std::cout
		<< "It returns a single bitvec value\n";
		return 1;
	}

	int x, width;

  std::istringstream ssWidth(argv[1]);
  if(!(ssWidth >> width))
    std::cerr<<"Unable to parse input width "<<std::endl;

	// arg 1 is x
	std::istringstream ssX(argv[2]);
	if(!(ssX >> x))
		std::cerr<<"Unable to parse input value"<<std::endl;



	std::cout<< answer(width,x)<< "\n"; 

	return 0;

}