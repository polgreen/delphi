
#include <cassert>
#include <iostream>
#include <sstream>
#include <random>
#include <chrono>
#include <string>

uint64_t timeSinceEpochMillisec() {
  using namespace std::chrono;
  return duration_cast<milliseconds>(system_clock::now().time_since_epoch()).count();
}



void init(long &x, long&y, long randvar)
{
	x = randvar;
	y = randvar;
}


void unroll_trans(long &x, long &y)
{
	if(x>1)
	{
		x --;
	}
}

std::string format(long x)
{
  std::string result;
  if(x < 0)
    result =  "(- " + std::to_string(x*-1) + " )";
  else
    result  = std::to_string(x);
  return result;
}

int main(int argc, const char *argv[])
{

	long x,y;

  srand (timeSinceEpochMillisec());
  unsigned int unroll = rand()% 10; 


	// arg 1 is x
	// std::istringstream ssUnroll(argv[1]);
	// if(!(ssUnroll >> unroll))
	// 	std::cerr<<"Unable to parse unroll long "<<std::endl;

  init(x,y, rand()%30);
  for(int i=0; i<unroll; i++)
    unroll_trans(x,y);

	std::cout << format(x) << " " << format(y)<<" ";



  std::cout << format(x) << " " << format(y)<<std::endl;
	return 0;
}