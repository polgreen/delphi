
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



void init(long &x,long &y)
{
  x = 0; y = 0;
}

//    (or 

void unroll_trans(long &x,long &y)
{
  if(y <=0)
    y = y +x;
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

	long x, y;

  srand (timeSinceEpochMillisec());
  unsigned int unroll = rand()%50; 

  init(x,y);
  for(int i=0; i<unroll; i++)
    unroll_trans(x,y);
	std::cout << format(x) << " " << format(y)<<std::endl;

	return 0;
}
