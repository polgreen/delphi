
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



void init(long &c, long&n)
{
  c = 0; 
  if(n<0)
    n = -n;
  if(n==0)
    n++;
}

//    (or 

void unroll_trans(long &c, long&n)
{
  if(c!=n)
  {
    c++;
  }
  else
    c = 1;
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

	long c, n;

  srand (timeSinceEpochMillisec());
  unsigned int unroll = rand()%50; 

  n = rand()%20;
  init(c, n);
  for(int i=0; i<unroll; i++)
    unroll_trans(c, n);
	std::cout << format(c) << " " << format(n)<<" "<< format(rand()%20)<<" "<< format(rand()%20)<< " "<< format(rand()%20) <<std::endl;

	return 0;
}
