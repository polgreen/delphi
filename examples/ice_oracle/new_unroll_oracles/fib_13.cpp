
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



void init(long &j, long&k, long&t)
{
  j = 2;
  k = 0;
}

//    (or 

void unroll_trans(long &j, long&k, long&t)
{
  if(t==0)
  {
    j = j+4;
  }
  else
  {
    j = j+2;
    k = k+1;
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

	long j, k, t;

  srand (timeSinceEpochMillisec());
  unsigned int unroll = rand()% 10; 

  t = rand();
  init(j, k, t);
  for(int i=0; i<unroll; i++)
    unroll_trans(j, k, t);
	std::cout << format(j) << " " << format(k)<<" "<< format(t)<<std::endl;

	return 0;
}
