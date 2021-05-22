
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



void init(long &i,long &n, long &sn)
{
  sn = 0; i = 1;
}

//    (or 

void unroll_trans(long &i,long &n, long &sn)
{
  if(i < n)
  {
    i++;
    sn++;
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

	long i, n, sn;

  srand (timeSinceEpochMillisec());
  unsigned int unroll = rand()%50; 

  sn = rand()%20;
  init(i, n, sn);
  for(int ind=0; ind<unroll; ind++)
    unroll_trans(i, n, sn);
	std::cout << format(i) << " " << format(n)<<" "<< format(sn)<<" "<< format(rand()%50)<<" "<< format(rand()%50)<<" "<< format(rand()%50)<<std::endl;

	return 0;
}
