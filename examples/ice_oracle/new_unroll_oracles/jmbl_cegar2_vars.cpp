
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



void init(long &x, long&m, long&n)
{
  x = 0; m = 0;
}

//    (or 

void unroll_trans(long &x, long&m, long&n)
{
  if(x < n)
  {
    x++;
    if(rand()%2 == 0)
      m = x;
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

	long x, m, n;

  srand (timeSinceEpochMillisec());
  unsigned int unroll = rand()%50; 

  n = rand()%20;
  init(x, m, n);
  for(int i=0; i<unroll; i++)
    unroll_trans(x, m, n);
	std::cout << format(x) << " " << format(m)<<" "<< format(n)<< format(rand()%50)<< format(rand()%50)<< format(rand()%50)<<std::endl;

	return 0;
}
