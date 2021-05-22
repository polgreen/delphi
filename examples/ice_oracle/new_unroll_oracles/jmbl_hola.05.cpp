
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



void init(long &x,long &y, long &i,long &j)
{
  x = 0; y = 0;i = 0; j = 0;
}

//    (or 

void unroll_trans(long &x,long &y, long &i,long &j)
{
  long oldx = x;
  long oldy = y;
  x++;
  y++;
  i = i+oldx + 1;
  if(rand()%2==0)
    j = j + oldy + 1;
  else
    j = j + oldy + 2;

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

	long x, y, i, j;

  srand (timeSinceEpochMillisec());
  unsigned int unroll = rand()%50; 

  init(x, y, i, j);
  for(int ind=0; ind<unroll; ind++)
    unroll_trans(x, y, i, j);
	std::cout << format(x) << " " << format(y)<<" "<< format(i)<<" "<< format(j)<<std::endl;

	return 0;
}
