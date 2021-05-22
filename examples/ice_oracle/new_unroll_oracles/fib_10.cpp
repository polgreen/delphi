
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



void init(long &x, long&y, long&w, long&z)
{
	x = 0;
	y = 0;
  w = 1;
  z = 0;
}


void unroll_trans(long &x, long&y, long&w, long&z)
{
  long tmpx, tmpy, tmpw, tmpz;
  if(w==1 && z==0)
  {
    x = x+1;
    w= 0;
    y = y+1;
    z = 1;
  }
  else if(w==1 && z==0)
  {
    y = y+1;
    z = 1;
  }
  else if(w==1 && z!=0)
  {
    x = x+1;
    w = 0;
  }
  else if(w!=1 && z!=0)
  {
    // do nothing;
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

	long x,y, z, w;

  srand (timeSinceEpochMillisec());
  unsigned int unroll = rand()% 50; 

  init(x,y, w, z);
  for(int i=0; i<unroll; i++)
    unroll_trans(x,y, w, z);
	std::cout << format(x) << " " << format(y)<<" "<< format(w)<<" "<<format(z)<<" "<<std::endl;

	return 0;
}
