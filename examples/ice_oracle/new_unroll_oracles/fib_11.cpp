
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



void init(long &x, long&i, long&j)
{
  if(x < 0)
    x = -x;
  if(x==0)
    x ++;
	i = 0;
  j = 0;
}

//    (or 
//(and (< i x) (and (= j! (+ j 2)) (and (= i! (+ i 1)) (= x! x)))) (and (>= i x) (and (= j! j) (and (= i! i) (= x! x))))))

void unroll_trans(long &x, long&i, long&j)
{
  if(i < x)
  {
    j = j+2;
    i = i+1;
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

	long x, i, j;

  srand (timeSinceEpochMillisec());
  unsigned int unroll = rand()% 10; 

  x = rand();
  init(x, i, j);
  for(int ind=0; ind<unroll; ind++)
    unroll_trans(x,i,j);
	std::cout << format(x) << " " << format(i)<<" "<< format(j)<<std::endl;

	return 0;
}
