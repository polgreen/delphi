#include <math.h>
#include <stdio.h>
#include <stdlib.h>

#define BITS 4
#define MAX ((1<<BITS)-1)

int main(int argc, const char *argv[])
{
  if(argc != 2)
  {
    fprintf(stderr, "please give a number\n");
    return 1;
  }

  int input = atoi(argv[1]);

  int output = cos(((double)input)/MAX * M_PI/2) * MAX;

  printf("(_ bv%d %d)\n", output, BITS);
}
