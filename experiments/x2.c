#include <math.h>
#include <stdio.h>

double midpoint = 100.123456;

double f(double x)
{
  return fabs(midpoint-x);
}

double delta_f(double x)
{
  return x >= midpoint ? 1 : -1;
}

int sign(double x)
{
  return x<0 ? -1 : x==0 ? 0 : 1;
}

void gradient_descent()
{
  double x = 0;
  double gamma = 0.1;
  double previous_delta = 0;
  unsigned step = 0;

  while(1)
  {
    double value = f(x);
    printf("step = %u, gamma = %lf, x = %lf, f(x) = %lf\n", step, gamma, x, value);

    if(value >= -0.00001 && value <= 0.00001)
      break;

    // differentiate
    double delta = delta_f(x);

    if(delta == 0)
      break;

    // overshot?
    if(previous_delta != 0 && sign(previous_delta) != sign(delta))
      gamma *= 0.1;
    else
      gamma *= 1.1;

    // step
    x -= delta * gamma;

    previous_delta = delta;

    step++;
  }
}

int main()
{
  gradient_descent();
}
