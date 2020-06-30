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

    // step
    x -= value * delta * gamma;

    step++;
  }
}

int main()
{
  gradient_descent();
}
