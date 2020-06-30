#include <math.h>
#include <stdio.h>

double midpoint = 100.123456;

double f(double x)
{
  return fabs(midpoint-x);
}

double delta_f(double x, double gamma)
{
  double xdiff = 1 * gamma;

  while(1)
  {
    double value = f(x);

    if(value == 0)
      return 0;

    double delta_x_pos = f(x + xdiff)-value;
    double delta_x_neg = f(x - xdiff)-value;

    if(delta_x_pos == 0 && delta_x_neg == 0)
      return 0;

    if(delta_x_pos > 0 && delta_x_neg > 0)
    {
      // getting worse in both directions, reduce xdiff,
      // and do another iteration
      xdiff *= 0.1;
    }
    else
    {
      // pick direction
      if(delta_x_pos < delta_x_neg)
        return delta_x_pos * (1/xdiff);
      else
        return - delta_x_neg * (1/xdiff);
    }
  }
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

    // differentiate
    double delta = delta_f(x, gamma);

    printf("step = %u, gamma = %lf, x = %lf, f(x) = %lf, delta = %lf\n", step, gamma, x, value, delta);

    if(value >= -0.00001 && value <= 0.00001)
      break;

    if(delta == 0)
      break;

    // overshot?
    if(previous_delta != 0 && sign(previous_delta) != sign(delta))
      gamma *= 0.1;
    else
      gamma *= 1.1;

    // step
    x -= value * delta * gamma;

    previous_delta = delta;

    step++;
  }
}

int main()
{
  gradient_descent();
}
