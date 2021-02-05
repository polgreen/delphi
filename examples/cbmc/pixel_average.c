unsigned char tweak(unsigned char parameter0$0) {
  if(parameter0$0==0)
    return 20;
  if(parameter0$0==10)
    return 30;
  return 120;
}


unsigned char *stbi_load(char const *filename, int *x, int *y, int *channels_in_file, int desired_channels);
int printf(const char * restrict, ...) __attribute__((__format__ (__printf__, 1, 2)));

int main()
{
  int x, y, n;
  // get grayscale
  unsigned char *data = stbi_load("foto.jpg", &x, &y, &n, 1);
  if(data == 0)
    return 1;

  // number of pixels
  const int pixels = x * y;

  // transform using given function
  for(int index = 0; index < pixels; index++)
    data[index] = tweak(data[index]);

  // compute the average
  unsigned long long sum = 0;
  for(int index = 0; index < pixels; index++)
    sum += data[index];
 
  unsigned char average = sum/pixels;
 
  // output average in SMT-LIB format
  printf("(_ bv%d 8)\n", average);
}
