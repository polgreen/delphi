#!/bin/bash

# turn the given pixel processing function into C

./smt2c "$1" > pixel_oracle.c

cat << EOM >> pixel_oracle.c

unsigned char *stbi_load(char const *filename, int *x, int *y, int *channels_in_file, int desired_channels);
int printf(const char * restrict, ...) __attribute__((__format__ (__printf__, 1, 2)));
void *malloc(unsigned long);

unsigned char target(unsigned char pixel)
{
  if(pixel < 40)
    return 0;
  return pixel; // invert
}

int main()
{
  int x, y, n;
  // get grayscale
  const unsigned char *data_src = stbi_load("foto.jpg", &x, &y, &n, 1);
  if(data_src == 0)
    return 1;

  // number of pixels
  const int pixels = x * y;

  // make two copies of the image
  unsigned char *data_target = malloc(pixels);
  unsigned char *data_tweak = malloc(pixels);

  // transform using reference function
  for(int index = 0; index < pixels; index++)
    data_target[index] = target(data_src[index]);

  // transform using synthesized function
  for(int index = 0; index < pixels; index++)
    data_tweak[index] = tweak(data_src[index]);

  // compare with target
  int count=0;
  int success=1;
  for(int index = 0; index < pixels; index++)
  {
    if(data_target[index] != data_tweak[index])
    {
      success=0;
      // they differ; report the expected mapping
      if(count%37==0)
        printf("false (_ bv%d 8) (_ bv%d 8)\n", data_src[index], data_target[index]);
      count++;
    }
  }

  if(success==1)
    printf("true (_ bv%d 8) (_ bv%d 8)\n", 0, 0);
}
EOM

# compile

gcc pixel_oracle.c stb_image.o -o pixel_oracle

# run

./pixel_oracle
