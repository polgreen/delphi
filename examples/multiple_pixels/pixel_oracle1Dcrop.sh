#!/bin/bash

# turn the given pixel processing function into C

./smt2c "$1" > pixel_oracle.c

cat << EOM >> pixel_oracle.c

unsigned char *stbi_load(char const *filename, int *x, int *y, int *channels_in_file, int desired_channels);
int printf(const char * restrict, ...) __attribute__((__format__ (__printf__, 1, 2)));
void *malloc(unsigned long);

unsigned char target(unsigned char pixel, unsigned char columns, unsigned char rows)
{
  if(rows < 100)
    return 1;
  else
    return pixel;
}

int main()
{
  int x, y, n;
  // get grayscale
  const unsigned char *data_src = stbi_load("foto2.jpg", &x, &y, &n, 1);
  if(data_src == 0)
    return 1;

  // number of pixels
  const int pixels = x * y;

  // make two copies of the image
  unsigned char *data_target = malloc(pixels);
  unsigned char *data_tweak = malloc(pixels);

  // transform using reference function

  for(int i = 0; i < x; i++)
    for (int j=0; j < y; j++)
      data_target[i+x*j] = target(data_src[i+x*j], i, j);

  // transform using synthesized function
  for(int i = 0; i < x; i++)
    for (int j=0; j < y; j++)
      data_tweak[i+x*j] = tweak(data_src[i+x*j], i, j);

  int count=0;    
  // compare with target
  for(int i = 0; i < x; i++)
    for (int j=0; j < y; j++)
      if(data_target[i+x*j] != data_tweak[i+x*j])
      {
      // they differ; report the expected mapping
        if(count%10==0)
          printf("false (_ bv%d 8)(_ bv%d 8)(_ bv%d 8) (_ bv%d 8)\n", data_src[i+x*j], i, j, data_target[i+x*j]);
        count++;
      }


  // they matchindexx*indexy
  printf("true (_ bv%d 8) (_ bv%d 8) (_ bv%d 8) (_ bv%d 8)\n", 0,0,0, 0);
}
EOM

# compile

gcc pixel_oracle.c stb_image.o -o pixel_oracle

# run

./pixel_oracle
