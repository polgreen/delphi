#define STB_IMAGE_IMPLEMENTATION
#include "stb_image.h"

#define STB_IMAGE_WRITE_IMPLEMENTATION
#include "stb_image_write.h"

unsigned char target(unsigned char pixel)
{
  return ~ pixel; // invert
}

int main()
{
  int x, y, n;
  // get grayscale
  unsigned char *data = stbi_load("foto.jpg", &x, &y, &n, 1);
  if(data == 0)
    return 1;

  // number of pixels
  const int pixels = x * y;

  // transform using reference function
  for(int index = 0; index < pixels; index++)
    data[index] = target(data[index]);

  // save to disc
  stbi_write_jpg("foto-target.jpg", x, y, 1, data, 0);
}
