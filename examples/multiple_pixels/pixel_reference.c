#define STB_IMAGE_IMPLEMENTATION
#include "stb_image.h"

#define STB_IMAGE_WRITE_IMPLEMENTATION
#include "stb_image_write.h"

// transformations


// unsigned char target(unsigned char pixel, unsigned char columns, unsigned char rows)
// {
//   if(rows < 10 || columns < 10)
//     return 1;
//   // else
//   //   return 0;
//   return pixel;
// }

unsigned char target(unsigned char pixel00, unsigned char pixel01, unsigned char pixel10, unsigned char pixel11)
{
  if(pixel00 < 206)
    return (pixel00)+50;
 return pixel00; 
}


int main()
{
  int x, y, n;
  // get grayscale
  unsigned char *data = stbi_load("foto.jpg", &x, &y, &n, 1);
  if(data == 0)
    return 1;


  // transform using reference function
  for(int i = 0; i < x; i++)
    for (int j=0; j < y; j++)
    {
      // data[i+x*j] = target(data[i+x*j], i, j);
      data[i+x*j] = target(data[i+x*j], data[(i+1)+(j+1)*x], data[(i)+(j+1)*x], data[(i+1)+(j)*x]);
    }

  // save to disc
  stbi_write_jpg("foto2-target.jpg", x, y, 1, data, 0);
}
