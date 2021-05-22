#include <stdio.h>
#include <stdlib.h>

const int array[] = {
3,
4,
4,
5,
6,
8,
10,
11,
11,
11,
14,
15,
16,
17,
17,
18,
18,
19,
21,
21,
23,
24,
25,
26,
26,
27,
29,
29,
30,
31,
32,
32,
32,
33,
34,
37,
39,
40,
41,
45,
46,
46,
47,
50,
52,
52,
53,
54,
54,
54,
56,
58,
58,
60,
61,
61,
62,
62,
65,
66,
68,
69,
70,
70,
71,
72,
73,
73,
74,
74,
75,
75,
76,
77,
77,
78,
78,
79,
81,
83,
85,
86,
86,
87,
88,
92,
92,
92,
93,
94,
95,
95,
97,
99,
99,
99,
99,
100,
100,
100
};

int main(int argc, const char *argv[])
{
  unsigned elements = (sizeof array)/sizeof(int);

  if(argc != 2)
  {
    fprintf(stderr, "please give an index\n");
    exit(1);
  }

  int index = atoi(argv[1]);

  if(index<0 || index>=elements)
  {
    fprintf(stderr, "index out of bounds\n");
    exit(1);
  }

  printf("(_ bv%d 32)\n", array[index]);
}
