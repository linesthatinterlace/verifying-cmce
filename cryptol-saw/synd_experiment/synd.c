#include "params.h"
//

void synd_function(gf *out, gf *f, gf *L, unsigned char *r)
{
	int i, j;
	gf e, e_inv, c;

	for (j = 0; j < 2*SYS_T; j++)
		out[j] = 0;

	for (i = 0; i < SYS_N; i++)
	{
		c = (r[i/8] >> (i%8)) & 1;

		e = eval(f, L[i]);
		e_inv = gf_inv(gf_mul(e,e));

		for (j = 0; j < 2*SYS_T; j++)
		{
			out[j] = gf_add(out[j], gf_mul(e_inv, c));
			e_inv = gf_mul(e_inv, L[i]);
		}
	}
}

int main (int argc, char *argv[]) {
  if (argc!=2){
    printf("Exactly one argument please.");
    exit(1);
  }
  
  int arg1 = atoi(argv[1]);
  test(arg1);

  return 0;
}