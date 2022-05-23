#include <stdio.h>
#include <stdlib.h>
#include "params.h"

unsigned char b_func(const unsigned char b_in)
{
  unsigned char b = b_in;
  b ^= b >> 4;
  b ^= b >> 2;
  b ^= b >> 1;
  b &= 1;
  return b;
}

unsigned char bytes_bit_dotprod(const unsigned char *u, const unsigned char *v)
{
  unsigned char b;
  int i;
  b = 0;
  for (i = 0; i < PK_ROW_BYTES; i++)
    b ^= u[i] & v[i];
  
  return b_func(b);
}

unsigned char bytes_bit_mul_block(const unsigned char *u, const unsigned char *v)
{
	const unsigned char *u_ptr = u;
  unsigned char b;
  int i;
  b = 0;
  for (i = 0; i < 8; i++)
  {
    b += (bytes_bit_dotprod(u_ptr, v) << i);
    u_ptr += PK_ROW_BYTES;
  }

  return b;
}

void syndrome_function(unsigned char *s, const unsigned char *pk, unsigned char *e)
{
	const unsigned char *pk_ptr = pk;
  const unsigned char *eid = e;
  const unsigned char *epk = e + SYND_BYTES;
	int i;
	for (i = 0; i < SYND_BYTES; i++)
	{
  	s[i] = eid[i] ^ bytes_bit_mul_block(pk_ptr, epk);
    pk_ptr += 8*PK_ROW_BYTES;
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