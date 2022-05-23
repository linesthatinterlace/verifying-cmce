/*
  This file is for Niederreiter encryption
*/

#include "../imp/encrypt.h"

#include "../imp/util.h"
#include "../imp/params.h"
#include "../imp/randombytes.h"

#include <stdint.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>

#include "../imp/gf.h"

static inline unsigned char same_mask(uint16_t x, uint16_t y)
{
	uint32_t mask;

	mask = x ^ y;
	mask -= 1;
	mask >>= 31;
	mask = -mask;

	return mask & 0xFF;
}

/* output: e, an error vector of weight t */
static void gen_e(unsigned char *e)
{
	int i, j, eq, count;

	union 
	{
		uint16_t nums[ SYS_T*2 ];
		unsigned char bytes[ SYS_T*2 * sizeof(uint16_t) ];
	} buf;

	uint16_t ind[ SYS_T ];
	unsigned char mask;	
	unsigned char val[ SYS_T ];	

	while (1)
	{
		randombytes(buf.bytes, sizeof(buf));

		for (i = 0; i < SYS_T*2; i++)
			buf.nums[i] = load_gf(buf.bytes + i*2);

		// moving and counting indices in the correct range

		count = 0;
		for (i = 0; i < SYS_T*2 && count < SYS_T; i++)
			if (buf.nums[i] < SYS_N)
				ind[ count++ ] = buf.nums[i];
		
		if (count < SYS_T) continue;

		// check for repetition

		eq = 0;

		for (i = 1; i < SYS_T; i++) 
			for (j = 0; j < i; j++)
				if (ind[i] == ind[j]) 
					eq = 1;

		if (eq == 0)
			break;
	}

	for (j = 0; j < SYS_T; j++)
		val[j] = 1 << (ind[j] & 7);

	for (i = 0; i < SYS_N/8; i++) 
	{
		e[i] = 0;

		for (j = 0; j < SYS_T; j++)
		{
			mask = same_mask(i, (ind[j] >> 3));

			e[i] |= val[j] & mask;
		}
	}
}


/* input: public key pk, error vector e */
/* output: syndrome s */
static void syndrome(unsigned char *s, const unsigned char *pk, unsigned char *e)
{
	unsigned char b, row[SYS_N/8];
	const unsigned char *pk_ptr = pk;

	int i, j;

	for (i = 0; i < SYND_BYTES; i++)
		s[i] = 0;

	for (i = 0; i < PK_NROWS; i++)	
	{
		for (j = 0; j < SYS_N/8; j++) 
			row[j] = 0;

		for (j = 0; j < PK_ROW_BYTES; j++) 
			row[ SYS_N/8 - PK_ROW_BYTES + j ] = pk_ptr[j];

		row[i/8] |= 1 << (i%8);
		
		b = 0;
		for (j = 0; j < SYS_N/8; j++)
			b ^= row[j] & e[j];

		b ^= b >> 4;
		b ^= b >> 2;
		b ^= b >> 1;
		b &= 1;

		s[ i/8 ] |= (b << (i%8));

		pk_ptr += PK_ROW_BYTES;
	}
}

unsigned char b_func(const unsigned char b_in)
{
  unsigned char b = b_in;
  b ^= b >> 4;
  b ^= b >> 2;
  b ^= b >> 1;
  b &= 1;
  return b;
}

void syndrome_loop(const unsigned char *e, const unsigned char *pk_ptr, const uint16_t i, unsigned char *s)
{
  unsigned char b, row[SYS_N/8];
  int j;
  
  for (j = 0; j < SYS_N/8; j++) 
    row[j] = 0;

  for (j = 0; j < PK_ROW_BYTES; j++) 
    row[ SYS_N/8 - PK_ROW_BYTES + j ] = pk_ptr[j];

  row[i/8] |= 1 << (i%8);

  b = 0;
  for (j = 0; j < SYS_N/8; j++)
    b ^= row[j] & e[j];

  s[ i/8 ] |= (b_func(b) << (i%8));
}

void syndrome_outer(unsigned char *s, const unsigned char *pk, unsigned char *e)
{
	const unsigned char *pk_ptr = pk;

	int i;

	for (i = 0; i < SYND_BYTES; i++)
		s[i] = 0;

	for (i = 0; i < PK_NROWS; i++)
  {
    syndrome_loop(e, pk_ptr, i, s);
    pk_ptr += PK_ROW_BYTES;
  }
}


void encrypt(unsigned char *s, const unsigned char *pk, unsigned char *e)
{
	gen_e(e);

#ifdef KAT
  {
    int k;
    printf("encrypt e: positions");
    for (k = 0;k < SYS_N;++k)
      if (e[k/8] & (1 << (k&7)))
        printf(" %d",k);
    printf("\n");
  }
#endif

	syndrome(s, pk, e);
}


unsigned char bytes_bit_dotprod(const unsigned char *u, const unsigned char *v, size_t n)
{
  unsigned char b;
  int i;
  b = 0;
  for (i = 0; i < n; i++)
    b ^= u[i] & v[i];
  
  return b_func(b);
}

unsigned char bytes_bit_mul_block(const unsigned char *u, const unsigned char *v, size_t n)
{
	const unsigned char *u_ptr = u;
  unsigned char b;
  int i;
  b = 0;
  for (i = 0; i < 8; i++)
  {
    b += (bytes_bit_dotprod(u_ptr, v, n) << i);
    u_ptr += n;
  }

  return b;
}

void syndrome_bytewise(unsigned char *s, const unsigned char *pk, unsigned char *e)
{
	const unsigned char *pk_ptr = pk;
  const unsigned char *eid = e;
  const unsigned char *epk = e + SYND_BYTES;
	int i;
	for (i = 0; i < SYND_BYTES; i++)
	{
  	s[i] = eid[i] ^ bytes_bit_mul_block(pk_ptr, epk, PK_ROW_BYTES);
    pk_ptr += 8*PK_ROW_BYTES;
  }
}