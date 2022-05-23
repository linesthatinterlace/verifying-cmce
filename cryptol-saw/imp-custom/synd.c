/*
  This file is for syndrome computation
*/

#include "../imp/synd.h"

#include "../imp/params.h"
#include "../imp/root.h"

#include <stdio.h>

/* input: Goppa polynomial f, support L, received word r */
/* output: out, the syndrome of length 2t */
void synd(gf *out, gf *f, gf *L, unsigned char *r)
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

void synd_loop(gf *out, gf *f, gf li, gf c)
{
  int j;
	gf e, e_inv;
  e = eval(f, li);
  e_inv = gf_inv(gf_mul(e,e));

  for (j = 0; j < 2*SYS_T; j++)
  {
    out[j] = gf_add(out[j], gf_mul(e_inv, c));
    e_inv = gf_mul(e_inv, li);
  }
}

void synd_outer(gf *out, gf *f, gf *L, unsigned char *r)
{
	int i;

	for (i = 0; i < 2*SYS_T; i++)
		out[i] = 0;

	for (i = 0; i < SYS_N; i++)
    synd_loop(out, f, L[i], (r[i/8] >> (i%8)) & 1);
}

//


gf zadd (const gf z, const gf addval[8]) {
  int i;
  gf z_final;

  z_final = z;
  for (i = 0; i < 8; i++)
    z_final = gf_add(z_final, addval[i]);

  return z_final;
}

void synd_byte_add (gf zs[2*SYS_T], const gf addvals[2*SYS_T][8]) {
  int i;

  for (i = 0; i < 2*SYS_T; i++) {
    zs[i] = zadd(zs[i], addvals[i]);
  }
}

void synd_byte_einv (gf out[8], const gf f[SYS_T + 1], const gf lis[8]) {
  int i;
  gf e;

  for (i = 0; i < 8; i++) {
    e = eval(f, lis[i]);
		out[i] = gf_inv(gf_mul(e,e));
  }
}

void selector (gf out[8], unsigned char byt) {
  int i;

  for (i = 0; i < 8; i++)
    out[i] &= ~(((byt >> i) & 1) - 1);
}

void synd_byte_seleinv (gf out[8], unsigned char byt, gf f[SYS_T + 1], gf lis[8]) {
  int i;

  for (i = 0; i < 8; i++) {
    out[i] = 0;
  }
  
  synd_byte_einv(out, f, lis);

  selector(out, byt);
}

void synd_byte_addvals (gf out[2*SYS_T][8], gf inits[8], gf lis[8]) {
  int i, j;
  gf zval;

  for (j = 0; j < 2*SYS_T; j++) {
    for (i = 0; i < 8; i++) {
      out[j][i] = 0;
    }
  }
  for (i = 0; i < 8; i++) {
    zval = inits[i];

    for (j = 0; j < 2*SYS_T; j++) {
      out[j][i] = zval;
      zval = gf_mul(zval, lis[i]);
    }
  }
}

void synd_bytewise_byt (gf out[2*SYS_T], unsigned char byt, gf f[SYS_T + 1], gf lis[8])
{	
  int i, j, k;
  gf addvals[2*SYS_T][8];
  gf inits[8];

  for (k = 0; k < 8; k++) {
    inits[k] = 0;
  }

	for (j = 0; j < 2*SYS_T; j++) {
    for (k = 0; k < 8; k++) {
      addvals[j][k] = 0;
    }
  }
  synd_byte_seleinv(inits, byt, f, lis);
  synd_byte_addvals(addvals, inits, lis);
  synd_byte_add(out, addvals);
}

void synd_bytewise(gf out[2*SYS_T], gf f[SYS_T + 1], gf L[SYS_N], unsigned char r[SYS_N/8])
{	
  int i, j;

  gf *ptr_L = L;

	for (j = 0; j < 2*SYS_T; j++)
		out[j] = 0;

	for (j = 0; j < SYS_N/8; j++) {
    synd_bytewise_byt (out, r[j], f, ptr_L);
    ptr_L += 8;
  }

}

void synd_bytewise_init(gf out[SYS_N], gf f[SYS_T + 1], gf L[SYS_N], unsigned char r[SYS_N/8])
{ 
	int j;
  gf *ptr_L = L;
  gf *ptr_out = out;
  for (j = 0; j < SYS_N/8; j++) {
    synd_byte_seleinv(ptr_out, r[j], f, ptr_L);
    ptr_out += 8; 
    ptr_L += 8;
  }
}

void synd_bytewise_next(gf out[SYS_N], gf in[SYS_N], gf L[SYS_N])
{ 
	int j;

  for (j = 0; j < SYS_N; j++) {
    out[j] = gf_mul(in[j], L[j]);
  }
}

gf synd_bytewise_sum(gf curr[SYS_N]) {
  int i;
  gf z_final;

  z_final = 0;
  for (i = 0; i < SYS_N; i++)
    z_final = gf_add(z_final, curr[i]);

  return z_final;
}

void synd_bytewise_alt(gf out[2*SYS_T], gf f[SYS_T + 1], gf L[SYS_N], unsigned char r[SYS_N/8])
{	
  int i, j;
  gf row[2*SYS_T*SYS_N];
  gf *ptr_row = row;

	for (j = 0; j < 2*SYS_T; j++)
		out[j] = 0;
  
  synd_bytewise_init(ptr_row, f, L, r);
	
  for (j = 0; j < 2*SYS_T; j++) {
    out[j] = synd_bytewise_sum(ptr_row);
    synd_bytewise_next(ptr_row + SYS_N, ptr_row, L);
    ptr_row += SYS_N;
  }

}