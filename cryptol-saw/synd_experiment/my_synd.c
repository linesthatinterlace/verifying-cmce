#include "params.h"

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
    out[j] = 0;
    for (k = 0; k < 8; k++) {
      addvals[j][k] = 0;
    }
  }
  synd_byte_seleinv(inits, byt, f, lis);
  synd_byte_addvals(addvals, inits, lis);
  synd_byte_add(out, addvals);
}

void synd_function(gf out[2*SYS_T], gf f[SYS_T + 1], gf L[SYS_N], unsigned char r[SYS_N/8])
{	
  int i, j, k;
  gf addvals[2*SYS_T][8];
  gf inits[8];
  gf *ptr_L = L;

  for (k = 0; k < 8; k++) {
    inits[k] = 0;
  }

	for (j = 0; j < 2*SYS_T; j++) {
    out[j] = 0;
    for (k = 0; k < 8; k++) {
      addvals[j][k] = 0;
    }
  }
	for (j = 0; j < 2*SYS_T; j++) {
    synd_byte_seleinv(inits, r[i], f, ptr_L);
    synd_byte_addvals(addvals, inits, ptr_L);
    synd_byte_add(out, addvals);
    ptr_L += 8;
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