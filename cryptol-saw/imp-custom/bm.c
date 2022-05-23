/*
  This file is for the Berlekamp-Massey algorithm
  see http://crypto.stanford.edu/~mironov/cs359/massey.pdf
*/

#include "../imp/params.h"
#include "../imp/gf.h"
#include "../imp/bm.h"

#define min(a, b) ((a < b) ? a : b)

/* the Berlekamp-Massey algorithm */
/* input: s, sequence of field elements */
/* output: out, minimal polynomial of s */

void bm(gf *out, gf *s)
{
	int i;

	uint16_t N = 0;
	uint16_t L = 0;
	uint16_t mle;
	uint16_t mne;

	gf T[ SYS_T+1  ];
	gf C[ SYS_T+1 ];
	gf B[ SYS_T+1 ];

	gf b = 1, d, f;

	//

	for (i = 0; i < SYS_T+1; i++)
		C[i] = B[i] = 0;

	B[1] = C[0] = 1;

	//

	for (N = 0; N < 2 * SYS_T; N++)
	{
		d = 0;

		for (i = 0; i <= min(N, SYS_T); i++)
			d ^= gf_mul(C[i], s[ N-i]);
	
		mne = d; mne -= 1;   mne >>= 15; mne -= 1;
		mle = N; mle -= 2*L; mle >>= 15; mle -= 1;
		mle &= mne;

		for (i = 0; i <= SYS_T; i++)			
			T[i] = C[i];

		f = gf_frac(b, d);

		for (i = 0; i <= SYS_T; i++)			
			C[i] ^= gf_mul(f, B[i]) & mne;

		L = (L & ~mle) | ((N+1-L) & mle);

		for (i = 0; i <= SYS_T; i++)			
			B[i] = (B[i] & ~mle) | (T[i] & mle);

		b = (b & ~mle) | (d & mle);

		for (i = SYS_T; i >= 1; i--) B[i] = B[i-1];
		B[0] = 0;
	}

	for (i = 0; i <= SYS_T; i++)
		out[i] = C[ SYS_T-i ];
}

void bm_calc(gf * d_pt, const gf *s, const gf *C, const uint16_t N)
{
  int i;
	*d_pt = 0;

  for (i = 0; i <= min(N, SYS_T); i++)
    *d_pt ^= gf_mul(C[i], s[ N-i]);
}

void bm_modif(const uint16_t N, const gf d, gf *B, gf *C, gf *b_pt, uint16_t *L_pt)
{
  gf f;
	int i;
	uint16_t mle;
	uint16_t mne;
	gf T[ SYS_T+1  ];

  mne = d; mne -= 1;   mne >>= 15; mne -= 1;
  mle = N; mle -= 2*(*L_pt); mle >>= 15; mle -= 1;
  mle &= mne;

  for (i = 0; i <= SYS_T; i++)			
    T[i] = C[i];

  f = gf_frac(*b_pt, d);

  for (i = 0; i <= SYS_T; i++)			
    C[i] ^= gf_mul(f, B[i]) & mne;

  *L_pt = (*L_pt & ~mle) | ((N+1-*L_pt) & mle);

  for (i = 0; i <= SYS_T; i++)			
    B[i] = (B[i] & ~mle) | (T[i] & mle);

  *b_pt = (*b_pt & ~mle) | (d & mle);

  for (i = SYS_T; i >= 1; i--) B[i] = B[i-1];
  
  B[0] = 0;
}
void bm_loop(const gf *s, const uint16_t N, gf *B, gf *C, gf *b_pt, uint16_t *L_pt)
{
  gf d;

  bm_calc(&d, s, C, N);

  bm_modif(N, d, B, C, b_pt, L_pt);
}

void bm_outer(gf *out, gf *s)
{
	int i;

	uint16_t N = 0;
	uint16_t L = 0;

	gf C[ SYS_T+1 ];
	gf B[ SYS_T+1 ];

	gf b = 1;

	//

	for (i = 0; i < SYS_T+1; i++)
		C[i] = B[i] = 0;

	B[1] = C[0] = 1;

	//

	for (N = 0; N < 2 * SYS_T; N++)
	  bm_loop(s, N, B, C, &b, &L);

	for (i = 0; i <= SYS_T; i++)
		out[i] = C[ SYS_T-i ];
}