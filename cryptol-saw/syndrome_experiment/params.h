#define GFBITS 12
#define SYS_N 3488
#define SYS_T 64
#define PK_NROWS (SYS_T*GFBITS) 
#define PK_NCOLS (SYS_N - PK_NROWS)
#define PK_ROW_BYTES ((PK_NCOLS + 7)/8)
#define SYND_BYTES ((PK_NROWS + 7)/8)
#define TESTS 42069

void syndrome_function(unsigned char *s, const unsigned char *pk, unsigned char *e);

void test(int seed)
{
  int i, j;
  unsigned char pk[SYND_BYTES*8*PK_ROW_BYTES];
  unsigned char e[SYND_BYTES + PK_ROW_BYTES];
  unsigned char s[SYND_BYTES];

  srand(seed);

  for (j = 0; j < TESTS; j++){
    for (i = 0; i < SYND_BYTES*8*PK_ROW_BYTES; i++)
      pk[i] = rand() & 0xFF;
    for (i = 0; i < SYND_BYTES + PK_ROW_BYTES; i++)
      e[i] = rand() & 0xFF;
    syndrome_function(s, pk, e);
  }
}