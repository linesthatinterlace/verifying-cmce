#ifndef crypto_kem_mceliece348864_H
#define crypto_kem_mceliece348864_H

#define crypto_kem_mceliece348864_sse_PUBLICKEYBYTES 261120
#define crypto_kem_mceliece348864_sse_SECRETKEYBYTES 6492
#define crypto_kem_mceliece348864_sse_CIPHERTEXTBYTES 128
#define crypto_kem_mceliece348864_sse_BYTES 32

 
#ifdef __cplusplus
extern "C" {
#endif
extern int crypto_kem_mceliece348864_sse_keypair(unsigned char *,unsigned char *);
extern int crypto_kem_mceliece348864_sse_enc(unsigned char *,unsigned char *,const unsigned char *);
extern int crypto_kem_mceliece348864_sse_dec(unsigned char *,const unsigned char *,const unsigned char *);
#ifdef __cplusplus
}
#endif

#define crypto_kem_mceliece348864_keypair crypto_kem_mceliece348864_sse_keypair
#define crypto_kem_mceliece348864_enc crypto_kem_mceliece348864_sse_enc
#define crypto_kem_mceliece348864_dec crypto_kem_mceliece348864_sse_dec
#define crypto_kem_mceliece348864_PUBLICKEYBYTES crypto_kem_mceliece348864_sse_PUBLICKEYBYTES
#define crypto_kem_mceliece348864_SECRETKEYBYTES crypto_kem_mceliece348864_sse_SECRETKEYBYTES
#define crypto_kem_mceliece348864_BYTES crypto_kem_mceliece348864_sse_BYTES
#define crypto_kem_mceliece348864_CIPHERTEXTBYTES crypto_kem_mceliece348864_sse_CIPHERTEXTBYTES

#endif
