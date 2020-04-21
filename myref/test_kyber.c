#include "api.h"
#include "indcpa.h"
#include "ntt.h"
#include "params.h"
#include "randombytes.h"
#include <assert.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// #define NTESTS 1000

// static int test_keys()
// {
//   unsigned int i;
//   unsigned char pk[CRYPTO_PUBLICKEYBYTES];
//   unsigned char sk[CRYPTO_SECRETKEYBYTES];
//   unsigned char ct[CRYPTO_CIPHERTEXTBYTES];
//   unsigned char key_a[CRYPTO_BYTES];
//   unsigned char key_b[CRYPTO_BYTES];

//   printf("running %d tests\n", NTESTS);

//   for(i=0;i<NTESTS;i++) {
//     //Alice generates a public key
//     crypto_kem_keypair(pk, sk);

//     //Bob derives a secret key and creates a response
//     crypto_kem_enc(ct, key_b, pk);

//     //Alice uses Bobs response to get her shared key
//     crypto_kem_dec(key_a, ct, sk);

//     if(memcmp(key_a, key_b, CRYPTO_BYTES))
//       printf("ERROR keys\n");
//   }

//   return 0;
// }

// static int test_invalid_sk_a()
// {
//   unsigned int i;
//   unsigned char pk[CRYPTO_PUBLICKEYBYTES];
//   unsigned char sk[CRYPTO_SECRETKEYBYTES];
//   unsigned char ct[CRYPTO_CIPHERTEXTBYTES];
//   unsigned char key_a[CRYPTO_BYTES];
//   unsigned char key_b[CRYPTO_BYTES];

//   for(i=0;i<NTESTS;i++) {
//     //Alice generates a public key
//     crypto_kem_keypair(pk, sk);

//     //Bob derives a secret key and creates a response
//     crypto_kem_enc(ct, key_b, pk);

//     //Replace secret key with random values
//     randombytes(sk, CRYPTO_SECRETKEYBYTES);

//     //Alice uses Bobs response to get her shared key
//     crypto_kem_dec(key_a, ct, sk);

//     if(!memcmp(key_a, key_b, CRYPTO_BYTES))
//       printf("ERROR invalid sk\n");
//   }

//   return 0;
// }

// static int test_invalid_ciphertext()
// {
//   unsigned int i;
//   unsigned char pk[CRYPTO_PUBLICKEYBYTES];
//   unsigned char sk[CRYPTO_SECRETKEYBYTES];
//   unsigned char ct[CRYPTO_CIPHERTEXTBYTES];
//   unsigned char key_a[CRYPTO_BYTES];
//   unsigned char key_b[CRYPTO_BYTES];
//   size_t pos;

//   for(i=0;i<NTESTS;i++) {
//     randombytes((unsigned char *)&pos, sizeof(size_t));

//     //Alice generates a public key
//     crypto_kem_keypair(pk, sk);

//     //Bob derives a secret key and creates a response
//     crypto_kem_enc(ct, key_b, pk);

//     //Change some byte in the ciphertext (i.e., encapsulated key)
//     ct[pos % CRYPTO_CIPHERTEXTBYTES] ^= 23;

//     //Alice uses Bobs response to get her shared key
//     crypto_kem_dec(key_a, ct, sk);

//     if(!memcmp(key_a, key_b, CRYPTO_BYTES))
//       printf("ERROR invalid ciphertext\n");
//   }

//   return 0;
// }

static void test_cpapke() {

  uint8_t msg[KYBER_INDCPA_MSGBYTES] = {0};
  uint8_t dec_msg[KYBER_INDCPA_MSGBYTES];
  uint8_t ct[KYBER_INDCPA_BYTES];
  uint8_t pk[KYBER_INDCPA_PUBLICKEYBYTES];
  uint8_t sk[KYBER_INDCPA_SECRETKEYBYTES];
  uint8_t coins[KYBER_SYMBYTES];

  const uint8_t ref_ct[KYBER_CIPHERTEXTBYTES] = {
//      0x78, 0xF0, 0xA3, 0xF7, 0xFD, 0xC3, 0xA4, 0xEF, 0x2D, 0xD4, 0x22, 0x6C,
//      0x82, 0x11, 0x58, 0x14, 0xA9, 0xEE, 0x3,  0xC5, 0x7B, 0xB7, 0x58, 0x2D,
//      0x74, 0x7B, 0x80, 0xE6, 0x75, 0x81, 0xD9, 0x94, 0x3A, 0xC6, 0xE4, 0x80,
//      0xC7, 0x97, 0xC8, 0x1B, 0x90, 0x6B, 0xC9, 0x8D, 0xD9, 0x7,  0x53, 0x7B,
//      0xBA, 0x17, 0x96, 0xC8, 0x53, 0x25, 0xC5, 0xD9, 0xED, 0xD1, 0x97, 0x86,
//      0x8B, 0x20, 0x65, 0xDC, 0x7E, 0xBA, 0xEA, 0xFF, 0x43, 0x2C, 0xDC, 0xE7,
//      0xF8, 0xA2, 0x15, 0x31, 0xB8, 0xAC, 0x51, 0x20, 0x90, 0x4A, 0x85, 0x71,
//      0xFF, 0xF7, 0x25, 0x8E, 0x64, 0xD9, 0x1F, 0xB9, 0x75, 0xA3, 0x1D, 0xA6,
//      0x33, 0x6A, 0x5,  0x3C, 0x7B, 0xF4, 0x6F, 0x9C, 0x6D, 0x45, 0x45, 0x99,
//      0xE8, 0x7,  0x64, 0x7F, 0xF2, 0xEF, 0x78, 0xED, 0xE7, 0x51, 0xC9, 0x5B,
//      0x68, 0x44, 0xDE, 0xB1, 0x1E, 0x5E, 0x15, 0x24, 0xD9, 0x1B, 0x4C, 0x29,
//      0x4D, 0x44, 0x6A, 0x9B, 0x4C, 0xAF, 0x4A, 0xE,  0x4B, 0x21, 0x2A, 0x74,
//      0x45, 0x56, 0x25, 0x1E, 0x5F, 0x71, 0xE5, 0xC8, 0x76, 0xAC, 0xEE, 0xFB,
//      0xFE, 0xA0, 0xB2, 0x9C, 0x17, 0x60, 0x36, 0xF,  0x5F, 0xA5, 0xEE, 0xDE,
//      0x3B, 0x4,  0xCA, 0x6E, 0xEB, 0x97, 0xBC, 0x3E, 0x86, 0xB6, 0x6D, 0xCF,
//      0x10, 0x65, 0x3,  0x25, 0xFA, 0x1B, 0x47, 0x6A, 0xBC, 0x7E, 0xF4, 0x4B,
//      0x90, 0x64, 0x35, 0x24, 0x2F, 0x50, 0xEF, 0xAC, 0x91, 0x8E, 0x75, 0x20,
//      0x7A, 0x68, 0xEE, 0xD9, 0x6B, 0xE0, 0x1D, 0x9D, 0x2C, 0x24, 0xA8, 0xAF,
//      0xA0, 0xBE, 0x51, 0x79, 0x3C, 0x34, 0xB3, 0xEA, 0xA3, 0xA2, 0x72, 0xEC,
//      0xC6, 0xC0, 0x8D, 0x8D, 0x92, 0xE2, 0xDB, 0x62, 0xC2, 0x88, 0xDE, 0xCB,
//      0xDF, 0xC7, 0xC,  0x8D, 0x70, 0x77, 0x4D, 0x79, 0x11, 0xDF, 0xF9, 0x41,
//      0x68, 0x3A, 0xFC, 0xD0, 0xAA, 0x20, 0x63, 0x7B, 0x3A, 0xDB, 0x70, 0xC8,
//      0x7E, 0xD4, 0xFF, 0x60, 0x88, 0xD,  0xFD, 0x41, 0xA1, 0x3C, 0x80, 0x3A,
//      0xE1, 0x30, 0x63, 0x35, 0x57, 0xE2, 0x7C, 0x17, 0x2B, 0xE2, 0xC3, 0xD,
//      0x8,  0xB5, 0xB5, 0x23, 0xE6, 0xBB, 0xD2, 0x7C, 0x7A, 0xF,  0x69, 0x99,
//      0x8,  0x33, 0xDB, 0x26, 0xF6, 0x3A, 0x4,  0x5D, 0xD1, 0x5D, 0x65, 0xD4,
//      0xBE, 0x1B, 0xD8, 0x58, 0x87, 0x31, 0xE,  0x30, 0xB,  0x74, 0x3,  0xAF,
//      0xA6, 0x85, 0x68, 0xB6, 0xB8, 0x7C, 0xC5, 0xD2, 0x47, 0xBE, 0x8B, 0xED,
//      0xFF, 0x7C, 0x9F, 0xD,  0x16, 0xE8, 0x2,  0x62, 0xE4, 0x1B, 0x9A, 0x5B,
//      0xB7, 0x26, 0x14, 0xA0, 0xEB, 0xFE, 0x90, 0x2C, 0x12, 0x3A, 0xEE, 0xFF,
//      0xF5, 0x2D, 0x84, 0x77, 0xE3, 0x9E, 0x51, 0xE7, 0xC,  0x72, 0x2E, 0x7B,
//      0xA6, 0xF7, 0x12, 0x88, 0x2F, 0x29, 0xB,  0xC7, 0x99, 0xF1, 0x1D, 0xBD,
//      0x13, 0x17, 0x33, 0x63, 0x5E, 0xF6, 0x0,  0x14, 0xEE, 0xE,  0x4F, 0xDC,
//      0xA7, 0xD0, 0x15, 0xAA, 0xCB, 0x7B, 0x8E, 0xB5, 0x34, 0x64, 0x84, 0x7A,
//      0x46, 0x98, 0xBD, 0xAA, 0x86, 0x3F, 0xD4, 0xD8, 0x3A, 0xE6, 0xA6, 0xBE,
//      0xFF, 0xEF, 0xCD, 0xC,  0x17, 0x32, 0x72, 0xD7, 0xF9, 0x1B, 0xAC, 0xC3,
//      0x7E, 0xF3, 0x58, 0x78, 0x9B, 0x5,  0x76, 0xF0, 0xEB, 0x32, 0xC3, 0xEC,
//      0xF,  0xF0, 0x51, 0x86, 0x83, 0xD9, 0x97, 0x1E, 0x7A, 0x3F, 0x96, 0x4D,
//      0x1E, 0x91, 0x5D, 0x32, 0x39, 0x97, 0x26, 0xD6, 0x5B, 0xDF, 0xA3, 0x6E,
//      0x94, 0x93, 0x18, 0x7D, 0x49, 0x71, 0xAE, 0x59, 0x47, 0x6C, 0x51, 0xC2,
//      0x36, 0xBB, 0xA9, 0x51, 0xE4, 0x89, 0x96, 0xA0, 0xAA, 0xA4, 0x11, 0xA1,
//      0x37, 0xC,  0x16, 0x39, 0x2B, 0x63, 0xD4, 0x9,  0x3,  0xD7, 0x99, 0xF2,
//      0x4B, 0x14, 0x4C, 0xC9, 0x6B, 0x5B, 0xA7, 0x6,  0x1C, 0x1B, 0xD4, 0x4A,
//      0x58, 0xE6, 0x78, 0x36, 0x7B, 0x35, 0xDF, 0xDA, 0xA4, 0x8A, 0x1F, 0x82,
//      0x41, 0xEF, 0xD8, 0x67, 0xFC, 0xE,  0xE1, 0x47, 0xD5, 0x1A, 0x7B, 0xC7,
//      0xEB, 0x1F, 0x19, 0x46, 0x17, 0xF8, 0x40, 0x3,  0xE6, 0xEA, 0xDD, 0x49,
//      0xF0, 0x9E, 0x7,  0x70, 0x2F, 0x28, 0x55, 0x70, 0xC1, 0xDB, 0x66, 0x31,
//      0xB6, 0xF7, 0x8E, 0x81, 0xCA, 0xDC, 0xCA, 0xE3, 0xD,  0x23, 0xBE, 0x7,
//      0xAA, 0xF1, 0xB3, 0xB,  0x28, 0xDB, 0xB0, 0xF,  0x29, 0xA,  0x79, 0x35,
//      0x99, 0xFD, 0x7,  0x83, 0x8D, 0xB,  0xF0, 0xD1, 0x79, 0xCC, 0x23, 0xF5,
//      0x9E, 0xD0, 0xFA, 0xC4, 0xC4, 0x97, 0xDF, 0x47, 0x1,  0x6C, 0x36, 0x43,
//      0x98, 0x8A, 0xDE, 0x83, 0xBB, 0xF6, 0x76, 0x2E, 0x57, 0xAF, 0x11, 0x6B,
//      0x0,  0x78, 0x88, 0x33, 0xD9, 0xEF, 0xDB, 0x3C, 0x5A, 0xCC, 0x2A, 0x29,
//      0x71, 0xA9, 0xD6, 0xEB, 0xE3, 0xC3, 0xDA, 0xFE, 0xD,  0x6B, 0xD0, 0x41,
//      0x5,  0x4F, 0x33, 0xD,  0x34, 0x64, 0x73, 0x9,  0x17, 0x40, 0x34, 0x1F,
//      0x67, 0x7A, 0xBD, 0xD9, 0x70, 0x64, 0x72, 0xD,  0xA7, 0xFC, 0xA3, 0x3,
//      0xAF, 0xD0, 0xDC, 0xF0, 0xAB, 0x65, 0xE8, 0xB8, 0x9B, 0xE9, 0xDF, 0x21,
//      0xA0, 0xDD, 0x6,  0xE4, 0xDD, 0x2F, 0xAE, 0x27, 0x9B, 0x44, 0x28, 0x9,
//      0x9B, 0x1D, 0x2F, 0x4A, 0x96, 0x8E, 0x35, 0xEB, 0x68, 0x87, 0xC6, 0x94,
//      0xED, 0xED, 0xC6, 0x48, 0xF4, 0x91, 0x70, 0x1B, 0x3F, 0xEA, 0x1E, 0x95,
//      0x8A, 0x9C, 0xB3, 0xB4, 0x2C, 0xF7, 0x78, 0x81, 0x99, 0x90, 0xE5, 0x86,
//      0xFD, 0xA6, 0x69, 0xD,  0xB9, 0x53, 0x39, 0x49, 0x43, 0x47, 0x4F, 0x91,
//      0x2B, 0xD1, 0x8D, 0xCD, 0x40, 0xDF, 0xDB, 0xA4, 0x14, 0xFB, 0x6C, 0x64,
//      0xFA, 0xEE, 0x1D, 0x82, 0x7B, 0xD7, 0x86, 0xE7, 0x6,  0xEB, 0xD8, 0xB9,
//      0x9B, 0x2A, 0x6B, 0x4,  0x53, 0x2,  0xA5, 0xF5, 0x82, 0xEA, 0x79, 0x59,
//      0x6,  0x7A, 0xEE, 0x60, 0x0,  0x80, 0x7A, 0x7F, 0xA0, 0x71, 0xC2, 0x5D,
//      0xB,  0x5D, 0xB5, 0x2B, 0xBD, 0xC9, 0xC5, 0xE3, 0x80, 0xB4, 0x39, 0xF8,
//      0x15, 0x1C, 0xDE, 0xA6, 0x9A, 0x60, 0xB6, 0xAA, 0x3,  0xBF, 0x19, 0x71,
//      0xD8, 0xD3, 0x7,  0x9,  0xE4, 0x70, 0x75, 0x35, 0x70, 0x63, 0x4D, 0x59,
//      0x6A, 0x47, 0x90, 0xE2, 0x1E, 0x1E, 0x7D, 0xA5, 0x55, 0x92, 0x32, 0x63,
//      0xC,  0xD1, 0x29, 0xBF, 0x37, 0x3A, 0xB8, 0xF8, 0x71, 0xB7, 0xE7, 0xE9,
//      0xD4, 0x13, 0x62, 0x35, 0x32, 0xC4, 0x59, 0x13, 0x7E, 0xF0, 0x34, 0x5,
//      0xC2, 0x77, 0xA1, 0xB0, 0x2,  0x8A, 0x25, 0x73, 0x32, 0x7B, 0x15, 0xE8,
//      0xE1, 0xF,  0x71, 0x7B, 0xA6, 0x11, 0xDF, 0x39, 0x2B, 0xB1, 0x55, 0x58,
//      0xE3, 0xDF, 0xFA, 0xA5, 0xCF, 0x81, 0x1F, 0xC5, 0x43, 0x3A, 0xC5, 0xA0,
//      0xEF, 0x1F, 0xD8, 0x72, 0x3E, 0xAD, 0xB,  0x8F, 0x22, 0xC0, 0xCB, 0x8C,
//      0xD3, 0x4A, 0x91, 0x1F, 0xF1, 0xC0, 0x88, 0xA2, 0x4B, 0x6F, 0x72, 0x97,
//      0x93, 0x14, 0xC6, 0x36, 0x57, 0x79, 0xF5, 0x1,  0x3D, 0xFB, 0x2,  0x8C,
//      0x21, 0xEF, 0xBF, 0xC5, 0x37, 0xD6, 0x80, 0x7,  0xD,  0x68, 0xE3, 0x4A,
//      0x6D, 0x55, 0x7C, 0xF9, 0xD7, 0x70, 0xA,  0xE5, 0xD5, 0xA9, 0xBA, 0xA1,
//      0x5E, 0xCB, 0x98, 0xF,  0x9D, 0x8B, 0x31, 0x4,  0xE3, 0x52, 0xD0, 0x3B,
//      0xE6, 0x56, 0xA6, 0xD6, 0xEE, 0x3D, 0xE0, 0xB,  0xBB, 0x5A, 0xA5, 0x73,
//      0x6D, 0xEA, 0x60, 0xCA, 0xC4, 0x46, 0x15, 0x12, 0x90, 0x8C, 0xB7, 0xBA,
//      0x75, 0xB,  0x75, 0xF5, 0x3C, 0xBA, 0x42, 0xA8, 0x7A, 0x70, 0xAC, 0x90,
//      0x51, 0x1,  0xCE, 0xFB, 0xB2, 0x40, 0xC4, 0xC3, 0x53, 0x3C, 0x35, 0xE6,
//      0x17, 0xEA, 0xC0, 0xD2, 0x78, 0x95, 0x9,  0x97, 0x5F, 0x87, 0x50, 0x60,
//      0x11, 0x7A, 0xA7, 0x67, 0x72, 0x81, 0xCB, 0x63, 0xE8, 0xD9, 0x26, 0xE5,
//      0x1,  0x5B, 0x46, 0xD,  0x5C, 0xA5, 0x5C, 0x3B, 0x18, 0xA,  0x77, 0x3D,
//      0x40, 0xEB, 0xCB, 0x44, 0x6F, 0x3,  0x74, 0x94, 0x6D, 0x96, 0xF3, 0x91,
//      0x9E, 0x16, 0x83, 0x39, 0xE1, 0x69, 0x5,  0xCB, 0x2B, 0xD7, 0x49, 0xAF,
//      0x8F, 0x4,  0x2E, 0xFD, 0xF2, 0x1B, 0x66, 0x8B, 0x06, 0x12, 0x80, 0x47,
//      0x60, 0xEF, 0xFA, 0xC0, 0xAF, 0x49, 0xEB, 0x23, 0xDD, 0x80, 0xE9, 0xDE,
//      0x32, 0x51, 0xD4, 0xD3, 0x8B, 0x2F, 0x78, 0x1B, 0x64, 0x3C, 0x22, 0x5D,
//      0x83, 0x28, 0xD8, 0xC2, 0x8D, 0xE0, 0xED, 0x4D, 0x20, 0xA8, 0x2A, 0xAA,
//      0xFC, 0xC1, 0x42, 0xD9, 0x80, 0x8A, 0xF3, 0xB6, 0x75, 0x55, 0x44, 0xE9,
//      0xAF, 0x32, 0xAF, 0x99, 0xF2, 0x51, 0xBF, 0x53, 0xEE, 0x81, 0xCA, 0xF9,
//      0x28, 0x4A, 0x32, 0x6B, 0xA5, 0x6,  0x4B, 0x63, 0x87, 0xC7, 0x9A, 0xD1,
//      0xE3, 0x67, 0x2C, 0x92, 0xBE, 0x57, 0x6F, 0xAF, 0x68, 0x8E, 0x4B, 0xBC,
//      0x1B, 0xA,  0x79, 0xB5, 0xF9, 0xFE, 0x3F, 0x51, 0x18, 0xD1, 0x79, 0x91,
//      0xDC, 0x9,  0x5D, 0xFE, 0x3B, 0xC0, 0xF0, 0xD0, 0x32, 0x6E, 0x5E, 0xA9,
//      0x65, 0x50, 0x14, 0x19, 0xCB, 0x3C, 0x74, 0xDE, 0x2C, 0xD9, 0x9,  0x1,
//      0x70, 0xD0, 0xF5, 0x5F, 0x4C, 0xFC, 0x4B, 0x8F, 0x5F, 0x94, 0xE6, 0x79,
//      0x39, 0x9F, 0x36, 0x27, 0xD8, 0xC9, 0x21, 0x84, 0x79, 0x60, 0x6F, 0xE0,
//      0x87, 0x79, 0xE9, 0x5F, 0x42, 0x41, 0x9C, 0xF2, 0x41, 0x63, 0x39, 0x8A,
//      0x48, 0xF5, 0x4F, 0xD9, 0xEE, 0x67, 0x17, 0xA5, 0x14, 0xBD, 0xD4, 0x75,
//      0x78, 0xB4, 0xBD, 0x2,  0x8A, 0x5C, 0x19, 0x9E, 0xFF, 0x22, 0x3D, 0xBB,
//      0xAF, 0x88, 0x9F, 0xDB, 0xDD, 0x1A, 0x88, 0xD0, 0x65, 0xE8, 0x70, 0xEF,
//      0x75, 0x51, 0x62, 0x13, 0xEE, 0x4D, 0x9B, 0xBE, 0x54, 0xB,  0xE4, 0x99,
//      0xDC, 0x79, 0x28, 0x61, 0xF,  0x3D, 0xF7, 0x8D, 0x1B, 0x66, 0x28, 0x7E,
//      0x52, 0x60, 0x64, 0x6E, 0x3B, 0x63, 0xE,  0x6F, 0xBA, 0x71, 0x2E, 0x9C,
//      0x36, 0x38, 0xA8, 0xAF, 0x53, 0x4B, 0xAB, 0x50, 0x66, 0x76, 0x82, 0x5E,
//      0x71, 0x41, 0xF6, 0x9A, 0x2C, 0x96, 0x61, 0xC1, 0x4D, 0x51, 0xA8, 0x64,
//      0xED, 0x36, 0x6B, 0x5D, 0x96, 0x43, 0x61, 0x2F, 0xB,  0x55, 0x3E, 0x62,
//      0xB9, 0x62, 0x8C, 0x58, 0x7,  0xB5, 0xDF, 0xEE, 0xA,  0x1,  0x6D, 0x3F,
//      0xD2, 0x3C, 0xF1, 0x2,  0x62, 0x9B, 0x25, 0xBE, 0xC3, 0x9C, 0x62, 0x4E,
//      0x46, 0x9E, 0x4A, 0x37, 0xB5, 0x75, 0x79, 0xD1, 0x2B, 0x6E, 0xB7, 0x9,
//      0x20, 0xDE, 0xC5, 0x1E, 0x8C, 0x60, 0x9B, 0x26, 0x6B, 0x4E, 0xD5, 0x10,
//      0xC2, 0x4,  0x95, 0xB,  0x4,  0x87, 0xDC, 0x5D, 0x1C, 0xF4, 0x7D, 0x5B,
//      0xE1, 0x6E, 0xA7, 0x93, 0xE0, 0x4C, 0x67, 0x10, 0xAE, 0x9C, 0x70, 0x18,
//      0x42, 0x21, 0x76, 0x82, 0x51, 0xF4, 0xCE, 0x84, 0x77, 0x17, 0x3C, 0xC9,
//      0xF3, 0xB,  0x85, 0xDF, 0x6F, 0x85, 0xB0, 0xE,  0x8F, 0xC,  0x59, 0x12,
//      0x6E, 0xDB, 0xFD, 0xAA, 0x26, 0x5D, 0xAD, 0x67, 0x9,  0xDC, 0x9,  0x65,
//      0xD1, 0xE5, 0x11, 0x85, 0x85, 0x24, 0x7A, 0xE9, 0x9A, 0xB6, 0xA3, 0x6D,
//      0x64, 0xD2, 0xBF, 0x92, 0xDE, 0x17, 0x9,  0x72, 0x3,  0x19, 0xB3, 0xFD,
//      0xD9, 0xF3, 0xF2, 0x5E, 0x9A, 0x24, 0xC3, 0x0,  0xD9, 0xA9, 0xB4, 0x7D,
//      0xE,  0x29, 0x3,  0xF5, 0xC0, 0x96, 0x62, 0x4C, 0xD1, 0xB3, 0x96, 0xB2,
//      0xCD, 0x13, 0xBA, 0x1,  0x35, 0x44, 0x9,  0xAD, 0x23, 0x89, 0x86, 0x9F,
//      0x51, 0xD8, 0xF5, 0x24, 0xB9, 0x43, 0xDF, 0xC7, 0x9F, 0x54, 0x4F, 0xE0,
//      0x2D, 0x46, 0xEB, 0xCE, 0xCD, 0xCC, 0x5E, 0x7,  0xA4, 0x9F, 0xE4, 0x9,
//      0x78, 0x4E, 0xB6, 0xDD, 0x4E, 0xA6, 0x6,  0x46, 0xB0, 0x61, 0x0,  0x73,
//      0x0,  0x8A, 0x30, 0x8C, 0xD4, 0xEA, 0xCF, 0x9
      };


  init_ntt();
  no_rand = 1;

  for (int i = 0; i < 1000; i++) {

    randombytes(msg, KYBER_INDCPA_MSGBYTES);
    randombytes(coins, KYBER_INDCPA_MSGBYTES);


    // Alice generates a public key
    indcpa_keypair(pk, sk);
    // for (int i = 0; i < KYBER_INDCPA_SECRETKEYBYTES; ++i) {
    //   printf("%X ", sk[i]);
    // }
    // printf("\n");
    // exit(1);
    indcpa_enc(ct, msg, pk, coins);

    indcpa_dec(dec_msg, ct, sk);

    if (no_rand) {
      printf("msg:\n");
      for (int j = 0; j < KYBER_INDCPA_MSGBYTES; ++j)
        printf("%2X ", msg[j]);

      printf("\n dec_msg:\n");
      for (int j = 0; j < KYBER_INDCPA_MSGBYTES; ++j)
        printf("%2X ", dec_msg[j]);

      printf("\n");
    }

    // printf("ct:\n{");
    // printf("0x%X", ct[0]);
    // for (int j = 1; j < KYBER_INDCPA_BYTES; ++j)
    //   printf(", 0x%X", ct[j]);
    // printf("}\n\n");

    if (memcmp(msg, dec_msg, KYBER_INDCPA_MSGBYTES)) {
      fprintf(stderr, "\n[ERROR] decryption failed!\n");
      exit(1);
    }

    if (no_rand) {
//      assert(!memcmp(ct, ref_ct, KYBER_INDCPA_BYTES));
      no_rand = 0;
    }
  }
}

int main(void) {
  // test_keys();
  // test_invalid_sk_a();
  // test_invalid_ciphertext();
  test_cpapke();

  // printf("CRYPTO_SECRETKEYBYTES:  %d\n",CRYPTO_SECRETKEYBYTES);
  // printf("CRYPTO_PUBLICKEYBYTES:  %d\n",CRYPTO_PUBLICKEYBYTES);
  // printf("CRYPTO_CIPHERTEXTBYTES: %d\n",CRYPTO_CIPHERTEXTBYTES);

  return 0;
}
