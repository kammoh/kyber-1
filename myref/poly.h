#ifndef POLY_H
#define POLY_H

#include <stdint.h>
#include "params.h"

/*
 * Elements of R_q = Z_q[X]/(X^n + 1). Represents polynomial
 * coeffs[0] + X*coeffs[1] + X^2*xoeffs[2] + ... + X^{n-1}*coeffs[n-1]
 */
typedef struct{
  int16_t coeffs[KYBER_N];
} poly;

void scale_poly(poly *r);

void poly_compress(uint8_t r[KYBER_POLYCOMPRESSEDBYTES], poly *a);
void poly_decompress(poly *r, const uint8_t a[KYBER_POLYCOMPRESSEDBYTES]);

void poly_tobytes(uint8_t r[KYBER_POLYBYTES], poly *a);
void poly_frombytes(poly *r, const uint8_t a[KYBER_POLYBYTES]);

void poly_frommsg(poly *r, const uint8_t msg[KYBER_INDCPA_MSGBYTES]);
void poly_tomsg(uint8_t msg[KYBER_INDCPA_MSGBYTES], poly *r);

void poly_getnoise(poly *r, const uint8_t seed[KYBER_SYMBYTES], uint8_t nonce);

void poly_ntt(poly *r);
void poly_invntt(poly *r);

void poly_basemac(poly *r, const poly *a, const poly *b);

void poly_reduce(poly *r);
void poly_csubq(poly *r);

void poly_add(poly *r, const poly *a, const poly *b);
void poly_sub(poly *r, const poly *a, const poly *b);

#endif
