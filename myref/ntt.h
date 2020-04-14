#ifndef NTT_H
#define NTT_H

#include <stdint.h>
#include "params.h"

#define max(a,b)             \
({                           \
    __typeof__ (a) _a = (a); \
    __typeof__ (b) _b = (b); \
    _a > _b ? _a : _b;       \
})

#define min(a,b)             \
({                           \
    __typeof__ (a) _a = (a); \
    __typeof__ (b) _b = (b); \
    _a < _b ? _a : _b;       \
})

#define N_INV 3303 // (KYBER_N/2=) 128^-1 mod KYBER_Q
void ntt_ct_ng(int16_t r[256], uint8_t inv, uint8_t is_odd);

#define zetas KYBER_NAMESPACE(zetas)
extern int16_t zetas[128];

#define zetas_inv KYBER_NAMESPACE(zetas_inv)
extern int16_t zetas_inv[128];

#define ntt KYBER_NAMESPACE(ntt)
void ntt(int16_t poly[256]);

#define invntt KYBER_NAMESPACE(invntt)
void invntt(int16_t poly[256]);

#define basemul KYBER_NAMESPACE(basemul)
void basemul(int16_t r[2],
             const int16_t a[2],
             const int16_t b[2],
             int16_t zeta);

#define init_ntt KYBER_NAMESPACE(init_ntt)
void init_ntt(void);

#endif
