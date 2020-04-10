#ifndef NTT_H
#define NTT_H

#include <stdint.h>
#include "params.h"

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
