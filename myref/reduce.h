#ifndef REDUCE_H
#define REDUCE_H

#include <stdint.h>
#include "params.h"

// #define MONT 2285 // 2^16 mod q
#define MONT_INV 169 // MONT^-1 mod q
// #define QINV 62209 // q^-1 mod 2^16

// #define montgomery_reduce KYBER_NAMESPACE(montgomery_reduce)
// int16_t montgomery_reduce(int32_t a);

#define barrett_reduce KYBER_NAMESPACE(barrett_reduce)
int16_t barrett_reduce(int16_t a);

#define csubq KYBER_NAMESPACE(csubq)
int16_t csubq(int16_t x);

int16_t full_reduce(int64_t a);

#endif