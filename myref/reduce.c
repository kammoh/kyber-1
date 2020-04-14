#include <stdint.h>
#include <assert.h>
#include "params.h"
#include "reduce.h"

/*************************************************
* Name:        montgomery_reduce
*
* Description: Montgomery reduction; given a 32-bit integer a, computes
*              16-bit integer congruent to a * R^-1 mod q,
*              where R=2^16
*
* Arguments:   - int32_t a: input integer to be reduced;
*                           has to be in {-q2^15,...,q2^15-1}
*
* Returns:     integer in {-q+1,...,q-1} congruent to a * R^-1 modulo q.
**************************************************/
int16_t full_reduce(int64_t a){
  return ((a % KYBER_Q) + KYBER_Q) % KYBER_Q;
}

// int16_t montgomery_reduce(int32_t a)
// {
//   // int32_t t;
//   // int16_t u;

//   // u = a*QINV;
//   // t = (int32_t)u*KYBER_Q;
//   // t = a - t;
//   // t >>= 16;
//   // // return t;
//   // assert(full_reduce(t * MONT) == full_reduce(a));
//   return full_reduce((int64_t)a * MONT_INV);
// }

/*************************************************
* Name:        barrett_reduce
*
* Description: Barrett reduction; given a 16-bit integer a, computes
*              16-bit integer congruent to a mod q in {0,...,q}
*
* Arguments:   - int16_t a: input integer to be reduced
*
* Returns:     integer in {0,...,q} congruent to a modulo q.
**************************************************/
#include <assert.h>
int16_t barrett_reduce(int32_t u){
  const int32_t q_inv = 5039;

  uint16_t uh = ((uint32_t)u) >> 10;
  uint16_t ul = ((uint32_t)u) & ((1 << 13) - 1);
  uint16_t q_hat = (q_inv * uh) & ((1 << 13) - 1);
  uint32_t q_hat_times_M = (q_hat * KYBER_Q) & ((1L << 25) - 1); // WHY??? we only need 13 bits right?

  // printf("%X\n", q_hat_times_M);

  int32_t r_hat = (ul - q_hat_times_M);

  // int32_t r_hat_minus_M = r_hat - KYBER_Q;

  // int16_t t;
  // const int16_t v = ((1U << 26) + KYBER_Q/2)/KYBER_Q;

  // t  = (int32_t)v*a >> 26;
  // t *= KYBER_Q;
  // return a - t;
  // assert (r_hat > 0);
  return full_reduce(u);
}

/*************************************************
 * Name:        csubq
 *
 * Description: Conditionallly subtract q
 *
 * Arguments:   - int16_t x: input integer
 *
 * Returns:     a - q if a >= q, else a
 **************************************************/
int16_t csubq(int16_t a) {
  a -= KYBER_Q;
  a += (a >> 15) & KYBER_Q;
  return a;
}
