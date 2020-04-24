#include <stdint.h>
#include <stdio.h>
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
int16_t full_reduce(int32_t a) {
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
int16_t barrett_reduce(int32_t u) {
//    assert(u>=0);

    int16_t alpha = 13;
    int16_t n = 12;
    int16_t beta = -1;
    const int32_t m = (1<< (n+alpha)) / KYBER_Q;

    int32_t uh = (u >> (n+beta));
    int32_t ul = u;
    int32_t q_hat = (((int32_t)m * uh) >> (alpha - beta));
    int32_t q_hat_times_Q = (q_hat * KYBER_Q); // WHY??? we only need 13 bits right?


    int16_t r_hat = (u - q_hat_times_Q);

//    int32_t r_hat_minus_M = r_hat - KYBER_Q;
//if(r_hat & (1U << 13)){
//    printf("was neg:%d\n", r_hat);
//    r_hat = (r_hat + (1U << 14)) & ((1U << 12) - 1);
//    printf("now:%d\n", r_hat);
//}
    if(r_hat < 0){
        r_hat += KYBER_Q;
    }
//    else if (r_hat > KYBER_Q) {
//        r_hat -= KYBER_Q;
//    }
//    r_hat = r_hat & ((1<<13) - 1);

    int16_t full_red = full_reduce(u);
//    printf("m=%d u=%X(%d) uh=%X ul=%X,q_hat=%X q_hat_times_M=%X r_hat=%X(%d), full_red=%X(%d)\n", m, u, u, uh, ul,
//        q_hat, q_hat_times_Q, r_hat, r_hat, full_red, full_red);
    assert (r_hat >= 0);
//    assert (r_hat == full_red || (r_hat == full_red + KYBER_Q));
    return (r_hat);
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

int16_t csub2q(int16_t a) {
    if(a >= (2 * KYBER_Q))
        return a - 2 * KYBER_Q;
    if(a >= KYBER_Q)
        return a - KYBER_Q;
    return a;
}

int16_t caddq(int16_t a) {
    a += (a >> 15) & KYBER_Q;
    return a;
}