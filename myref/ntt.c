#include <stdint.h>
#include <stdio.h>
#include <assert.h>
#include "params.h"
#include "ntt.h"
#include "reduce.h"

/* Code to generate zetas and zetas_inv used in the number-theoretic transform:*/

#define KYBER_ROOT_OF_UNITY 17

int16_t zetas[128];
int16_t zetas_inv[128];

static unsigned int bit_reverse(unsigned int num, unsigned int bits) {
    unsigned int reverse_num = 0;

    for (unsigned i = 0; i < bits; i++) {
        if (num & (1 << i))
            reverse_num |= (1 << ((bits - 1) - i));
    }

    return reverse_num;
}

void init_ntt() {
    unsigned int i, j, k;
    int16_t tmp[128];

    tmp[0] = 1;
    for (i = 1; i < 128; ++i)
        tmp[i] = full_reduce(tmp[i - 1] * KYBER_ROOT_OF_UNITY);

    for (i = 0; i < 128; ++i)
        zetas[i] = tmp[bit_reverse(i, 7)];

    k = 0;
    for (i = 64; i >= 1; i >>= 1)
        for (j = i; j < 2 * i; ++j)
            zetas_inv[k++] = full_reduce(-tmp[128 - bit_reverse(j, 7)]);

}

/*************************************************
* Name:        ntt
*
* Description: Inplace number-theoretic transform (NTT) in Rq
*              input is in standard order, output is in bitreversed order
*
* Arguments:   - int16_t r[256]: pointer to input/output vector of elements
*                                of Zq
**************************************************/
void ntt(int16_t r[256]) {
    int16_t rp_odds[128];
    int16_t rp_evens[128];
    for (int i = 0; i < 256; ++i) {
        if (i & 1)
            rp_odds[i / 2] = r[i];
        else
            rp_evens[i / 2] = r[i];
    }
    ntt_ct_ng(rp_evens, 0);
    ntt_ct_ng(rp_odds, 0);

//    unsigned int len, start, j, k;
//    int16_t t, zeta;
//
//    k = 1;
//    for (len = 128; len >= 2; len >>= 1) {
//        for (start = 0; start < 256; start = j + len) {
//            zeta = zetas[k++];
//            for (j = start; j < start + len; ++j) {
//                t = full_reduce(zeta * r[j + len]);
//                // if(len > 64){
//                //   printf("[ntt] (%5d, %5d) -> (%5d, %5d)\n", r[j],  r[j + len], r[j] + t,r[j] - t);
//                // }
//                r[j + len] = full_reduce(r[j] - t);
//                r[j] = full_reduce(r[j] + t);
//            }
//        }
//    }

    for (int i = 0; i < 256; ++i) {
        if (i & 1)
            r[i] = rp_odds[i / 2];
        else
            r[i] = rp_evens[i / 2];
    }
}
void ntt_ct_ng(int16_t r[128], uint8_t inv) {
    unsigned const n = 128;
    unsigned num_cycles =  0;
//    if (inv && !is_odd) {
//        printf("ntt_ct_ng.inv (even) input=\n");
//        for (int i = 0; i < n; i++) {
//            printf("%4d ", r[i]);
//            if (i % 32 == 31) {
//                printf("\n");
//            }
//        }
//        printf("\n");
//    }
    unsigned k;
    int16_t t0, t1, u0, u1, r0, r1;

    int16_t mem[n / 2][2];

    if (inv) {
        for (unsigned i = 0; i < n / 2; i++) {
            mem[i][0] = r[2 * i];
            mem[i][1] = r[2 * i + 1];
        }
    } else {
        for (unsigned i = 0; i < n / 2; i++) {
            mem[i][0] = r[i];
            mem[i][1] = r[i + n / 2];
        }
    }

    k = (!inv) ? 1 : 0;
    for (unsigned len = (!inv) ? (n / 2) : 2; 1 <= len && len <= n; len = (!inv) ? (len >> 1U) : (len << 1U)) {
        uint8_t last_len = (!inv) ? (len == 1) : (len == n);
        for (unsigned i = 0; i < n / 2; i += (last_len ? 2 : len) ) {
            for (unsigned j = 0; j < (last_len ? 1 : len / 2); j += 1) {
                unsigned j0 = j + i;
                unsigned j1 = j0 + (last_len ? 1 : len / 2);
                assert(0 <= j0 && j0 < n / 2);
                assert(j1 < n / 2);
                assert(j0 < j1);

                t0 = mem[j0][0];
                u0 = mem[j0][1];
                t1 = mem[j1][0];
                u1 = mem[j1][1];

                assert(k < 128);
                int16_t w0 = (!inv) ? zetas[k] : zetas_inv[k];
                r0 = (!inv) ? barrett_reduce((int32_t) w0 * u0) : barrett_reduce((int32_t) w0 * (t0 - u0));
                int16_t w1 = (!inv) ? zetas[last_len ? k | 1 : k] : zetas_inv[last_len ? k : k | 1];
                r1 = (!inv) ? barrett_reduce((int32_t) w1 * u1) : barrett_reduce((int32_t) w1 * (t1 - u1));

                int16_t f0 = csubq(((!inv) ? r0 : u0) + t0 );
                int16_t f1 = csubq(((!inv) ? r1 : u1) + t1 );
                int16_t g0 = (!inv) ? (t0 - r0) : r0;
                int16_t g1 = (!inv) ? (t1 - r1) : r1;


                mem[j0][0] = f0;
                mem[j0][1] = (!last_len) ? f1 : g0;
                mem[j1][0] = (!last_len) ? g0 : f1;
                mem[j1][1] = g1;
                num_cycles++;
            }
            if (inv ^ last_len)
                k += 2;
            if (!inv && !last_len) // else
                k += 1;
            // if (inv && last_len) do nothing
        }
    }

    if (inv) {
        for (unsigned i = 0; i < n / 2; i++) {
            r[i] = mem[i][0];
            r[i + n / 2] = mem[i][1];
        }
    } else {
        for (unsigned i = 0; i < n / 2; i++) {
            r[2 * i] = mem[i][0];
            r[2 * i + 1] = mem[i][1];
        }
    }
//    printf("%s %d cycles\n", !inv?"fwd":"inv", num_cycles);
}

/*************************************************
* Name:        invntt
*
* Description: Inplace inverse number-theoretic transform in Rq
*              Input is in bit-reversed order, output is in standard order
*
* Arguments:   - int16_t r[256]: pointer to input/output vector of elements
*                                of Zq
**************************************************/

void invntt(int16_t r[256]) {
    unsigned int start, len, j, k;
    int16_t t, zeta;

    // scaling can be done either at the beginning .. or

    int16_t rp_odds[128];
    int16_t rp_evens[128];
    for (unsigned i = 0; i < 256; ++i) {
        if (i & 1U)
            rp_odds[i / 2] = r[i];
        else
            rp_evens[i / 2] = r[i];
    }
    ntt_ct_ng(rp_evens, 1);
    ntt_ct_ng(rp_odds, 1);

//    k = 0;
//    for (len = 2; len <= 128; len <<= 1U) {
//        for (start = 0; start < 256; start = j + len) {
//            zeta = zetas_inv[k];
//            for (j = start; j < start + len; ++j) {
//                t = r[j];
//                uint16_t o1 = full_reduce(t + r[j + len]);
//                uint16_t o2 = full_reduce((int32_t) zeta * (t - r[j + len]));
//                r[j] = o1;
//                r[j + len] = o2;
//            }
//            k += 1;
//        }
//    }

    // ... the end (here)
    // tt] ( 2766,   258) -> (   44,  2159)

//    printf("rp:\n");
//    for (int i = 0; i < 256; ++i) {
//        if (i & 1)
//            printf("%4d ", rp_odds[i / 2]);
//        else
//            printf("%4d ", rp_evens[i / 2]);
//    }
//    printf("\nr:\n");
//    for (int i = 0; i < 256; ++i) {
//        printf("%4d ", r[i]);
//    }
//    printf("\n\n");

//    for (unsigned i = 0; i < 256; ++i) {
//        if (i & 1)
//            assert(rp_odds[i / 2] == r[i]);
//        else
//            assert(rp_evens[i / 2] == r[i]);
//    }
    for (int i = 0; i < 256; ++i) {
        if (i & 1)
            r[i] = rp_odds[i / 2];
        else
            r[i] = rp_evens[i / 2];
    }
}

/*************************************************
* Name:        basemul
*
* Description: Multiplication of polynomials in Zq[X]/(X^2-zeta)
*              used for multiplication of elements in Rq in NTT domain
*
* Arguments:   - int16_t r[2]:       pointer to the output polynomial
*              - const int16_t a[2]: pointer to the first factor
*              - const int16_t b[2]: pointer to the second factor
*              - int16_t zeta:       integer defining the reduction polynomial
**************************************************/
void basemac(int16_t r[2],
             const int16_t a[2],
             const int16_t b[2],
             int16_t zeta) {

    // phase 1: N / 4 cycles
    r[0] = csubq(barrett_reduce((int32_t) a[0] * b[0]) + r[0]);

    // phase 2: N / 2 cycles
    int16_t top = barrett_reduce((int32_t) a[1] * b[1]);
    r[0] = csubq(barrett_reduce((int32_t) top * zeta) +  r[0]);

    // phase 3: N / 4 cycles
    r[1] = csubq(barrett_reduce((int32_t) a[1] * b[0]) + r[1]);
    // phase 4: N / 4 cycles
    r[1] = csubq(barrett_reduce((int32_t) a[0] * b[1]) + r[1]);
}
