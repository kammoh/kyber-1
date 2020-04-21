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
    int16_t t1, t2, u1, u2, r1, r2;

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
                unsigned j1 = j + i;
                unsigned j2 = j1 + (last_len ? 1 : len / 2);
                assert(0 <= j1 && j1 < n / 2);
                assert(j2 < n / 2);
                assert(j1 < j2);

                t1 = mem[j1][0];
                u1 = mem[j1][1];
                t2 = mem[j2][0];
                u2 = mem[j2][1];

                assert(k < 128);
                int16_t w1 = (!inv) ? zetas[k] : zetas_inv[k];
                r1 = (!inv) ? barrett_reduce((int32_t) w1 * u1)   : barrett_reduce((int32_t) w1 * (t1 - u1));
                int16_t w2 = (!inv) ? zetas[last_len ? k | 1 : k] : zetas_inv[last_len ? k : k | 1];
                r2 = (!inv) ? barrett_reduce((int32_t) w2 * u2)   : barrett_reduce((int32_t) w2 * (t2 - u2));

                uint16_t fwd_t1 = csubq(t1 + r1);
                uint16_t fwd_t2 = csubq(t2 + r2);
                uint16_t fwd_u1 = (t1 - r1);
                uint16_t fwd_u2 = (t2 - r2);
                uint16_t inv_t1 = csubq(t1 + u1);
                uint16_t inv_t2 = csubq(t2 + u2);
                uint16_t inv_u1 = (r1);
                uint16_t inv_u2 = (r2);

                mem[j1][0] = (!inv) ? fwd_t1 : inv_t1;
                mem[j1][1] = (!inv) ? (last_len ? fwd_u1 : fwd_t2) : (last_len ? inv_u1 : inv_t2);
                mem[j2][0] = (!inv) ? (last_len ? fwd_t2 : fwd_u1) : (last_len ? inv_t2 : inv_u1);
                mem[j2][1] = (!inv) ? fwd_u2 : inv_u2;
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
void basemul(int16_t r[2],
             const int16_t a[2],
             const int16_t b[2],
             int16_t zeta) {
    r[0] = full_reduce((int64_t) a[1] * b[1]);
    r[0] = full_reduce((int64_t) r[0] * zeta) + full_reduce((int64_t) a[0] * b[0]);

    r[1] = full_reduce((int64_t) a[0] * b[1]) + full_reduce((int64_t) a[1] * b[0]);
}
