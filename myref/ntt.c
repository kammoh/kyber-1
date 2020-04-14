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
    ntt_ct_ng(rp_evens, 0, 0);
    ntt_ct_ng(rp_odds, 0, 1);

    unsigned int len, start, j, k;
    int16_t t, zeta;

    k = 1;
    for (len = 128; len >= 2; len >>= 1) {
        for (start = 0; start < 256; start = j + len) {
            zeta = zetas[k++];
            for (j = start; j < start + len; ++j) {
                t = barrett_reduce(zeta * r[j + len]);
                // if(len > 64){
                //   printf("[ntt] (%5d, %5d) -> (%5d, %5d)\n", r[j],  r[j + len], r[j] + t,r[j] - t);
                // }
                r[j + len] = full_reduce(r[j] - t);
                r[j] = full_reduce(r[j] + t);
            }
        }
    }

    for (int i = 0; i < 256; ++i) {
        if (i & 1)
            assert(rp_odds[i / 2] == r[i]);
        else
            assert(rp_evens[i / 2] == r[i]);
    }
}
const int m_level = 1;
#define mm1 ( (!inv) ? m==1 ? 1 : (m / 2) : m )
void ntt_ct_ng(int16_t r[128], uint8_t inv, uint8_t is_odd) {
    unsigned const n = 128;
    if (inv && !is_odd) {
        printf("ntt_ct_ng.inv (even) input=\n");
        for (int i = 0; i < n; i++) {
            printf("%4d ", r[i]);
            if (i % 32 == 31) {
                printf("\n");
            }
        }
        printf("\n");
    }
    unsigned i, j, k, m;
    unsigned n1 = (!inv) ? n : (n / 4);
    int16_t t1, t2, u1, u2, r1, r2;

    int16_t mem[n / 2][2];

    if (inv) {
        for (i = 0; i < n / 4; i++) {
            mem[2 * i][0] = r[4 * i];
            mem[2 * i][1] = r[4 * i + 2];
            mem[2 * i + 1][0] = r[4 * i + 1];
            mem[2 * i + 1][1] = r[4 * i + 3];
        }
//    for (int i = 0; i < n / 2; i++) {
//      mem[i][0] = r[2 * i];
//      mem[i][1] = r[2 * i + 1];
//    }
    } else {
        for (int i = 0; i < n / 2; i++) {
            mem[i][0] = r[i];
            mem[i][1] = r[i + n / 2];
        }
    }

    if (inv) { // m = 1
        m = 1;
        k = 0;

        printf("zeta_invs @ct-ng.inv.pre\n");
        for (int kk = 0; kk < 128; kk++) {
            printf("%5d ", zetas_inv[kk]);
        }
        printf("\n");
        for (j = 0; j < (n / 2); j = j + 2) {
            t1 = mem[j][0];
            u1 = mem[j + 1][0];
            t2 = mem[j][1];
            u2 = mem[j + 1][1];

            int16_t w = zetas_inv[k++];
            r1 = barrett_reduce((int32_t) w * (t1 - u1));

            w = zetas_inv[k++];
            r2 = barrett_reduce((int32_t) w * (t2 - u2));

//            uint16_t fwd_t1 = full_reduce(t1 + r1);
//            uint16_t fwd_t2 = full_reduce(t2 + r2);
//            uint16_t fwd_u1 = full_reduce(t1 - r1);
//            uint16_t fwd_u2 = full_reduce(t2 - r2);
            uint16_t inv_t1 = full_reduce(t1 + u1);
            uint16_t inv_t2 = full_reduce(t2 + u2);
            uint16_t inv_u1 = full_reduce(r1);
            uint16_t inv_u2 = full_reduce(r2);

            uint16_t inv_u1t2_1 = (m == 200) ? inv_u1 : inv_t2;
            uint16_t inv_u1t2_2 = (m == 200) ? inv_t2 : inv_u1;

            if (!is_odd) {
                printf(
                    "[ntt-ct-ng(inv)(pre)] (%5d,%5d(%2d) : %5d,%5d(%2d)) -> (%5d,%5d : %5d,%5d) "
                    "w=%4d,  k=%3d,  m=%2d,  j:%2d \n",
                    t1, u1, j, t2, u2, j + 1, inv_t1, inv_u1t2_1, inv_u1t2_2, inv_u2,
                    w, k, m, j
                );
            }

            mem[j][0] = inv_t1;
            mem[j][0] = inv_u1;
            mem[j + 1][1] = inv_t2;
            mem[j + 1][1] = inv_u2;

            //mem[i] = (a[i], a[i + m])25
            // k = (!inv) ? k + 1 : k;
        }
        printf("pre loop done\n");
    }

    k = (!inv) ? 1 : 0;
    for (m = (!inv) ? (n / 2) : 2; 1 <= m && m < n1; m = (!inv) ? (m >> 1) : (m << 1)) {
        for (i = 0; i < (n / 2); i = j + (m == 1 ? 1 : (m / 2))) { // TODO inc for inv
            int16_t w = (!inv) ? zetas[k++] : zetas_inv[k++];
            for (j = i; j < i + (m == 1 ? 1 : m / 2); j = j + 1) {
                unsigned j2 = j + (m == 1 ? 1 : m / 2);
                if (inv) {
                    printf("m=%d i=%d, j=%d j2=%d\n", m, i, j, j2);
                }
                assert(0 <= j && j < n / 2);
                assert(j2 < n / 2);
                t1 = mem[j][0];
                u1 = mem[j][!inv];

                t2 = mem[j2][inv];
                u2 = mem[j2][1];

                r1 = (!inv) ? barrett_reduce((int32_t) w * u1) : barrett_reduce((int32_t) w * (t1 - u1));
                if (m == 1) {
                    w = (!inv) ? zetas[k++] : zetas_inv[k++];
                    // printf("w=%d\n", w);
                }
                r2 = (!inv) ? barrett_reduce((int32_t) w * u2) : barrett_reduce((int32_t) w * (t2 - u2));

                uint16_t fwd_t1 = full_reduce(t1 + r1);
                uint16_t fwd_t2 = full_reduce(t2 + r2);
                uint16_t fwd_u1 = full_reduce(t1 - r1);
                uint16_t fwd_u2 = full_reduce(t2 - r2);
                uint16_t inv_t1 = full_reduce(t1 + u1);
                uint16_t inv_t2 = full_reduce(t2 + u2);
                uint16_t inv_u1 = full_reduce(r1);
                uint16_t inv_u2 = full_reduce(r2);

                uint16_t inv_u1t2_1 = (m == 200) ? inv_u1 : inv_t2;
                uint16_t inv_u1t2_2 = (m == 200) ? inv_t2 : inv_u1;

                if (inv && m == m_level && !is_odd) {
                    printf(
                        "[ntt-ct-ng(inv)] (%5d,%5d(%2d) : %5d,%5d(%2d)) -> (%5d,%5d : %5d,%5d) "
                        "w=%4d,  k=%3d,  m=%2d,  i=%2d,  mm1=%2d, j:%2d \n",
                        t1, u1, j, t2, u2, j2, inv_t1, inv_u1t2_1, inv_u1t2_2, inv_u2,
                        w, k, m, i, mm1, j
                    );
                }

                mem[j][0] = (!inv) ? fwd_t1 : inv_t1;
                mem[j][!inv] = (!inv) ? fwd_t2 : inv_u1t2_1;
                mem[j2][inv] = (!inv) ? fwd_u1 : inv_u1t2_2;
                mem[j2][1] = (!inv) ? fwd_u2 : inv_u2;
            }
        }
    }
    printf("\n---\n\n");
    // for(unsigned j = 0; j < (n/2); j = j + 2){
    //   t1 = mem[j][0];
    //   u1 = mem[j][1];
    //   t2 = mem[j + 1][0];
    //   u2 = mem[j + 1][1];

    //   w = zetas[k++];
    //   r1 = (!inv) ? barrett_reduce((int32_t)w * u1): barrett_reduce((int32_t)w * (t1 - u1));

    //   w = zetas[k++];
    //   r2 = (!inv) ? barrett_reduce((int32_t)w * u2) : barrett_reduce((int32_t)w * (t2 - u2));

    //   mem[j][0] = (!inv) ? full_reduce(t1 + r1) : full_reduce(t1 + u1);
    //   mem[j][1] = (!inv) ? full_reduce(t1 - r1) : full_reduce(r1);
    //   mem[j + 1][0] = (!inv) ? full_reduce(t2 + r2) : full_reduce(t2 + u2);
    //   mem[j + 1][1] = (!inv) ? full_reduce(t2 - r2) : full_reduce(r2);

    //   //mem[i] = (a[i], a[i + m])25
    //   // k = (!inv) ? k + 1 : k;
    // }

    if (inv) {
        for (i = 0; i < n / 2; i++) {
            r[i] = mem[i][0];
            r[i + n / 2] = mem[i][1];
        }
    } else {
        for (i = 0; i < n / 4; i++) {
            r[4 * i] = mem[2 * i][0];
            r[4 * i + 2] = mem[2 * i][1];
            r[4 * i + 1] = mem[2 * i + 1][0];
            r[4 * i + 3] = mem[2 * i + 1][1];
        }
    }
    printf("\n>>---\n\n");
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

//    int16_t rp_odds[128];
//    int16_t rp_evens[128];
//    for (int i = 0; i < 256; ++i) {
//        if (i & 1)
//            rp_odds[i / 2] = r[i];
//        else
//            rp_evens[i / 2] = r[i];
//    }
//    ntt_ct_ng(rp_evens, 1, 0);
//    ntt_ct_ng(rp_odds, 1, 1);

    k = 0;
    for (len = 2; len <= 128; len <<= 1) {
        for (start = 0; start < 256; start = j + len) {
            zeta = zetas_inv[k++];
            for (j = start; j < start + len; ++j) {
                t = r[j];
                uint16_t o1 = full_reduce(t + r[j + len]);
                uint16_t o2 = full_reduce((int32_t) zeta * (t - r[j + len]));
                if (1) {
                    printf("[invntt] (%5d, %5d) -> (%5d, %5d) zeta=%4d k=%2d, len=%2d, start=%2d, j=%2d \n",
                           r[j], r[j + len], o1, o2, zeta, k, len, start, j);
                }
                r[j] = o1;
                r[j + len] = o2;
            }
        }
    }

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

//    for (int i = 0; i < 256; ++i) {
//        if (i & 1)
//            assert(rp_odds[i / 2] == r[i]);
//        else
//            assert(rp_evens[i / 2] == r[i]);
//    }

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
    r[0] = barrett_reduce((int64_t) a[1] * b[1]);
    r[0] = barrett_reduce((int64_t) r[0] * zeta) + barrett_reduce((int64_t) a[0] * b[0]);

    r[1] = barrett_reduce((int64_t) a[0] * b[1]) + barrett_reduce((int64_t) a[1] * b[0]);
}
