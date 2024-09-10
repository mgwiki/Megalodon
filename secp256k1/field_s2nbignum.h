#ifndef SECP256K1_FIELD_REPR_H
#define SECP256K1_FIELD_REPR_H

#include <stdint.h>

#include "s2n-bignum.h"

/* ****************************************************************************
 * This is the core datatype for internal and storage. In our case they
 * are both the same, just s2n-bignum 4-digit bignums wrapped in a struct.
 * Also we always maintain normalization as per usual s2n-bignum setting.
 * That means we can mostly ignore the distinction between normalized and
 * unnormalized except when mapping into the format.
 *****************************************************************************/

typedef struct
{ uint64_t d[4];
#ifdef VERIFY
    int magnitude;
    int normalized;
#endif
 } secp256k1_fe;

#define SECP256K1_FE_CONST_INNER(d7, d6, d5, d4, d3, d2, d1, d0) { \
    (d0) | (((uint64_t)(d1)) << 32), \
    (d2) | (((uint64_t)(d3)) << 32), \
    (d4) | (((uint64_t)(d5)) << 32), \
    (d6) | (((uint64_t)(d7)) << 32) \
}

#ifdef VERIFY
#define SECP256K1_FE_CONST(d7, d6, d5, d4, d3, d2, d1, d0) {SECP256K1_FE_CONST_INNER((d7), (d6), (d5), (d4), (d3), (d2), (d1), (d0)), 1, 1}
#else
#define SECP256K1_FE_CONST(d7, d6, d5, d4, d3, d2, d1, d0) {SECP256K1_FE_CONST_INNER((d7), (d6), (d5), (d4), (d3), (d2), (d1), (d0))}
#endif

typedef struct { uint64_t d[4]; } secp256k1_fe_storage;

#define SECP256K1_FE_STORAGE_CONST(d7, d6, d5, d4, d3, d2, d1, d0) {{ \
    (d0) | (((uint64_t)(d1)) << 32), \
    (d2) | (((uint64_t)(d3)) << 32), \
    (d4) | (((uint64_t)(d5)) << 32), \
    (d6) | (((uint64_t)(d7)) << 32) \
}}

#define SECP256K1_FE_STORAGE_CONST_GET(x) \
    (uint32_t)((x).d[3] >> 32), (uint32_t)(x).d[3], \
    (uint32_t)((x).d[2] >> 32), (uint32_t)(x).d[2], \
    (uint32_t)((x).d[1] >> 32), (uint32_t)(x).d[1], \
    (uint32_t)((x).d[0] >> 32), (uint32_t)(x).d[0]

#endif /* SECP256K1_FIELD_REPR_H */
