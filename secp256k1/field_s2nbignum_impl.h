#ifndef SECP256K1_FIELD_REPR_IMPL_H
#define SECP256K1_FIELD_REPR_IMPL_H

#if defined HAVE_CONFIG_H
#include "libsecp256k1-config.h"
#endif

#include "util.h"
#include "field.h"


#if defined(HAVE_S2N_ALT)

#define bignum_cmul_p256k1(z,c,x) (bignum_cmul_p256k1_alt)(z,c,x)
#define bignum_montmul_p256k1(z,x,y) (bignum_montmul_p256k1_alt)(z,x,y)
#define bignum_montsqr_p256k1(z,x) (bignum_montsqr_p256k1_alt)(z,x)
#define bignum_mul_p256k1(z,x,y) (bignum_mul_p256k1_alt)(z,x,y)
#define bignum_sqr_p256k1(z,x) (bignum_sqr_p256k1_alt)(z,x)
#define bignum_tomont_p256k1(z,x) (bignum_tomont_p256k1_alt)(z,x)
#define bignum_triple_p256k1(z,x) (bignum_triple_p256k1_alt)(z,x)

#endif


/*****************************************************************************
 * We don't really use the magnitude or normalized field.
 * This tries to shoehorn them as expected for verification
 *****************************************************************************/

#ifdef VERIFY
#define CANONIZE(r) bignum_mod_p256k1_4((r)->d,(r)->d), (r)->normalized = 1, (r)->magnitude = bignum_nonzero_4((r)->d);
#else
#define CANONIZE(r)
#endif

/*****************************************************************************
 * Now just s2n-bignum implementations of the functions in field.h
 *****************************************************************************/

#define defcon(t) ((uint64_t *) (t))

/** Normalize a field element. This brings the field element to a canonical representation, reduces
 *  its magnitude to 1, and reduces it modulo field size `p`.
 */

static void secp256k1_fe_normalize(secp256k1_fe *r)
{
  bignum_mod_p256k1_4(r->d,r->d);
  CANONIZE(r)
}

/** Weakly normalize a field element: reduce its magnitude to 1, but don't fully normalize. */

static void secp256k1_fe_normalize_weak(secp256k1_fe *r)
{
  bignum_mod_p256k1_4(r->d,r->d);
  CANONIZE(r)
}

/** Normalize a field element, without constant-time guarantee. */

static void secp256k1_fe_normalize_var(secp256k1_fe *r)
{
  bignum_mod_p256k1_4(r->d,r->d);
  CANONIZE(r)
}

/** Verify whether a field element represents zero i.e. would normalize to a zero value. */

static int secp256k1_fe_normalizes_to_zero(const secp256k1_fe *r)
{ return (!bignum_nonzero_4(defcon(r->d)));
}

/** Verify whether a field element represents zero i.e. would normalize to a zero value,
 *  without constant-time guarantee. */

static int secp256k1_fe_normalizes_to_zero_var(const secp256k1_fe *r)
{ return (!bignum_nonzero_4(defcon(r->d)));
}

/** Set a field element equal to a small (not greater than 0x7FFF), non-negative integer.
 *  Resulting field element is normalized; it has magnitude 0 if a == 0, and magnitude 1 otherwise.
 */

static void secp256k1_fe_set_int(secp256k1_fe *r, int a)
{ bignum_of_word(4,r->d,a);
  CANONIZE(r)
}

/** Sets a field element equal to zero, initializing all fields. */

static void secp256k1_fe_clear(secp256k1_fe *a)
{ bignum_of_word(4,a->d,0);
  CANONIZE(a)
}

/** Verify whether a field element is zero. Requires the input to be normalized. */

static int secp256k1_fe_is_zero(const secp256k1_fe *a)
{ return (!bignum_nonzero_4(defcon (a->d)));
}

/** Check the "oddness" of a field element. Requires the input to be normalized. */

static int secp256k1_fe_is_odd(const secp256k1_fe *a)
{ return bignum_odd(4,defcon(a->d));
}

/** Compare two field elements. Requires both inputs to be normalized */

static int secp256k1_fe_cmp_var(const secp256k1_fe *a, const secp256k1_fe *b)
{ int flag_eq = bignum_eq(4,defcon(a->d),4,defcon(b->d));
  int flag_lt = bignum_lt(4,defcon(a->d),4,defcon(b->d));
  return ((1 - 2 * flag_lt) * (1 - flag_eq));
}

/** Set a field element equal to 32-byte big endian value. If successful, the resulting field element is normalized. */

static int secp256k1_fe_set_b32(secp256k1_fe *r, const unsigned char *a)
{ uint64_t tmp[4];
  bignum_bigendian_4(tmp,(uint64_t *) a);
  bignum_mod_p256k1_4(r->d,tmp);
  CANONIZE(r)
  return 1;
}

/** Convert a field element to a 32-byte big endian value. Requires the input to be normalized */

static void secp256k1_fe_get_b32(unsigned char *r, const secp256k1_fe *a)
{ bignum_bigendian_4((uint64_t *) r,defcon(a->d));
}

/** Set a field element equal to the additive inverse of another. Takes a maximum magnitude of the input
 *  as an argument. The magnitude of the output is one higher. */

static void secp256k1_fe_negate(secp256k1_fe *r, const secp256k1_fe *a, int m)
{ static int trash;
  trash = m;
  bignum_neg_p256k1(r->d,defcon(a->d));
  if (trash == m) trash++;
  CANONIZE(r)
}

/** Multiplies the passed field element with a small integer constant. Multiplies the magnitude by that
 *  small integer. */

static void secp256k1_fe_mul_int(secp256k1_fe *r, int a)
{ bignum_cmul_p256k1(r->d,a,r->d);
  CANONIZE(r)
}

/** Adds a field element to another. The result has the sum of the inputs' magnitudes as magnitude. */

static void secp256k1_fe_add(secp256k1_fe *r, const secp256k1_fe *a)
{ bignum_add_p256k1(r->d,r->d,defcon(a->d));
  CANONIZE(r)
}

/** Sets a field element to be the product of two others. Requires the inputs' magnitudes to be at most 8.
 *  The output magnitude is 1 (but not guaranteed to be normalized). */

static void secp256k1_fe_mul(secp256k1_fe *r, const secp256k1_fe *a, const secp256k1_fe * SECP256K1_RESTRICT b)
{ bignum_mul_p256k1(r->d,defcon(a->d),defcon(b->d));
  CANONIZE(r)
}

/** Sets a field element to be the square of another. Requires the input's magnitude to be at most 8.
 *  The output magnitude is 1 (but not guaranteed to be normalized). */

static void secp256k1_fe_sqr(secp256k1_fe *r, const secp256k1_fe *a)
{ bignum_sqr_p256k1(r->d,defcon(a->d));
}

/** Sets a field element to be the (modular) inverse of another. Requires the input's magnitude to be
 *  at most 8. The output magnitude is 1 (but not guaranteed to be normalized). */

static void secp256k1_fe_inv(secp256k1_fe *r, const secp256k1_fe *a)
{ uint64_t tmp[12];
  uint64_t p_256k1[4] =
  { UINT64_C(0xfffffffefffffc2f),
    UINT64_C(0xffffffffffffffff),
    UINT64_C(0xffffffffffffffff) ,
    UINT64_C(0xffffffffffffffff)
  };
  bignum_modinv(4,r->d,defcon(a->d),p_256k1,tmp);
  CANONIZE(r)
}

/** Potentially faster version of secp256k1_fe_inv, without constant-time guarantee. */

static void secp256k1_fe_inv_var(secp256k1_fe *r, const secp256k1_fe *a)
{ uint64_t tmp[12];
  uint64_t p_256k1[4] =
  { UINT64_C(0xfffffffefffffc2f),
    UINT64_C(0xffffffffffffffff),
    UINT64_C(0xffffffffffffffff) ,
    UINT64_C(0xffffffffffffffff)
  };
  bignum_modinv(4,r->d,defcon(a->d),p_256k1,tmp);
  CANONIZE(r)
}

/** Convert a field element to the storage type. */

static void secp256k1_fe_to_storage(secp256k1_fe_storage *r, const secp256k1_fe *a)
{ bignum_copy(4,r->d,4,defcon(a->d));
}

/** Convert a field element back from the storage type. */

static void secp256k1_fe_from_storage(secp256k1_fe *r, const secp256k1_fe_storage *a)
{ bignum_copy(4,r->d,4,defcon(a->d));
  CANONIZE(r)
}

/** If flag is true, set *r equal to *a; otherwise leave it. Constant-time.  Both *r and *a must be initialized.*/

static void secp256k1_fe_storage_cmov(secp256k1_fe_storage *r, const secp256k1_fe_storage *a, int flag)
{ bignum_mux_4(flag,r->d,defcon(a->d),r->d);
}

/** If flag is true, set *r equal to *a; otherwise leave it. Constant-time.  Both *r and *a must be initialized.*/

static void secp256k1_fe_cmov(secp256k1_fe *r, const secp256k1_fe *a, int flag)
{ bignum_mux_4(flag,r->d,defcon(a->d),r->d);
  CANONIZE(r)
}

#endif /* SECP256K1_FIELD_IMPL_H */
