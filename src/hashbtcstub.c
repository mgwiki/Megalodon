#include <caml/alloc.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/custom.h>
#include <arpa/inet.h>
#include <caml/fail.h>

#include "secp256k1.h"
#include "hash_impl.h"

#define visible __attribute__((visibility("default")))

visible value c_int32_bebits(value x){
  CAMLparam1(x);
  CAMLlocal1(r);
  r = caml_alloc_string(4);
  *((uint32_t*)(Bytes_val(r))) = htonl((uint32_t)(Int32_val(x)));
  CAMLreturn(r);
}

value c_sha256_bebits(value s){
  CAMLparam1(s);
  secp256k1_sha256 hasher;
  secp256k1_sha256_initialize(&hasher);
  secp256k1_sha256_write(&hasher, (const unsigned char*)(Bytes_val(s)), caml_string_length(s));
  CAMLlocal1(r);
  r = caml_alloc_string(32);
  secp256k1_sha256_finalize(&hasher, (unsigned char*)(Bytes_val(r)));
  CAMLreturn(r);
}

#define hd(a) Field(a, 0)
#define tl(a) Field(a, 1)

value c_sha256_list_bebits(value l){
  CAMLparam1(l);
  secp256k1_sha256 hasher;
  secp256k1_sha256_initialize(&hasher);
  for (; l != Val_emptylist; l = tl(l))
    secp256k1_sha256_write(&hasher, (const unsigned char*)(Bytes_val(hd(l))), caml_string_length(hd(l)));
  CAMLlocal1(r);
  r = caml_alloc_string(32);
  secp256k1_sha256_finalize(&hasher, (unsigned char*)(Bytes_val(r)));
  CAMLreturn(r);
}

static inline char i_to_ascii(uint8_t i) {
  return (((i < 10) ? '0' : 'W') + i); // W is the ascii code of 'a' minus 10
}

visible value c_bebits_hexstring(value x){
  CAMLparam1(x);
  const mlsize_t len = caml_string_length(x);
  CAMLlocal1(r);
  r = caml_alloc_string(2 * len);
  for (uint32_t i = 0; i < len; ++i) {
    const uint8_t xi = Byte_u(x, i);
    const uint8_t c2 = xi        & 0x0F;
    const uint8_t c1 = (xi >> 4) & 0x0F;
    Byte(r, 2 * i  ) = i_to_ascii(c1);
    Byte(r, 2 * i+1) = i_to_ascii(c2);
  }
  CAMLreturn(r);
}

static const char hextable[] = {
  -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
  -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
  -1,-1, 0,1,2,3,4,5,6,7,8,9,-1,-1,-1,-1,-1,-1,-1,10,11,12,13,14,15,-1,
  -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
  -1,-1,10,11,12,13,14,15,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
  -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
  -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
  -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
  -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
  -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
  -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1
};

// Could also provide a 'hexsubstring_bebits'
// Ignores last character is length is odd.
visible value c_hexstring_bebits(value x){
  CAMLparam1(x);
  const mlsize_t len = caml_string_length(x);
  const mlsize_t nlen = len >> 1;
  CAMLlocal1(r);
  r = caml_alloc_string(nlen);
  for (uint32_t i = 0; i < nlen; ++i) {
    const int8_t b1 = hextable[Byte_u(x, 2 * i)];
    const int8_t b2 = hextable[Byte_u(x, 2 * i + 1)];
    if (b1 < 0 || b2 < 0)
      caml_invalid_argument("c_hexstring_bebits: not a hex string!");
    Byte_u(r, i) = b1 << 4 | b2;
  }
  CAMLreturn(r);
}

visible value c_bebits_get_byte(value x, value i){
  CAMLparam2(x,i);
  const uint8_t t = Bytes_val(x)[Int_val(i)];
  CAMLreturn(Val_int(t));
}

visible void c_bebits_set_byte(value x, value i, value v){
  CAMLparam3(x,i,v);
  const uint8_t t = Int_val(v);
  Bytes_val(x)[Int_val(i)] = t;
  CAMLreturn0;
}

visible value c_int32pow8_bebits(value x){
  CAMLparam1(x);
  CAMLlocal1(r);
  r = caml_alloc_string(32);
  ((uint32_t*)(Bytes_val(r)))[0] = htonl((uint32_t)(Int32_val(Field(x, 0))));
  ((uint32_t*)(Bytes_val(r)))[1] = htonl((uint32_t)(Int32_val(Field(x, 1))));
  ((uint32_t*)(Bytes_val(r)))[2] = htonl((uint32_t)(Int32_val(Field(x, 2))));
  ((uint32_t*)(Bytes_val(r)))[3] = htonl((uint32_t)(Int32_val(Field(x, 3))));
  ((uint32_t*)(Bytes_val(r)))[4] = htonl((uint32_t)(Int32_val(Field(x, 4))));
  ((uint32_t*)(Bytes_val(r)))[5] = htonl((uint32_t)(Int32_val(Field(x, 5))));
  ((uint32_t*)(Bytes_val(r)))[6] = htonl((uint32_t)(Int32_val(Field(x, 6))));
  ((uint32_t*)(Bytes_val(r)))[7] = htonl((uint32_t)(Int32_val(Field(x, 7))));
  CAMLreturn(r);
}

visible value c_bebits_int32pow8(value x){
  CAMLparam1(x);
  if (caml_string_length(x) != 32)
    caml_invalid_argument("c_bebits_int32pow8: not a 32 byte string!");
  CAMLlocal4(a,b,c,d);
  a=caml_copy_int32((int32_t)(ntohl(((uint32_t*)(Bytes_val(x)))[0])));
  b=caml_copy_int32((int32_t)(ntohl(((uint32_t*)(Bytes_val(x)))[1])));
  c=caml_copy_int32((int32_t)(ntohl(((uint32_t*)(Bytes_val(x)))[2])));
  d=caml_copy_int32((int32_t)(ntohl(((uint32_t*)(Bytes_val(x)))[3])));
  CAMLlocal4(e,f,g,h);
  e=caml_copy_int32((int32_t)(ntohl(((uint32_t*)(Bytes_val(x)))[4])));
  f=caml_copy_int32((int32_t)(ntohl(((uint32_t*)(Bytes_val(x)))[5])));
  g=caml_copy_int32((int32_t)(ntohl(((uint32_t*)(Bytes_val(x)))[6])));
  h=caml_copy_int32((int32_t)(ntohl(((uint32_t*)(Bytes_val(x)))[7])));
  CAMLlocal1(r);
  r = caml_alloc_tuple(8);
  Field(r, 0) = a;
  Field(r, 1) = b;
  Field(r, 2) = c;
  Field(r, 3) = d;
  Field(r, 4) = e;
  Field(r, 5) = f;
  Field(r, 6) = g;
  Field(r, 7) = h;
  CAMLreturn(r);
}
