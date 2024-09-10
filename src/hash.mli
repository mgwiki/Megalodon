(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

type hashval = string

val hashval_hexstring : hashval -> string
val hexstring_hashval : string -> hashval
val md256_hexstring : int32 * int32 * int32 * int32 * int32 * int32 * int32 * int32 -> string
val hexstring_md256 : string -> int32 * int32 * int32 * int32 * int32 * int32 * int32 * int32

val printhashval : hashval -> unit
val hashint32 : int32 -> hashval
val hashpair : hashval -> hashval -> hashval
val hashtag : hashval -> int32 -> hashval
(*val hashlist : hashval list -> hashval*)
val ohashlist : hashval list -> hashval option
val hashopair : hashval option -> hashval option -> hashval option
val hashopair2 : hashval option -> hashval -> hashval

val seo_hashval : (int -> int -> 'a -> 'a) -> hashval -> 'a -> 'a
val sei_hashval : (int -> 'a -> int * 'a) -> 'a -> hashval * 'a

val sha256 : string -> hashval
