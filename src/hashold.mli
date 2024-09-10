(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

type hashvalold = int32 * int32 * int32 * int32 * int32 * int32 * int32 * int32

val hashval_hexstring : hashvalold -> string
val hexstring_hashval : string -> hashvalold
val hashint32 : int32 -> hashvalold
val hashpair : hashvalold -> hashvalold -> hashvalold
val hashtag : hashvalold -> int32 -> hashvalold
val md256_hexstring : hashvalold -> string
val hexstring_md256 : string -> hashvalold
