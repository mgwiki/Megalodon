(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)
type hashvalold = int32 * int32 * int32 * int32 * int32 * int32 * int32 * int32
let hashint32 x = Hashbtc.bebits_to_int32p8 (Hash.hashint32 x);;
let hashpair x y = Hashbtc.bebits_to_int32p8 (Hash.hashpair (Hashbtc.bebits_of_int32p8 x) (Hashbtc.bebits_of_int32p8 y));;
let hashtag x tg = Hashbtc.bebits_to_int32p8 (Hash.hashtag (Hashbtc.bebits_of_int32p8 x) tg);;
let hashval_hexstring x = Hash.hashval_hexstring (Hashbtc.bebits_of_int32p8 x)
let hexstring_hashval x = Hashbtc.bebits_to_int32p8 (Hash.hexstring_hashval x)
let md256_hexstring = hashval_hexstring
let hexstring_md256 = hexstring_hashval
