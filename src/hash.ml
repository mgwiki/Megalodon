(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)
type hashval = string

let hi = Hashtbl.create 1000000;;
let hp = Hashtbl.create 1000000;;
let ht = Hashtbl.create 1000000;;
let hashint32 x = try Hashtbl.find hi x with Not_found -> let ret = Hashbtc.sha256l ["\000\000\000\001"; Hashbtc.bebits_of_int32 x] in Hashtbl.add hi x ret; ret;;
let hashpair x y = try Hashtbl.find hp (x,y) with Not_found -> let ret = Hashbtc.sha256l ["\000\000\000\007"; x; y] in Hashtbl.add hp (x,y) ret; ret;;
let hashtag x tg = try Hashtbl.find ht (x,tg) with Not_found -> let ret = Hashbtc.sha256l ["\000\000\000\008"; Hashbtc.bebits_of_int32 tg; x] in Hashtbl.add ht (x,tg) ret; ret;;
let hashval_hexstring x = Hashbtc.to_hexstring x
let hexstring_hashval x = Hashbtc.of_hexstring x
let sha256 x = Hashbtc.sha256 x;;
let md256_hexstring x = hashval_hexstring (Hashbtc.bebits_of_int32p8 x);;
let hexstring_md256 x = Hashbtc.bebits_to_int32p8 (hexstring_hashval x);;

let rec ohashlist hl =
  begin
    match hl with
    | [] -> None
    | h::hr ->
	begin
	  match ohashlist hr with
	  | None -> Some(hashtag h 3l)
	  | Some(k) -> Some(hashtag (hashpair h k) 4l)
	end
  end

(*** hashopair, x and y are hashval options ***)
let hashopair x y =
  match x,y with
  | Some x,Some y -> Some(hashpair x y)
  | Some x,None -> Some(hashtag x 0l)
  | None,Some y -> Some(hashtag y 1l)
  | None,None -> None

let hashopair2 x y =
  match x with
  | Some x -> hashpair x y
  | None -> hashtag y 1l

let printhashval h =
  Printf.printf "%s\n" (hashval_hexstring h)

let seo_hashval o x c = Hashbtc.seo o x c;;
let sei_hashval i c = let s,r = Hashbtc.sei i c in s, r;;
