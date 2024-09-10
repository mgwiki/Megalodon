external bebits_of_int32 : int32 -> string = "c_int32_bebits";;
external sha256 : string -> string = "c_sha256_bebits";;
external sha256l : string list -> string = "c_sha256_list_bebits";;
external to_hexstring : string -> string = "c_bebits_hexstring";;
(* if input length is odd, last character is ignored as we cannot put it in a single be character *)
external of_hexstring : string -> string = "c_hexstring_bebits";;

external bebits_get_byte : string -> int -> int = "c_bebits_get_byte" [@@noalloc];;
external bebits_set_byte : string -> int -> int -> unit = "c_bebits_set_byte" [@@noalloc];;
external bebits_of_int32p8 : int32 * int32 * int32 * int32 * int32 * int32 * int32 * int32 -> string = "c_int32pow8_bebits";;
external bebits_to_int32p8 : string -> int32 * int32 * int32 * int32 * int32 * int32 * int32 * int32 = "c_bebits_int32pow8";;

let seo o x c =
  let rec seo_iter i c =
    if i = 32 then c else seo_iter (i + 1) (o 8 (bebits_get_byte x i) c) in
  seo_iter 0 c;;

let sei i c =
  let zero n = String.make n '\000' in
  let x = zero 32 in
  let rec sei_iter j c =
    if j = 32 then x, c else
    let v, nc = i 8 c in
    bebits_set_byte x j v;
    sei_iter (j + 1) nc
  in
  sei_iter 0 c;;
