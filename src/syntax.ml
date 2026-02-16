(* Copyright (c) 2020-2023 CIIRC (Czech Institute of Informatics, Robotics and Cybernetics) / CTU (Czech Technical University) *)
(*** File: syntax.ml ***)
(*** Chad E. Brown ***)
(*** Jan 18 2014 (Egal version started) ***)

let sexprinfo = ref false;;
let reportbushydeps = ref None;;

let explorerurl = ref "https://formalweb3.uibk.ac.at/pgbce/q.php"

let pfgtmroot : (string,string) Hashtbl.t = Hashtbl.create 100;;
let pfgobjid : (string,string) Hashtbl.t = Hashtbl.create 100;;
let pfgpropid : (string,string) Hashtbl.t = Hashtbl.create 100;;

let notationhrefcntr = ref 0;;
let postinfixnotationhrefstack : (string,string list) Hashtbl.t = Hashtbl.create 100;;
let prefixnotationhrefstack : (string,string list) Hashtbl.t = Hashtbl.create 100;;
let bindernotationhrefstack : (string,string list) Hashtbl.t = Hashtbl.create 100;;
let tuplenotationhrefstack = ref [];;
let ifnotationhrefstack = ref [];;
let setlamnotationhrefstack = ref [];;
let replnotationhrefstack = ref [];;
let sepnotationhrefstack = ref [];;
let replsepnotationhrefstack = ref [];;
let setenumnotationhrefstack = ref [];;
let setenum0notationhrefstack = ref [];;
let setenum1notationhrefstack = ref [];;
let setenum2notationhrefstack = ref [];;
let natnotationhrefstack = ref [];;

let pop_notationstack r =
  match !r with
  | [] -> ()
  | _::rr -> r := rr;;

let copy_head_notationstack r =
  match !r with
  | [] -> ()
  | h::rr -> r := h::h::rr;;

let pop_notationhashtbl h =
  let l = ref [] in
  Hashtbl.iter
    (fun k v ->
      match v with
      | [] -> ()
      | _::[] -> ()
      | _::rr -> l := (k,rr)::!l)
    h;
  Hashtbl.clear h;
  if not (!l = []) then
    List.iter (fun (k,v) -> Hashtbl.replace h k v) !l
  
let copy_head_notationhashtbl h =
  let l = ref [] in
  Hashtbl.iter
    (fun k v ->
      match v with
      | [] -> ()
      | hr::rr -> l := (k,hr::v)::!l)
    h;
  Hashtbl.clear h;
  if not (!l = []) then
    List.iter (fun (k,v) -> Hashtbl.replace h k v) !l

let wrap_href_special ch s f =
  match s with
  | [] -> f()
  | h::_ ->
     Printf.fprintf ch "<a href='#%s'>" h;
     f();
     Printf.fprintf ch "</a>";;

let wrap_href_special2 ch s s2 f =
  match s with
  | [] -> wrap_href_special ch s2 f
  | h::_ ->
     Printf.fprintf ch "<a href='#%s'>" h;
     f();
     Printf.fprintf ch "</a>";;

let hashtbl_find_or_nil h k =
  try
    Hashtbl.find h k
  with Not_found -> []

type pfgthy = HF | Egal | Mizar | HOAS | SetMM;;

let pfgtheory : pfgthy ref = ref Egal;;

let pfgreserved : (string,unit) Hashtbl.t = Hashtbl.create 100;;

let eagerdeltas = ref false;;

let prim_legend : (int,string) Hashtbl.t = Hashtbl.create 100;;
let tmh_legend : (string,string) Hashtbl.t = Hashtbl.create 100;;
let knownh_legend : (string,string) Hashtbl.t = Hashtbl.create 100;;

Hashtbl.add pfgreserved "Prim" ();;
Hashtbl.add pfgreserved "Ap" ();;
Hashtbl.add pfgreserved "Lam" ();;
Hashtbl.add pfgreserved "Imp" ();;
Hashtbl.add pfgreserved "All" ();;
Hashtbl.add pfgreserved "Ex" ();;
Hashtbl.add pfgreserved "Eq" ();;
Hashtbl.add pfgreserved "PrAp" ();;
Hashtbl.add pfgreserved "TmAp" ();;
Hashtbl.add pfgreserved "PrLa" ();;
Hashtbl.add pfgreserved "TmLa" ();;
Hashtbl.add pfgreserved "Ext" ();;

(** HF theory **)
let pfghfprim : (string,int) Hashtbl.t = Hashtbl.create 100;;
let pfghfknname : (string,string) Hashtbl.t = Hashtbl.create 100;;
let pfghfaxnum : (string,int) Hashtbl.t = Hashtbl.create 100;;

let pfghfanchor : (string,string) Hashtbl.t = Hashtbl.create 100;;

Hashtbl.add pfghfprim "174b78e53fc239e8c2aab4ab5a996a27e3e5741e88070dad186e05fb13f275e5" 0;;
Hashtbl.add pfghfprim "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87" 1;;
Hashtbl.add pfghfprim "5867641425602c707eaecd5be95229f6fd709c9b58d50af108dfe27cb49ac069" 2;;
Hashtbl.add pfghfprim "058f630dd89cad5a22daa56e097e3bdf85ce16ebd3dbf7994e404e2a98800f7f" 3;;
Hashtbl.add pfghfprim "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738" 4;;
Hashtbl.add pfghfprim "cfe97741543f37f0262568fe55abbab5772999079ff734a49f37ed123e4363d7" 5;;
Hashtbl.add pfghfprim "9c60bab687728bc4482e12da2b08b8dbc10f5d71f5cab91acec3c00a79b335a3" 6;;
Hashtbl.add pfghfprim "73c9efe869770ab42f7cde0b33fe26bbc3e2bd157dad141c0c27d1e7348d60f5" 7;;
Hashtbl.add pfghfprim "8a8e36b858cd07fc5e5f164d8075dc68a88221ed1e4c9f28dac4a6fdb2172e87" 8;;
Hashtbl.add pfghfprim "e2a83319facad3a3d8ff453f4ef821d9da495e56a623695546bb7d7ac333f3fe" 9;;
Hashtbl.add pfghfprim "844774016d959cff921a3292054b30b52f175032308aa11e418cb73f5fef3d54" 10;;
Hashtbl.add pfghfprim "2a38dbb37506341b157c11dddf8eb7d8404ce97eb50d5e940b23d5094ae39d70" 11;;
Hashtbl.add pfghfprim "b1b8f6f9d4d6136be8375ed2faddb54df84cdb3018ec6bd2ac07b2c25d3d8af8" 12;;
Hashtbl.add pfghfprim "e7493d5f5a73b6cb40310f6fcb87d02b2965921a25ab96d312adf7eb8157e4b3" 13;;
Hashtbl.add pfghfprim "384d9f66d8806a02ebe28da535de6ad3715d7edbe784c055e3c70df3ad888708" 14;;
Hashtbl.add pfghfprim "bb3da8f6f3861e950e002517b27fe9407103f6d9bfacf8e3d7600f2396cc1059" 15;;
Hashtbl.add pfghfprim "dcde207b36b2fb5f060060582bf079763feaf495d2165b7092e20cd10daf7a99" 16;;
Hashtbl.add pfghfprim "7c09f0cab3d30d5ff3c2ec8c2cff61e158c82ce67d886c8b6a8763990b8a0515" 17;;
Hashtbl.add pfghfprim "c59022da27533d1a9c86144e1d2afd1512d11dfffd04a979887af2e1ee5f6e59" 18;;
Hashtbl.add pfghfprim "c7df083c7cf25a97335c4c9d8dc333551ed272dcab0c9c75bdb57679962006f5" 19;;
Hashtbl.add pfghfprim "06a9db6a163cde1bda5ecbfee9ca49f646ff205577687d3f603d53e0c58aefb5" 20;;
Hashtbl.add pfghfprim "3c3963fd1d3e8a801895ec2bc1bdd6c0d1f64c3f6bee436c56b146112890c357" 21;;
Hashtbl.add pfghfprim "f73cdba5a4e557a8f57fbba8517c0f7593a0b36795e8f51b63ba62b37035c3d0" 22;;
Hashtbl.add pfghfprim "67f7963d11a96caa6d857a801e3a87a49e63de70c1a4d3f1be82810c5ca7eca7" 23;;
Hashtbl.add pfghfprim "161886ed663bc514c81ed7fe836cca71861bfe4dfe4e3ede7ef3a48dbc07d247" 24;;
Hashtbl.add pfghfprim "3e5bc5e85f7552688ed0ced52c5cb8a931e179c99646161ada3249216c657566" 25;;
Hashtbl.add pfghfprim "591ebe2d703dc011fd95f000dd1ad77b0dca9230146d2f3ea2cb96d6d1fba074" 26;;
Hashtbl.add pfghfprim "e66ec047c09acdc1e824084ea640c5c9a30ab00242f4c1f80b83c667c930e87e" 27;;
Hashtbl.add pfghfprim "8f39e0d849db8334a6b514454a2aef6235afa9fc2b6ae44712b4bfcd7ac389cc" 28;;
Hashtbl.add pfghfprim "0609dddba15230f51d1686b31544ff39d4854c4d7f71062511cc07689729b68d" 29;;
Hashtbl.add pfghfprim "4a0f686cd7e2f152f8da5616b417a9f7c3b6867397c9abde39031fa0217d2692" 30;;
Hashtbl.add pfghfprim "4267a4cfb6e147a3c1aa1c9539bd651e22817ab41fd8ab5d535fbf437db49145" 31;;
Hashtbl.add pfghfprim "f3818d36710e8c0117c589ed2d631e086f82fbcbf323e45d2b12a4eaddd3dd85" 32;;
Hashtbl.add pfghfprim "5057825a2357ee2306c9491a856bb7fc4f44cf9790262abb72d8cecde03e3df4" 33;;
Hashtbl.add pfghfprim "f3976896fb7038c2dd6ace65ec3cce7244df6bf443bacb131ad83c3b4d8f71fb" 34;;
Hashtbl.add pfghfprim "35f61b92f0d8ab66d988b2e71c90018e65fc9425895b3bae5d40ddd5e59bebc1" 35;;
Hashtbl.add pfghfprim "b90ec130fa720a21f6a1c02e8b258f65af5e099282fe8b3927313db7f25335ed" 36;;
Hashtbl.add pfghfprim "8c8f550868df4fdc93407b979afa60092db4b1bb96087bc3c2f17fadf3f35cbf" 37;;
Hashtbl.add pfghfprim "3578b0d6a7b318714bc5ea889c6a38cf27f08eaccfab7edbde3cb7a350cf2d9b" 38;;
Hashtbl.add pfghfprim "d2a0e4530f6e4a8ef3d5fadfbb12229fa580c2add302f925c85ede027bb4b175" 39;;
Hashtbl.add pfghfprim "2f8b7f287504f141b0f821928ac62823a377717763a224067702eee02fc1f359" 40;;
Hashtbl.add pfghfprim "f275e97bd8920540d5c9b32de07f69f373d6f93ba6892c9e346254a85620fa17" 41;;
Hashtbl.add pfghfprim "80aea0a41bb8a47c7340fe8af33487887119c29240a470e920d3f6642b91990d" 42;;
Hashtbl.add pfghfprim "158bae29452f8cbf276df6f8db2be0a5d20290e15eca88ffe1e7b41d211d41d7" 43;;
Hashtbl.add pfghfprim "0a445311c45f0eb3ba2217c35ecb47f122b2301b2b80124922fbf03a5c4d223e" 44;;
Hashtbl.add pfghfprim "153bff87325a9c7569e721334015eeaf79acf75a785b960eb1b46ee9a5f023f8" 45;;
Hashtbl.add pfghfprim "d772b0f5d472e1ef525c5f8bd11cf6a4faed2e76d4eacfa455f4d65cc24ec792" 46;;
Hashtbl.add pfghfprim "f7e63d81e8f98ac9bc7864e0b01f93952ef3b0cbf9777abab27bcbd743b6b079" 47;;
Hashtbl.add pfghfprim "f627d20f1b21063483a5b96e4e2704bac09415a75fed6806a2587ce257f1f2fd" 48;;
Hashtbl.add pfghfprim "8cf6b1f490ef8eb37db39c526ab9d7c756e98b0eb12143156198f1956deb5036" 49;;
Hashtbl.add pfghfprim "cc569397a7e47880ecd75c888fb7c5512aee4bcb1e7f6bd2c5f80cccd368c060" 50;;
Hashtbl.add pfghfprim "2ce94583b11dd10923fde2a0e16d5b0b24ef079ca98253fdbce2d78acdd63e6e" 51;;
Hashtbl.add pfghfprim "9ef333480205115fcb54535d5d8de44756eee80867000051222280db0c9646e4" 52;;
Hashtbl.add pfghfprim "6f4d9bb1b2eaccdca0b575e1c5e5a35eca5ce1511aa156bebf7a824f08d1d69d" 53;;
Hashtbl.add pfghfprim "7b717effbbdb47e1c3b6b0b11d8afebd925fdf397e15abe9de1d5ea74224420c" 54;;
Hashtbl.add pfghfprim "ee2e1f36ccc047af9077fcfe6de79d6c9574876b02cae0b4b919e11461760f0d" 55;;
Hashtbl.add pfghfprim "f97da687c51f5a332ff57562bd465232bc70c9165b0afe0a54e6440fc4962a9f" 56;;
Hashtbl.add pfghfprim "9db634daee7fc36315ddda5f5f694934869921e9c5f55e8b25c91c0a07c5cbec" 57;;
Hashtbl.add pfghfprim "25c483dc8509e17d4b6cf67c5b94c2b3f3902a45c3c34582da3e29ab1dc633ab" 58;;
Hashtbl.add pfghfprim "9161ec45669e68b6f032fc9d4d59e7cf0b3f5f860baeb243e29e767a69d600b1" 59;;
Hashtbl.add pfghfprim "e4d45122168d3fb3f5723ffffe4d368988a1be62792f272e949c6728cec97865" 60;;
Hashtbl.add pfghfprim "7a45b2539da964752f7e9409114da7fc18caef138c5d0699ec226407ece64991" 61;;
Hashtbl.add pfghfprim "dab6e51db9653e58783a3fde73d4f2dc2637891208c92c998709e8795ba4326f" 62;;
Hashtbl.add pfghfprim "dc688de6dbfa5c75bd45f1eb198583d07be144f0cdabb44def09da1c0976495b" 63;;
Hashtbl.add pfghfprim "fb5286197ee583bb87a6f052d00fee2b461d328cc4202e5fb40ec0a927da5d7e" 64;;
Hashtbl.add pfghfprim "3585d194ae078f7450f400b4043a7820330f482343edc5773d1d72492da8d168" 65;;
Hashtbl.add pfghfprim "d3f7df13cbeb228811efe8a7c7fce2918025a8321cdfe4521523dc066cca9376" 66;;
Hashtbl.add pfghfprim "f0267e2cbae501ea3433aecadbe197ba8f39c96e80326cc5981a1630fda29909" 67;;
Hashtbl.add pfghfprim "b260cb5327df5c1f762d4d3068ddb3c7cc96a9cccf7c89cee6abe113920d16f1" 68;;
Hashtbl.add pfghfprim "877ee30615a1a7b24a60726a1cf1bff24d7049b80efb464ad22a6a9c9c4f6738" 69;;
Hashtbl.add pfghfprim "dc75c4d622b258b96498f307f3988491e6ba09fbf1db56d36317e5c18aa5cac6" 70;;
Hashtbl.add pfghfprim "d744bcd791713cf88021ce34168c3e2d109a8a6c45637d74541d94007e3139ca" 71;;
Hashtbl.add pfghfprim "93592da87a6f2da9f7eb0fbd449e0dc4730682572e0685b6a799ae16c236dcae" 72;;
Hashtbl.add pfghfprim "ecef5cea93b11859a42b1ea5e8a89184202761217017f3a5cdce1b91d10b34a7" 73;;
Hashtbl.add pfghfprim "58c1782da006f2fb2849c53d5d8425049fad551eb4f8025055d260f0c9e1fe40" 74;;
Hashtbl.add pfghfprim "dac986a57e8eb6cc7f35dc0ecc031b9ba0403416fabe2dbe130edd287a499231" 75;;
Hashtbl.add pfghfprim "091d1f35158d5ca6063f3c5949e5cbe3d3a06904220214c5781c49406695af84" 76;;
Hashtbl.add pfghfprim "8ab5fa18b3cb4b4b313a431cc37bdd987f036cc47f175379215f69af5977eb3b" 77;;
Hashtbl.add pfghfprim "fcd77a77362d494f90954f299ee3eb7d4273ae93d2d776186c885fc95baa40dc" 78;;
Hashtbl.add pfghfprim "0775ebd23cf37a46c4b7bc450bd56bce8fc0e7a179485eb4384564c09a44b00f" 79;;
Hashtbl.add pfghfprim "04c0176f465abbde82b7c5c716ac86c00f1b147c306ffc6b691b3a5e8503e295" 80;;
Hashtbl.add pfghfprim "dc7715ab5114510bba61a47bb1b563d5ab4bbc08004208d43961cf61a850b8b5" 81;;
Hashtbl.add pfghfprim "ac96e86902ef72d5c44622f4a1ba3aaf673377d32cc26993c04167cc9f22067f" 82;;
Hashtbl.add pfghfprim "f36b5131fd375930d531d698d26ac2fc4552d148f386caa7d27dbce902085320" 83;;
Hashtbl.add pfghfprim "2336eb45d48549dd8a6a128edc17a8761fd9043c180691483bcf16e1acc9f00a" 84;;
Hashtbl.add pfghfprim "f91c31af54bc4bb4f184b6de34d1e557a26e2d1c9f3c78c2b12be5ff6d66df66" 85;;
Hashtbl.add pfghfprim "e59af381b17c6d7665103fc55f99405c91c5565fece1832a6697045a1714a27a" 86;;
Hashtbl.add pfghfprim "eb5699f1770673cc0c3bfaa04e50f2b8554934a9cbd6ee4e9510f57bd9e88b67" 87;;
Hashtbl.add pfghfprim "1e55e667ef0bb79beeaf1a09548d003a4ce4f951cd8eb679eb1fed9bde85b91c" 88;;
Hashtbl.add pfghfprim "3bbf071b189275f9b1ce422c67c30b34c127fdb067b3c9b4436b02cfbe125351" 89;;
Hashtbl.add pfghfprim "89e534b3d5ad303c952b3eac3b2b69eb72d95ba1d9552659f81c57725fc03350" 90;;
Hashtbl.add pfghfprim "87d7604c7ea9a2ae0537066afb358a94e6ac0cd80ba277e6b064422035a620cf" 91;;
Hashtbl.add pfghfprim "bf1decfd8f4025a2271f2a64d1290eae65933d0f2f0f04b89520449195f1aeb8" 92;;
Hashtbl.add pfghfprim "6f17daea88196a4c038cd716092bd8ddbb3eb8bddddfdc19e65574f30c97ab87" 93;;
Hashtbl.add pfghfprim "0d574978cbb344ec3744139d5c1d0d90336d38f956e09a904d230c4fa06b30d1" 94;;
Hashtbl.add pfghfprim "09cdd0b9af76352f6b30bf3c4bca346eaa03d280255f13afb2e73fe8329098b6" 95;;
Hashtbl.add pfghfprim "c271c80f80f5f72a61f48aa63abcf552ccb5c1c1455890804f46f810f52c1725" 96;;
Hashtbl.add pfghfprim "8aee977f39b94de3060d4e641f09019ff1a3f86f5572cb3093ec9aa4a0a4c21b" 97;;
Hashtbl.add pfghfprim "65c0daed14d78ada9e0321a2b41d12cc9f628aacc67d8a940c28f08abf25f617" 98;;
Hashtbl.add pfghfprim "c309fccae6f2952d12a16bfffc197737f9a1e290345afcd106428e646f9cbd2e" 99;;
Hashtbl.add pfghfprim "cbf428d60d780d655f1b7593b16f52a9cbc57bf95a866db8389c330113d406f3" 100;;
Hashtbl.add pfghfprim "f152c3f1281bd34cf1c2b19b596c7883b3995533b2fcccc0eaa6048037ebe4d3" 101;;
Hashtbl.add pfghfprim "4bc888f121f3c8defd33607bf8c316d9626aeb31d9d8b49058dc19828f9be72b" 102;;
Hashtbl.add pfghfprim "dff028b00391bf89df7db2deea89f2e8932114cc819135e93697f3555f1f256d" 103;;

Hashtbl.add pfghfaxnum "4d0b1b3ca489073915e8701e021a09da22887f41f83e407df8eafe040825db18" 0;;
Hashtbl.add pfghfaxnum "e4b03c310442ae760be9945e176494db51515dfb952ee60fbd42e05527752af0" 1;;
Hashtbl.add pfghfaxnum "d8c32d0ac70c5760222c9adf1a3ca90f3cb6b5182b0f70a5d82cb9000abc77ef" 2;;
Hashtbl.add pfghfaxnum "5189b0389a1efe35ba744aa1436bb23541e75e8a85658313375e1e0b3321128f" 3;;
Hashtbl.add pfghfaxnum "920f955f033a1286fcaba96c8eb55d2079812a3041ff6b812df4cc2636156b59" 4;;
Hashtbl.add pfghfaxnum "0b67fbe4188c03468f8cd69c462ea8e5fb2269bf1fd67125a6456853d4ab7c74" 5;;
Hashtbl.add pfghfaxnum "b492ab96942311595fd53c93243cb7ab5314986bb8460d580d9382dfab90f7d1" 6;;
Hashtbl.add pfghfaxnum "c10976371705fb97042c207e4021721b0543188b170452fb918fb78d30b85c02" 7;;
Hashtbl.add pfghfaxnum "de0eaf5d33c0b573d63cc09df92572f243045babd3e3cb9aa49e72d618f6c7c9" 8;;
Hashtbl.add pfghfaxnum "73fa935250c44cafb3971bffe3b0cdef8869cd5693da6149f81741261543e04d" 9;;
Hashtbl.add pfghfaxnum "d163e2ba8be4862ce0d5ac17697ba5682d8de00436463bf450e9125489dacfc3" 10;;
Hashtbl.add pfghfaxnum "0c00a11817788d01d6282959a65fb640cd29eeecb21451696ae86d2c972ea6a1" 11;;
Hashtbl.add pfghfaxnum "81edf453007e75af3d93a8839c342755cf567e7e6a5013d8f463cb4140ccad71" 12;;
Hashtbl.add pfghfaxnum "6cb883a59e6fddeb39d4eebbe83417eba32939a89eb03700ed2435b07d6f31a5" 13;;
Hashtbl.add pfghfaxnum "06e53f495fbacecf847dbc5190516b217f2f92565fe8bfc4615d85e44cc77999" 14;;
Hashtbl.add pfghfaxnum "9b82b58da0e4095efc581051714ee0393eb423e395ec31dc00ec6d95c8e77b64" 15;;
Hashtbl.add pfghfaxnum "565012fb49695bbe133012328479877f4cead41cd3716f3772f3913917b21c27" 16;;
Hashtbl.add pfghfaxnum "8ad26e31e3f38cfdf8779e1d676300e70c868404a4fdeb018dd56527642ecee1" 17;;
Hashtbl.add pfghfaxnum "3ad2cd53af6e886067f36cf5d7a6686fb057b11e0af8ccb3ae491fce5213f516" 18;;
Hashtbl.add pfghfaxnum "7db945208f1c44134b64f1d6aa93463fa0c8bc5f1e02c9723c1a6c807e17bcc2" 19;;
Hashtbl.add pfghfaxnum "1e4e84c130e0882f993ba6d0725e5ce537488f3e04aeede384a09f2d1b06719d" 20;;
Hashtbl.add pfghfaxnum "5fded9d5ec7a3d33bfb840dc4a879fc85216375a19e401f04514b20635bf0648" 21;;
Hashtbl.add pfghfaxnum "87271e863c44798c3e4de1b8f94789072942588da2226bb4b8ab30dfd7954f42" 22;;
Hashtbl.add pfghfaxnum "d85840034f85eb9ab4e3d0362277ac520974920f971983d1894a834be2f58be4" 23;;
Hashtbl.add pfghfaxnum "bf0e9190cbf189b369083df40a90fa3be75393b0cdc894a6e7624bf15b71eae3" 24;;
Hashtbl.add pfghfaxnum "e1493c8264407ce4977f743da708af28f3e1817238c5e6a4df6fe74e4eac3608" 25;;
Hashtbl.add pfghfaxnum "cf0ceafc8c7e1c575b546e37d09bd7dc2acbed4fd47e5e5c6367777dce26e23d" 26;;
Hashtbl.add pfghfaxnum "03ef95824c9d27c385abd2cbf383f74dd9055886882b365893f0308b44a54a6a" 27;;
Hashtbl.add pfghfaxnum "b3f7f55079aa75828bfd3546160e7e051546d8bb9c652e454240c24b2953a703" 28;;
Hashtbl.add pfghfaxnum "bb7b109b6d194e6019b5ed8f268daa4a5944b43e2861d9c77bc9c90a26a6546f" 29;;
Hashtbl.add pfghfaxnum "b5e97e5c479a400f15307f87ad7213febacf085aca1fcffe72dc9b606b43b224" 30;;
Hashtbl.add pfghfaxnum "7fdf10edf434392f083f83041d690be73abf737b4349f00e2439155761461a53" 31;;
Hashtbl.add pfghfaxnum "255284955fa857314ff4caa3fb1f74c8c002da18d1dcb5dc7e42e903c456d5e9" 32;;
Hashtbl.add pfghfaxnum "406886eb8ba2e63fd142e06f6d7776bd0ac252db18f45614976726ccbeada812" 33;;
Hashtbl.add pfghfaxnum "03b8444fc49f5ce909b97c84648b4538c4bc9f6968e92a8a9243fc06db320dcf" 34;;
Hashtbl.add pfghfaxnum "7ee92353533ddf535d642b2bef129c16c883c14d39afce96770747278152c535" 35;;
Hashtbl.add pfghfaxnum "ad12f6917e0ca69c133ca56a02d806067620494392a4e55a3ac777c23bcf2ecb" 36;;
Hashtbl.add pfghfaxnum "ecefebac8563a68cbfce793120303743637d5819451daffc181b33f630a438b6" 37;;
Hashtbl.add pfghfaxnum "db908632cbf11771ec4744480ece7a038138cfb412c4002ac4861a544f7f9bc6" 38;;
Hashtbl.add pfghfaxnum "b6e249245c9d96bc7c87682fa4b263749fd50f89ced60ddba233249143b17ec6" 39;;
Hashtbl.add pfghfaxnum "b6fb7dfd3a4e7e4d40d079a52242724a194378edcb1723c9194906bdb983e7de" 40;;
Hashtbl.add pfghfaxnum "3c031eb9b813b10c973c2e405a449509495e89954b4927372175bde6a43672bb" 41;;
Hashtbl.add pfghfaxnum "0cb1eb090a19596f321d88b63bd310023ff30f1e55f649589c9dc7ad04918219" 42;;
Hashtbl.add pfghfaxnum "721e592a599e6ae4f540013ca4dff30ccb24f5a8279aecf7a527d3fdd365713e" 43;;
Hashtbl.add pfghfaxnum "1013258a7dd03314edde209dc3ed607693e989cd51567ee2b3770f70512a100c" 44;;
Hashtbl.add pfghfaxnum "fe0137795d3e0bb93daba2e7871618d0878ea87235765eda5ccfe10d795c4028" 45;;
Hashtbl.add pfghfaxnum "84ce1720f201517b5d7d0a55cf867ad2e1830c370df9f00103f3b8f4ede18442" 46;;
Hashtbl.add pfghfaxnum "1d313c5de18d746735e9bfa92b8e6f0bc60d8718fac1e198635080d3d0a330f1" 47;;
Hashtbl.add pfghfaxnum "d7d6188fe9d1029409ee6a37626f85d97049d246e0c58ce03256c1ba25c90b59" 48;;
Hashtbl.add pfghfaxnum "77e29ee5b23b44e015f7012c4a3d9fbe416b26f56b7d575c1c972d8fb7ae1d8e" 49;;
Hashtbl.add pfghfaxnum "80f19f3c9c089aeb52c61db93aac8c5865260969594e036dcae075b48816d85e" 50;;
Hashtbl.add pfghfaxnum "70181fda3cd0f3a49f0e332fffc1b82c7f3db1dea2b54ed28b6eea1422b3a0df" 51;;
Hashtbl.add pfghfaxnum "84847918a6f1940ec36a1b45fa4b2ae22fbd7db41d15edc80e45d7873aef54ff" 52;;
Hashtbl.add pfghfaxnum "6e58b31079ecf8bae23a9c138e685957465c6669ebd5614fe1de151266aca30b" 53;;
Hashtbl.add pfghfaxnum "61134abe2d03ac1a882ca1f6cb15a30302faf8a83dda486152c15415b76431eb" 54;;
Hashtbl.add pfghfaxnum "c7c71a691305af81552e17d4bddd97e45146ffae2dff038ee57c0e33239e8165" 55;;
Hashtbl.add pfghfaxnum "d52ab71745969a7954a3a9dff4f816cfa80f40893dc58cdbf7215538f7db6801" 56;;
Hashtbl.add pfghfaxnum "d98b8cabfcd1585ea3aed5e4341aa3efe311c5c234cfa49859f97f7d338267d6" 57;;
Hashtbl.add pfghfaxnum "ae80637a1c6842749a6b25cd0fb423826edeb06aa9ab471bcb1786a2417e9383" 58;;
Hashtbl.add pfghfaxnum "5d85ec0b61383a7f30ded95d038e36ade33f73733216927e94a6d3a6f29a7297" 59;;
Hashtbl.add pfghfaxnum "a548d12e16f10ede54e57981b037b682eafb7989b4b8fa8de01ef56bfa63f472" 60;;
Hashtbl.add pfghfaxnum "e21218f4f9fe181cc79122ffa00ecd0a9ab89d5c268eab61884d227cb092804c" 61;;
Hashtbl.add pfghfaxnum "8ae304381145ad470bcb5884f94b55179f2d878015514d28fb1fec556d6b9e8b" 62;;
Hashtbl.add pfghfaxnum "a662bd9f0cf9e8ac9a23debeebfe19b66bd11f19173953cea8e6470be043b9af" 63;;
Hashtbl.add pfghfaxnum "28c7a81eb6ad33b10da0764d900b05a10fd1dd2bcc5ed5e58bf75fa8a89d03b6" 64;;
Hashtbl.add pfghfaxnum "1cccbbadd044ffae74c0982aeadf97372aa58997086cc64bc5c256b36b3ea7fa" 65;;
Hashtbl.add pfghfaxnum "1263d8ba94ef9d0d6f7f2b39151f12d28d2d8c71ba57de61f6ac8cc6b355f701" 66;;
Hashtbl.add pfghfaxnum "4a22d56a44f5a868129999956374ce814c29898709c8dfc5c00040cdecb23ce6" 67;;
Hashtbl.add pfghfaxnum "6965cb1b0e7c2d05180bbda0d02badf5449f148f0012a7bb2c9ac88f6f71c940" 68;;
Hashtbl.add pfghfaxnum "44c2f2efdcb9da22db222a641a49682addeb32ed8efb2a51bfcd49ebb4ea1a45" 69;;
Hashtbl.add pfghfaxnum "5be13590762e2d145538955a6f24bcb3a5ad7c280d517cb99ade95547629db2a" 70;;
Hashtbl.add pfghfaxnum "26b135d99afcfe8c2658d9b6d4bd2ef9c7f18c6b3e9778ec8a094e1f7e9efcbc" 71;;
Hashtbl.add pfghfaxnum "b14a1577984678c7ad7c87c6bbb9ff2b176b0ad0eb46b57f8a7e05a97ac6640e" 72;;
Hashtbl.add pfghfaxnum "4eafc37373118a9f1243cba3928f3c40a9f0ac0526c943d0c7d25224eebc54ff" 73;;
Hashtbl.add pfghfaxnum "27ca9823a62a4121fe1658d93efca87de1c55324f15ceee21ab4565256024dc4" 74;;
Hashtbl.add pfghfaxnum "218e38705a57200a96de46b70654e61ef9d8b37738f2c493eccbdea77df8016f" 75;;
Hashtbl.add pfghfaxnum "c5522fbe8cf04414ffb8b169c05a81601ed8e85835d65624841b68acc0395eeb" 76;;
Hashtbl.add pfghfaxnum "a680fe3e891cb25b3b41f7ae2c2e87682b19cbd9b1c7c57edcf11097c7d01f7a" 77;;
Hashtbl.add pfghfaxnum "2c345ca37c0de440610409cb7e4a0618cca967ba6399aa197f52c4dddf7a6b1b" 78;;
Hashtbl.add pfghfaxnum "579c6bcc2e49082ddbe990366347358544e408099563117cb95fd61b761acb3e" 79;;
Hashtbl.add pfghfaxnum "9edbe245b62c3afd467422d8d7d68805a9556871be26d98031aaad0eecdcd728" 80;;
Hashtbl.add pfghfaxnum "602ffb18d1bbc5843fe462e731b3f73a5a976ee46e9da6bb6b40d8509a333aa5" 81;;
Hashtbl.add pfghfaxnum "659e82bb8ae88e2b04e50f651d5446a3fdf84711bbf57106c58d8bb717cec709" 82;;
Hashtbl.add pfghfaxnum "12451cb2963ac437754f119fd700a4c871292257bf373759b7bd92287a0143c3" 83;;
Hashtbl.add pfghfaxnum "a185fe1020a787ac3f5fc232b2cdb281c3c8d79b3befbea0c4edf43a97623f29" 84;;
Hashtbl.add pfghfaxnum "35ddbe41ccf8d636bb7be09d378ebbeafa96ab247fbb22d61de52fb2ae8f7d2c" 85;;
Hashtbl.add pfghfaxnum "ecbeeaf0badaae278dd637ce4637ef85208490fc1eae35c0e79164f3f5b9fdf5" 86;;
Hashtbl.add pfghfaxnum "5b5879bfb5f5ab380758f631c5dda71fdd77a20870fc0d9ff94c46e173ce9d04" 87;;
Hashtbl.add pfghfaxnum "c5ca53a6adf517d6574675abbb5f9032ef9ad79b9b8714203f092faaa8ba0887" 88;;
Hashtbl.add pfghfaxnum "82640bea0f55be344d1e16e89f41f32887a7a47d8ee55bff12f5481d83e942b5" 89;;
Hashtbl.add pfghfaxnum "7fca94a5974ea12bc67f55a16f67dbaca0d58af6648a5661c36b0e6c572cd896" 90;;
Hashtbl.add pfghfaxnum "f030a2d2c44eabec7a4cc7446328bc1194822bd4441b8a806ebda667f414ca66" 91;;
Hashtbl.add pfghfaxnum "d20efd6ecacb0cb3079f2127a08724476d4eabf3507c95ed5457caf478e82dc0" 92;;
Hashtbl.add pfghfaxnum "ec74e0e0b43759c2e284f91d3fc896bad3dfb5b25e731877ccefe7c66e001835" 93;;
Hashtbl.add pfghfaxnum "89dc652e8e86a81513b682fa88ff665d5c7ce80f8e965051c98997954b367bf9" 94;;
Hashtbl.add pfghfaxnum "22071e7ec3d44038501eae7b845bd1fe4144e084a8985f9cc2d5dbdabd2f5592" 95;;
Hashtbl.add pfghfaxnum "5d04957e5d383065e03c72e5f6f126c0dfebf4f039551609c1be24d94cf2b447" 96;;
Hashtbl.add pfghfaxnum "95d047b09ce188d473c5e7498669c05fbe6529fc7483ec34f11eec9f9eb9a361" 97;;
Hashtbl.add pfghfaxnum "89bdea0aa616a43a477ff5a2b8f8d93ffd0e81538b14f1e3acf287a190a89ddd" 98;;
Hashtbl.add pfghfaxnum "cbb07c2a4d089aafb664d96f12f4bb4d73181a7d7b6079750a8b1f00ffa3b378" 99;;
Hashtbl.add pfghfaxnum "a9f7dddd1e068a3c747980f5d0555f105b6f79bf8350ae9f2a610b1ad88118a6" 100;;
Hashtbl.add pfghfaxnum "bf9e3955698cfdd47596df01c71e1cf03ac8e02f35e01b8b2560828b931bf3b6" 101;;
Hashtbl.add pfghfaxnum "72fb3b732d20df7b10a7d845367a5d455a600ffaad98f8e89af0d369750d36ee" 102;;
Hashtbl.add pfghfaxnum "85ddba6a7609c822f37b453fe65991931570c7b63ba128a986dba37ced7bbcf1" 103;;
Hashtbl.add pfghfaxnum "047aee660e1a13eb74426c75dbc197f437b5b8efbb63d3fb3c4fe31dfaa6eb61" 104;;
Hashtbl.add pfghfaxnum "822a836127ce60e878d67d66e2b4a46ea0b813f9f55cc8ff810951d073cc1dbc" 105;;
Hashtbl.add pfghfaxnum "aa9ee728af378f05d9eb99b00d097d784ce116396b9b970397b723582e0352eb" 106;;
Hashtbl.add pfghfaxnum "77dc3318ff617828477b0a91f762ed88177211d91054f972756c52eddaba4efc" 107;;

Hashtbl.add pfghfknname "4d0b1b3ca489073915e8701e021a09da22887f41f83e407df8eafe040825db18" "Eps_i_R";;
Hashtbl.add pfghfknname "e4b03c310442ae760be9945e176494db51515dfb952ee60fbd42e05527752af0" "dneg";;
Hashtbl.add pfghfknname "d8c32d0ac70c5760222c9adf1a3ca90f3cb6b5182b0f70a5d82cb9000abc77ef" "prop_ext";;
Hashtbl.add pfghfknname "5189b0389a1efe35ba744aa1436bb23541e75e8a85658313375e1e0b3321128f" "set_ext";;
Hashtbl.add pfghfknname "920f955f033a1286fcaba96c8eb55d2079812a3041ff6b812df4cc2636156b59" "EmptyAx";;
Hashtbl.add pfghfknname "0b67fbe4188c03468f8cd69c462ea8e5fb2269bf1fd67125a6456853d4ab7c74" "UnionEq";;
Hashtbl.add pfghfknname "b492ab96942311595fd53c93243cb7ab5314986bb8460d580d9382dfab90f7d1" "PowerEq";;
Hashtbl.add pfghfknname "c10976371705fb97042c207e4021721b0543188b170452fb918fb78d30b85c02" "ReplEq";;
Hashtbl.add pfghfknname "de0eaf5d33c0b573d63cc09df92572f243045babd3e3cb9aa49e72d618f6c7c9" "HF_Min";;
Hashtbl.add pfghfknname "73fa935250c44cafb3971bffe3b0cdef8869cd5693da6149f81741261543e04d" "In_ind";;
Hashtbl.add pfghfknname "d163e2ba8be4862ce0d5ac17697ba5682d8de00436463bf450e9125489dacfc3" "False_def";;
Hashtbl.add pfghfknname "0c00a11817788d01d6282959a65fb640cd29eeecb21451696ae86d2c972ea6a1" "True_def";;
Hashtbl.add pfghfknname "81edf453007e75af3d93a8839c342755cf567e7e6a5013d8f463cb4140ccad71" "not_def";;
Hashtbl.add pfghfknname "6cb883a59e6fddeb39d4eebbe83417eba32939a89eb03700ed2435b07d6f31a5" "and_def";;
Hashtbl.add pfghfknname "06e53f495fbacecf847dbc5190516b217f2f92565fe8bfc4615d85e44cc77999" "or_def";;
Hashtbl.add pfghfknname "9b82b58da0e4095efc581051714ee0393eb423e395ec31dc00ec6d95c8e77b64" "iff_def";;
Hashtbl.add pfghfknname "565012fb49695bbe133012328479877f4cead41cd3716f3772f3913917b21c27" "Subq_def";;
Hashtbl.add pfghfknname "8ad26e31e3f38cfdf8779e1d676300e70c868404a4fdeb018dd56527642ecee1" "TransSet_def";;
Hashtbl.add pfghfknname "3ad2cd53af6e886067f36cf5d7a6686fb057b11e0af8ccb3ae491fce5213f516" "atleast2_def";;
Hashtbl.add pfghfknname "7db945208f1c44134b64f1d6aa93463fa0c8bc5f1e02c9723c1a6c807e17bcc2" "atleast3_def";;
Hashtbl.add pfghfknname "1e4e84c130e0882f993ba6d0725e5ce537488f3e04aeede384a09f2d1b06719d" "atleast4_def";;
Hashtbl.add pfghfknname "5fded9d5ec7a3d33bfb840dc4a879fc85216375a19e401f04514b20635bf0648" "atleast5_def";;
Hashtbl.add pfghfknname "87271e863c44798c3e4de1b8f94789072942588da2226bb4b8ab30dfd7954f42" "atleast6_def";;
Hashtbl.add pfghfknname "d85840034f85eb9ab4e3d0362277ac520974920f971983d1894a834be2f58be4" "exactly2_def";;
Hashtbl.add pfghfknname "bf0e9190cbf189b369083df40a90fa3be75393b0cdc894a6e7624bf15b71eae3" "exactly3_def";;
Hashtbl.add pfghfknname "e1493c8264407ce4977f743da708af28f3e1817238c5e6a4df6fe74e4eac3608" "exactly4_def";;
Hashtbl.add pfghfknname "cf0ceafc8c7e1c575b546e37d09bd7dc2acbed4fd47e5e5c6367777dce26e23d" "exactly5_def";;
Hashtbl.add pfghfknname "03ef95824c9d27c385abd2cbf383f74dd9055886882b365893f0308b44a54a6a" "exu_i_def";;
Hashtbl.add pfghfknname "b3f7f55079aa75828bfd3546160e7e051546d8bb9c652e454240c24b2953a703" "reflexive_i_def";;
Hashtbl.add pfghfknname "bb7b109b6d194e6019b5ed8f268daa4a5944b43e2861d9c77bc9c90a26a6546f" "irreflexive_i_def";;
Hashtbl.add pfghfknname "b5e97e5c479a400f15307f87ad7213febacf085aca1fcffe72dc9b606b43b224" "symmetric_i_def";;
Hashtbl.add pfghfknname "7fdf10edf434392f083f83041d690be73abf737b4349f00e2439155761461a53" "antisymmetric_i_def";;
Hashtbl.add pfghfknname "255284955fa857314ff4caa3fb1f74c8c002da18d1dcb5dc7e42e903c456d5e9" "transitive_i_def";;
Hashtbl.add pfghfknname "406886eb8ba2e63fd142e06f6d7776bd0ac252db18f45614976726ccbeada812" "eqreln_i_def";;
Hashtbl.add pfghfknname "03b8444fc49f5ce909b97c84648b4538c4bc9f6968e92a8a9243fc06db320dcf" "per_i_def";;
Hashtbl.add pfghfknname "7ee92353533ddf535d642b2bef129c16c883c14d39afce96770747278152c535" "linear_i_def";;
Hashtbl.add pfghfknname "ad12f6917e0ca69c133ca56a02d806067620494392a4e55a3ac777c23bcf2ecb" "trichotomous_or_i_def";;
Hashtbl.add pfghfknname "ecefebac8563a68cbfce793120303743637d5819451daffc181b33f630a438b6" "partialorder_i_def";;
Hashtbl.add pfghfknname "db908632cbf11771ec4744480ece7a038138cfb412c4002ac4861a544f7f9bc6" "totalorder_i_def";;
Hashtbl.add pfghfknname "b6e249245c9d96bc7c87682fa4b263749fd50f89ced60ddba233249143b17ec6" "strictpartialorder_i_def";;
Hashtbl.add pfghfknname "b6fb7dfd3a4e7e4d40d079a52242724a194378edcb1723c9194906bdb983e7de" "stricttotalorder_i_def";;
Hashtbl.add pfghfknname "3c031eb9b813b10c973c2e405a449509495e89954b4927372175bde6a43672bb" "If_i_def";;
Hashtbl.add pfghfknname "0cb1eb090a19596f321d88b63bd310023ff30f1e55f649589c9dc7ad04918219" "exactly1of2_def";;
Hashtbl.add pfghfknname "721e592a599e6ae4f540013ca4dff30ccb24f5a8279aecf7a527d3fdd365713e" "exactly1of3_def";;
Hashtbl.add pfghfknname "1013258a7dd03314edde209dc3ed607693e989cd51567ee2b3770f70512a100c" "nIn_def";;
Hashtbl.add pfghfknname "fe0137795d3e0bb93daba2e7871618d0878ea87235765eda5ccfe10d795c4028" "nSubq_def";;
Hashtbl.add pfghfknname "84ce1720f201517b5d7d0a55cf867ad2e1830c370df9f00103f3b8f4ede18442" "UPair_def";;
Hashtbl.add pfghfknname "1d313c5de18d746735e9bfa92b8e6f0bc60d8718fac1e198635080d3d0a330f1" "Sing_def";;
Hashtbl.add pfghfknname "d7d6188fe9d1029409ee6a37626f85d97049d246e0c58ce03256c1ba25c90b59" "binunion_def";;
Hashtbl.add pfghfknname "77e29ee5b23b44e015f7012c4a3d9fbe416b26f56b7d575c1c972d8fb7ae1d8e" "SetAdjoin_def";;
Hashtbl.add pfghfknname "80f19f3c9c089aeb52c61db93aac8c5865260969594e036dcae075b48816d85e" "famunion_def";;
Hashtbl.add pfghfknname "70181fda3cd0f3a49f0e332fffc1b82c7f3db1dea2b54ed28b6eea1422b3a0df" "Sep_def";;
Hashtbl.add pfghfknname "84847918a6f1940ec36a1b45fa4b2ae22fbd7db41d15edc80e45d7873aef54ff" "ReplSep_def";;
Hashtbl.add pfghfknname "6e58b31079ecf8bae23a9c138e685957465c6669ebd5614fe1de151266aca30b" "binintersect_def";;
Hashtbl.add pfghfknname "61134abe2d03ac1a882ca1f6cb15a30302faf8a83dda486152c15415b76431eb" "setminus_def";;
Hashtbl.add pfghfknname "c7c71a691305af81552e17d4bddd97e45146ffae2dff038ee57c0e33239e8165" "inj_def";;
Hashtbl.add pfghfknname "d52ab71745969a7954a3a9dff4f816cfa80f40893dc58cdbf7215538f7db6801" "bij_def";;
Hashtbl.add pfghfknname "d98b8cabfcd1585ea3aed5e4341aa3efe311c5c234cfa49859f97f7d338267d6" "atleastp_def";;
Hashtbl.add pfghfknname "ae80637a1c6842749a6b25cd0fb423826edeb06aa9ab471bcb1786a2417e9383" "equip_def";;
Hashtbl.add pfghfknname "5d85ec0b61383a7f30ded95d038e36ade33f73733216927e94a6d3a6f29a7297" "In_rec_G_i_def";;
Hashtbl.add pfghfknname "a548d12e16f10ede54e57981b037b682eafb7989b4b8fa8de01ef56bfa63f472" "In_rec_i_def";;
Hashtbl.add pfghfknname "e21218f4f9fe181cc79122ffa00ecd0a9ab89d5c268eab61884d227cb092804c" "ordsucc_def";;
Hashtbl.add pfghfknname "8ae304381145ad470bcb5884f94b55179f2d878015514d28fb1fec556d6b9e8b" "nat_p_def";;
Hashtbl.add pfghfknname "a662bd9f0cf9e8ac9a23debeebfe19b66bd11f19173953cea8e6470be043b9af" "nat_primrec_def";;
Hashtbl.add pfghfknname "28c7a81eb6ad33b10da0764d900b05a10fd1dd2bcc5ed5e58bf75fa8a89d03b6" "add_nat_def";;
Hashtbl.add pfghfknname "1cccbbadd044ffae74c0982aeadf97372aa58997086cc64bc5c256b36b3ea7fa" "mul_nat_def";;
Hashtbl.add pfghfknname "1263d8ba94ef9d0d6f7f2b39151f12d28d2d8c71ba57de61f6ac8cc6b355f701" "ordinal_def";;
Hashtbl.add pfghfknname "4a22d56a44f5a868129999956374ce814c29898709c8dfc5c00040cdecb23ce6" "V__def";;
Hashtbl.add pfghfknname "6965cb1b0e7c2d05180bbda0d02badf5449f148f0012a7bb2c9ac88f6f71c940" "Inj1_def";;
Hashtbl.add pfghfknname "44c2f2efdcb9da22db222a641a49682addeb32ed8efb2a51bfcd49ebb4ea1a45" "Inj0_def";;
Hashtbl.add pfghfknname "5be13590762e2d145538955a6f24bcb3a5ad7c280d517cb99ade95547629db2a" "Unj_def";;
Hashtbl.add pfghfknname "26b135d99afcfe8c2658d9b6d4bd2ef9c7f18c6b3e9778ec8a094e1f7e9efcbc" "combine_funcs_def";;
Hashtbl.add pfghfknname "b14a1577984678c7ad7c87c6bbb9ff2b176b0ad0eb46b57f8a7e05a97ac6640e" "setsum_def";;
Hashtbl.add pfghfknname "4eafc37373118a9f1243cba3928f3c40a9f0ac0526c943d0c7d25224eebc54ff" "proj0_def";;
Hashtbl.add pfghfknname "27ca9823a62a4121fe1658d93efca87de1c55324f15ceee21ab4565256024dc4" "proj1_def";;
Hashtbl.add pfghfknname "218e38705a57200a96de46b70654e61ef9d8b37738f2c493eccbdea77df8016f" "binrep_def";;
Hashtbl.add pfghfknname "c5522fbe8cf04414ffb8b169c05a81601ed8e85835d65624841b68acc0395eeb" "lam_def";;
Hashtbl.add pfghfknname "a680fe3e891cb25b3b41f7ae2c2e87682b19cbd9b1c7c57edcf11097c7d01f7a" "setprod_def";;
Hashtbl.add pfghfknname "2c345ca37c0de440610409cb7e4a0618cca967ba6399aa197f52c4dddf7a6b1b" "ap_def";;
Hashtbl.add pfghfknname "579c6bcc2e49082ddbe990366347358544e408099563117cb95fd61b761acb3e" "setsum_p_def";;
Hashtbl.add pfghfknname "9edbe245b62c3afd467422d8d7d68805a9556871be26d98031aaad0eecdcd728" "tuple_p_def";;
Hashtbl.add pfghfknname "602ffb18d1bbc5843fe462e731b3f73a5a976ee46e9da6bb6b40d8509a333aa5" "Pi_def";;
Hashtbl.add pfghfknname "659e82bb8ae88e2b04e50f651d5446a3fdf84711bbf57106c58d8bb717cec709" "setexp_def";;
Hashtbl.add pfghfknname "12451cb2963ac437754f119fd700a4c871292257bf373759b7bd92287a0143c3" "Sep2_def";;
Hashtbl.add pfghfknname "a185fe1020a787ac3f5fc232b2cdb281c3c8d79b3befbea0c4edf43a97623f29" "set_of_pairs_def";;
Hashtbl.add pfghfknname "35ddbe41ccf8d636bb7be09d378ebbeafa96ab247fbb22d61de52fb2ae8f7d2c" "lam2_def";;
Hashtbl.add pfghfknname "ecbeeaf0badaae278dd637ce4637ef85208490fc1eae35c0e79164f3f5b9fdf5" "PNoEq__def";;
Hashtbl.add pfghfknname "5b5879bfb5f5ab380758f631c5dda71fdd77a20870fc0d9ff94c46e173ce9d04" "PNoLt__def";;
Hashtbl.add pfghfknname "c5ca53a6adf517d6574675abbb5f9032ef9ad79b9b8714203f092faaa8ba0887" "PNoLt_def";;
Hashtbl.add pfghfknname "82640bea0f55be344d1e16e89f41f32887a7a47d8ee55bff12f5481d83e942b5" "PNoLe_def";;
Hashtbl.add pfghfknname "7fca94a5974ea12bc67f55a16f67dbaca0d58af6648a5661c36b0e6c572cd896" "PNo_downc_def";;
Hashtbl.add pfghfknname "f030a2d2c44eabec7a4cc7446328bc1194822bd4441b8a806ebda667f414ca66" "PNo_upc_def";;
Hashtbl.add pfghfknname "d20efd6ecacb0cb3079f2127a08724476d4eabf3507c95ed5457caf478e82dc0" "SNoElts__def";;
Hashtbl.add pfghfknname "ec74e0e0b43759c2e284f91d3fc896bad3dfb5b25e731877ccefe7c66e001835" "SNo__def";;
Hashtbl.add pfghfknname "89dc652e8e86a81513b682fa88ff665d5c7ce80f8e965051c98997954b367bf9" "PSNo_def";;
Hashtbl.add pfghfknname "22071e7ec3d44038501eae7b845bd1fe4144e084a8985f9cc2d5dbdabd2f5592" "SNo_def";;
Hashtbl.add pfghfknname "5d04957e5d383065e03c72e5f6f126c0dfebf4f039551609c1be24d94cf2b447" "SNoLev_def";;
Hashtbl.add pfghfknname "95d047b09ce188d473c5e7498669c05fbe6529fc7483ec34f11eec9f9eb9a361" "SNoEq__def";;
Hashtbl.add pfghfknname "89bdea0aa616a43a477ff5a2b8f8d93ffd0e81538b14f1e3acf287a190a89ddd" "SNoLt_def";;
Hashtbl.add pfghfknname "cbb07c2a4d089aafb664d96f12f4bb4d73181a7d7b6079750a8b1f00ffa3b378" "SNoLe_def";;
Hashtbl.add pfghfknname "a9f7dddd1e068a3c747980f5d0555f105b6f79bf8350ae9f2a610b1ad88118a6" "binop_on_def";;
Hashtbl.add pfghfknname "bf9e3955698cfdd47596df01c71e1cf03ac8e02f35e01b8b2560828b931bf3b6" "Loop_def";;
Hashtbl.add pfghfknname "72fb3b732d20df7b10a7d845367a5d455a600ffaad98f8e89af0d369750d36ee" "Loop_with_defs_def";;
Hashtbl.add pfghfknname "85ddba6a7609c822f37b453fe65991931570c7b63ba128a986dba37ced7bbcf1" "Loop_with_defs_cex1_def";;
Hashtbl.add pfghfknname "047aee660e1a13eb74426c75dbc197f437b5b8efbb63d3fb3c4fe31dfaa6eb61" "Loop_with_defs_cex2_def";;
Hashtbl.add pfghfknname "822a836127ce60e878d67d66e2b4a46ea0b813f9f55cc8ff810951d073cc1dbc" "combinator_def";;
Hashtbl.add pfghfknname "aa9ee728af378f05d9eb99b00d097d784ce116396b9b970397b723582e0352eb" "combinator_equiv_def";;
Hashtbl.add pfghfknname "77dc3318ff617828477b0a91f762ed88177211d91054f972756c52eddaba4efc" "equip_mod_def";;

(** Egal theory **)
let pfgegalprim : (string,int) Hashtbl.t = Hashtbl.create 100;;
let pfgegalknname : (string,string) Hashtbl.t = Hashtbl.create 100;;

Hashtbl.add pfgegalprim "174b78e53fc239e8c2aab4ab5a996a27e3e5741e88070dad186e05fb13f275e5" 0;;
Hashtbl.add pfgegalprim "73c9efe869770ab42f7cde0b33fe26bbc3e2bd157dad141c0c27d1e7348d60f5" 1;;
Hashtbl.add pfgegalprim "e2a83319facad3a3d8ff453f4ef821d9da495e56a623695546bb7d7ac333f3fe" 2;;
Hashtbl.add pfgegalprim "844774016d959cff921a3292054b30b52f175032308aa11e418cb73f5fef3d54" 3;;
Hashtbl.add pfgegalprim "2a38dbb37506341b157c11dddf8eb7d8404ce97eb50d5e940b23d5094ae39d70" 4;;
Hashtbl.add pfgegalprim "b1b8f6f9d4d6136be8375ed2faddb54df84cdb3018ec6bd2ac07b2c25d3d8af8" 5;;
Hashtbl.add pfgegalprim "5a50bfe3a33a99c34615616f54f10cc2df28717bcf140147a4c61b78529a8e94" 6;;

(** Mizar theory **)
let pfgmizprim : (string,int) Hashtbl.t = Hashtbl.create 100;;
let pfgmizknname : (string,string) Hashtbl.t = Hashtbl.create 100;;

Hashtbl.add pfgmizprim "174b78e53fc239e8c2aab4ab5a996a27e3e5741e88070dad186e05fb13f275e5" 0;;
Hashtbl.add pfgmizprim "73c9efe869770ab42f7cde0b33fe26bbc3e2bd157dad141c0c27d1e7348d60f5" 1;;
Hashtbl.add pfgmizprim "f55f90f052decfc17a366f12be0ad237becf63db26be5d163bf4594af99f943a" 2;;
Hashtbl.add pfgmizprim "844774016d959cff921a3292054b30b52f175032308aa11e418cb73f5fef3d54" 3;;

(** SetMM theory **)
let pfgsetmmprim : (string,int) Hashtbl.t = Hashtbl.create 100;;
let pfgsetmmknname : (string,string) Hashtbl.t = Hashtbl.create 100;; (** This is empty, but could be set to use the same names as in MetaMath. **)

Hashtbl.add pfgsetmmprim "d58762d200971dcc7f1850726d9f2328403127deeba124fc3ba2d2d9f7c3cb8c" 0;;
Hashtbl.add pfgsetmmprim "73c9efe869770ab42f7cde0b33fe26bbc3e2bd157dad141c0c27d1e7348d60f5" 1;;
Hashtbl.add pfgsetmmprim "e2a83319facad3a3d8ff453f4ef821d9da495e56a623695546bb7d7ac333f3fe" 2;;
Hashtbl.add pfgsetmmprim "844774016d959cff921a3292054b30b52f175032308aa11e418cb73f5fef3d54" 3;;
Hashtbl.add pfgsetmmprim "2a38dbb37506341b157c11dddf8eb7d8404ce97eb50d5e940b23d5094ae39d70" 4;;
Hashtbl.add pfgsetmmprim "b1b8f6f9d4d6136be8375ed2faddb54df84cdb3018ec6bd2ac07b2c25d3d8af8" 5;;
Hashtbl.add pfgsetmmprim "5a50bfe3a33a99c34615616f54f10cc2df28717bcf140147a4c61b78529a8e94" 6;;
Hashtbl.add pfgsetmmprim "d40ff093c97ce2dcd7283bb239ee6c9fbc61ce9d7c8263cb74b4bea83294fb72" 7;;
Hashtbl.add pfgsetmmprim "58b567ebc7e5082e1c61f8b0fa2e333e35ca293d56bdc2f8691ab8a06e2bcf42" 8;;
Hashtbl.add pfgsetmmprim "beb057fc4ca37210faaa4bbbe5d04208f898b08f71da35d5985417518a6c3709" 9;;
Hashtbl.add pfgsetmmprim "eab77d60373901b82f671c52b4ccbd564c24b22cbbf9c17a9db3cc519db6b1e7" 10;;
Hashtbl.add pfgsetmmprim "478bc044fccf0b83f84c21543a892da05bafc63bd5f2ffe56995180eae306faf" 11;;
Hashtbl.add pfgsetmmprim "0f42b49d80636c935528da6a6e9e9b8c8ad68262eb0e0513a4e9704ae1c033fb" 12;;
Hashtbl.add pfgsetmmprim "c8876962b8fe3565d27bfa2c7b30e5ef20bcae68ba646c0b2ee698ff6391ff54" 13;;
Hashtbl.add pfgsetmmprim "d87d1eab5b216be747b9b5c3e8f8fbeba0690369f657ee1ea210bc7d8f19b044" 14;;
Hashtbl.add pfgsetmmprim "def52f9c3925bf85ec33e19c500fb196124932fdd8131c25575200ed34cef91f" 15;;
Hashtbl.add pfgsetmmprim "cd81b02d1d93bdd38a5bc8748d59c48f1716f610fc11915ea56b43ec18167da2" 16;;
Hashtbl.add pfgsetmmprim "0d7023ef48adc7d6fc80c1506147a04cddb9046b8c9aca1f0a8172114c8470c6" 17;;
Hashtbl.add pfgsetmmprim "492055c01a06a0131cb53c41ccf1baa1a806f17938de1d7d082c2fb1c79b6a39" 18;;
Hashtbl.add pfgsetmmprim "5f03444a734d2d354c4f6af2307a4a35f31ff0b0983212cd27c2e5e2be1afaee" 19;;
Hashtbl.add pfgsetmmprim "8c73605ee638f59f8d4e61c4d37aac7b1b22425aed4ae4ba682339c8437681d4" 20;;
Hashtbl.add pfgsetmmprim "c4d47f9085a5494181dac05a5e48ede42de35aa2d2bea97803876e1e04563dea" 21;;
Hashtbl.add pfgsetmmprim "eda73ede2e55cf1a2c66cac7568282c20e5698acbc294aa9deb97b168f5c63dc" 22;;
Hashtbl.add pfgsetmmprim "087aa8785b80bd713e950b0fcd3964d911eff345487ff3ac9d1fae51a8d4f6f2" 23;;
Hashtbl.add pfgsetmmprim "2757c2cda6e298adc8772db1c3ae10c72b5cde4050a938a87b7bae7e6996c4d8" 24;;
Hashtbl.add pfgsetmmprim "6be52bb9bc697ca3e8be9f1ee9683225d94dfd128ffadfa7b385254cef283c57" 25;;
Hashtbl.add pfgsetmmprim "7bfdf1df3f0dd295b636b227f7e72169f731108fcd2c0be805eb736e33540161" 26;;
Hashtbl.add pfgsetmmprim "a07eb818df2f97de0fcb5dfb20faabfcc06696d7855b6471bb436c0dd9bd3688" 27;;
Hashtbl.add pfgsetmmprim "9672619ad493493a55bea9b1687b83bbf2e2b19ccdc99c97a92d62987ab9c220" 28;;
Hashtbl.add pfgsetmmprim "538b8c03dd02f712097a16f2b8366cc1cf081fcc35c058c34411dbb9646e325b" 29;;
Hashtbl.add pfgsetmmprim "31e44f7bf85251192ecd7d7dedbb1c86cacbad46389c99302cc4b5376e94270e" 30;;
Hashtbl.add pfgsetmmprim "f8623c820431b705346936434e870709e52fce0113677153c147f0368a95c347" 31;;
Hashtbl.add pfgsetmmprim "01b14287e6f4eca4eb00364fc07a7b34d75f2790da6fecb98cd1dcb222b03dfb" 32;;
Hashtbl.add pfgsetmmprim "dfea97e81829d4f83068f15d8df1d518c686556c4b6bc527ea500e6d0d0e049b" 33;;
Hashtbl.add pfgsetmmprim "f0bc62defe350d0b8308df66d14367caac7a21d93bb4cae5345a872da8f32a42" 34;;
Hashtbl.add pfgsetmmprim "5faff40e03e53b110d9c0b852b479297c202d8f2e5447e553601b5bdfb009d9f" 35;;
Hashtbl.add pfgsetmmprim "33d9ce60a36bc931564883d60927696ef7f1b630b01127eb67142bfb7e2cb686" 36;;
Hashtbl.add pfgsetmmprim "7dd167a2c0d449d94a22a916f3e623fef1a9c59036b8d8c35f541513a8f3120f" 37;;
Hashtbl.add pfgsetmmprim "780d2ffa0fd63a252a5b3df4e4327c483b712cf4804284518500603e144af07e" 38;;
Hashtbl.add pfgsetmmprim "7689a558278fd7c51a708eb1a1ba503efe06a7299459b8cf13aa809464cfbc43" 39;;
Hashtbl.add pfgsetmmprim "73d6400416fcebaf9ace9b899b071a69747e9413680f7931a16c0fd27f5e9c47" 40;;
Hashtbl.add pfgsetmmprim "43b4a7a3c9a84debf03abe04f76f705bed60a5543d72f56517503dafe0fdfab1" 41;;
Hashtbl.add pfgsetmmprim "334ea8344945870e1fd9c56d2551c5389082753d910a3e49ab4fc63d7f77f103" 42;;
Hashtbl.add pfgsetmmprim "2f055184ae4a80df19caeb631e63aab477bcb3ca14c26d9355cd6a184c7ae217" 43;;
Hashtbl.add pfgsetmmprim "5abd4f29031d757bfa9f06799c0d3edaeefb1296e78d991b3c224b4dcb1994d5" 44;;
Hashtbl.add pfgsetmmprim "e1cd0842f147de8bc6da01dd8acbd51161d90e2606e14acdfc6b5c60f53655df" 45;;
Hashtbl.add pfgsetmmprim "d96a9323b7e59d28c1cfa3f0652d4bae32912a58803677cabcf68cf64ed329dd" 46;;
Hashtbl.add pfgsetmmprim "251bb8864a7ee1ae024b04c668a57936092336e06629685fc6368d98f73a5416" 47;;
Hashtbl.add pfgsetmmprim "d54ea4ec78c1e8c1793f277fd9225231ab5550f31bb6dc603024bafbd51cea3f" 48;;
Hashtbl.add pfgsetmmprim "4e33c3eedc62d40f1067685b21f21a8bb21be5c8bbd3e5469c9e6a611f58f277" 49;;
Hashtbl.add pfgsetmmprim "68e685d84219e13e9d0c1ba61468fc71f1675ac75ffd8b81cf49f65cb01a018a" 50;;
Hashtbl.add pfgsetmmprim "fc99600c2e9edd0d2930b0aaa005668e670971c711b3124e7e8248a69cc9ee52" 51;;
Hashtbl.add pfgsetmmprim "f6c93846846640274ccd016bd35c2fae03bde49d62860fcd8ca3b75da0980409" 52;;
Hashtbl.add pfgsetmmprim "7ab34d55207b0a9aef0aa063cb420c1f20c4fce38480e807d9b5d7e345369b21" 53;;
Hashtbl.add pfgsetmmprim "66c81aec6c86035de94a6c732e4a180ccfd81185a4b3cfaa744452d1396b2005" 54;;
Hashtbl.add pfgsetmmprim "4c8f76be113856e4f9365807d0296bb1dbe1e315f0d42b75bfda52a58e82ed6b" 55;;
Hashtbl.add pfgsetmmprim "239125be2f232bea85f255000ac635c8ac48633043a5ea39ca8ab62d76c0f573" 56;;
Hashtbl.add pfgsetmmprim "3975d41a297a685caaa11dd7948b098fe0b3fd727c0912bf8d357e6001c1e76d" 57;;
Hashtbl.add pfgsetmmprim "c9b51ae4ceed6d284ac4b89af1cb6a16197ca3972faa0c9b586ac6ae5603da4d" 58;;
Hashtbl.add pfgsetmmprim "5869884d87bb4de5bedef0df7a8794d7bf08542fa57eddaf1bd333749d8e1044" 59;;
Hashtbl.add pfgsetmmprim "6b16731783e687bf00d1f3397394e561c857fa8b52aaa6704d2c0afc9afbca7e" 60;;
Hashtbl.add pfgsetmmprim "cc1fd37efffaf0a1b2150564462a485fce096b45956b5f3e71c8f9847ee4e1a9" 61;;
Hashtbl.add pfgsetmmprim "bd639e2125657d5bde8b46468987be2369413d9ce64c70fed0d3340ad6b31d99" 62;;
Hashtbl.add pfgsetmmprim "d725dde1c77cac542d78af628c2a0bb1b80291b3ee099cf3585e112a2bdeb56d" 63;;
Hashtbl.add pfgsetmmprim "31c7408a75d7db0c3efd99bef0f03675595884290ea9f89737f85c5119147bb2" 64;;
Hashtbl.add pfgsetmmprim "c6357b6c6730cdd4cab3f49dcb67fa9e854354bacc2308c9f32ea17048b72a2e" 65;;
Hashtbl.add pfgsetmmprim "b9abbb89edfc57f93fd00be10678155b188c2d685161f5b24a4fbad41867ba1f" 66;;
Hashtbl.add pfgsetmmprim "e1fb7cb96f25856a49a87ed6615caca0733393e60f64fffdf586642630e7dd92" 67;;
Hashtbl.add pfgsetmmprim "6b4cac0a4819cdffecabdeb0527a0426227a74f1371378da2d9754f7d60d4814" 68;;
Hashtbl.add pfgsetmmprim "9fe8664da622068f8fee03438618c441462773cffc630bb3b0d526f334a000bd" 69;;
Hashtbl.add pfgsetmmprim "c473372584153be9fba47a99b659854bbe9e860ec8a3a59276c4bf3f1dee7eb9" 70;;
Hashtbl.add pfgsetmmprim "04d790ad466f35be20d99fdbc1d22fb73af2766743a4ad8edb2f0a0639736d73" 71;;
Hashtbl.add pfgsetmmprim "e428697ec32fd9740d99a4d0dc43a45903fdf8017916d6bba09d938c4fc3f4f3" 72;;
Hashtbl.add pfgsetmmprim "b6938a6ce3934cd4188003051a9b8334f08b8feaffc98918af26f7875b84c682" 73;;
Hashtbl.add pfgsetmmprim "eedb49cf5a55fc1eda9f7290d7901e27b90b99e18f8d72de9120011fde4f4b5f" 74;;
Hashtbl.add pfgsetmmprim "06459a9fcf3493ada1e98c97ad92fa65849377c8ba25a2bd66493edaece5994e" 75;;
Hashtbl.add pfgsetmmprim "ef2c2cf5e9612132f65d4e3acd10816608bc78a3141967b89b4b8bf1a7f58af6" 76;;
Hashtbl.add pfgsetmmprim "7d203bb2a7daa2bf5b17d0bada3336e405d0b47098549a7f2f92c7b7827aaf0c" 77;;
Hashtbl.add pfgsetmmprim "4da89f044dbd20cce7379ec99b10f1d606af925340b22002ec6f7195c76418ec" 78;;
Hashtbl.add pfgsetmmprim "ce1f81f7615521a82afd7fdf1cbcb2e12c0aabd6069520aafbe5ca9572168781" 79;;
Hashtbl.add pfgsetmmprim "b2cf62010aefbf1dbfe010f0ee794a73b9cf9a5a8397b7e40f9c65677b15954d" 80;;
Hashtbl.add pfgsetmmprim "fa6b66b308044ea6ae8d47bed4eb632e61d5113cce10882c43a5a20db0a539b6" 81;;
Hashtbl.add pfgsetmmprim "139ab9b56b07d41cb35b8ba08ed2b36ba0850ea09fdc8043214a2f4296503ba6" 82;;
Hashtbl.add pfgsetmmprim "8ad96657111aec51dda36fbe2939c87af0b8526833c4834a9905db2e20e2ac33" 83;;
Hashtbl.add pfgsetmmprim "2506ed91c72dee44cfcdbf92bb04cb419736265661dfe14f6e9a59dfffde26f6" 84;;
Hashtbl.add pfgsetmmprim "5a7d6ff640e4e4171af2b78759fb5024fe426b1cb3e5dcc042933599ee6433b3" 85;;
Hashtbl.add pfgsetmmprim "65c9a5269e7686ec0db772628d577aad9c68e7838d969dfe739d6ed31901f872" 86;;
Hashtbl.add pfgsetmmprim "723eb0a34747eb7817c71c892867e619c1b13b64dd2f5f3aec325f44bff98159" 87;;
Hashtbl.add pfgsetmmprim "3e11dd89a5117e6875c533880d0775c8b446e4637033a50c515579d2d12f44a3" 88;;
Hashtbl.add pfgsetmmprim "eb1b9f617bf11d36e331b6180bafad7ec11dad6fd919f0679303e7efa7d0a8d3" 89;;
Hashtbl.add pfgsetmmprim "19141328f2cf154059e8176d08b6b80de23e2a370efe6fed3f07c84a04be7212" 90;;
Hashtbl.add pfgsetmmprim "68598ea2de4c2f252afd24f1dbd18731644c6f62f2fa7aa9bc3f6d2bbedb7cea" 91;;
Hashtbl.add pfgsetmmprim "362e751e30d04f4731719f9f1b5572ea7c286623ae42d15eaa07947f75e92de7" 92;;
Hashtbl.add pfgsetmmprim "2dceccc1bec3d059cd68d6b69d48fb1c5e63c1fd953e364af040623398e7d23a" 93;;
Hashtbl.add pfgsetmmprim "0e585e3da048dabad1bcbb51934a982f34ca4a234c7f0ebd6a9fe15a19144844" 94;;
Hashtbl.add pfgsetmmprim "16cb1d7809f7023be6550de7020622ac686598deea21a9380612ed560a0c179d" 95;;
Hashtbl.add pfgsetmmprim "89a9724a96664ffba46e5f3c3ea6447a9e14e577fe6da3e1af6767f773dc3cbb" 96;;
Hashtbl.add pfgsetmmprim "b3c32d524e4bf255274b27bac94bec6531416ddd586e68f0bb4cf8a3498ed45b" 97;;
Hashtbl.add pfgsetmmprim "cfedbf738f1db68a18c8c29d324c7351a28f9c48730bf4658f3eec79d5129c57" 98;;
Hashtbl.add pfgsetmmprim "5e2f97d4c98a08f9cc82ea68a1115059781f47db3956c9780ab700d4ef61218a" 99;;
Hashtbl.add pfgsetmmprim "9e404a3aea2fe1b78dd55c4406e17860f108aeb7fe3ce74a054750569b7fb7f0" 100;;
Hashtbl.add pfgsetmmprim "8776bfbd83c2e36050f0a33f9d06a18ff05fc544dcc39456cb496bf5f9d20936" 101;;
Hashtbl.add pfgsetmmprim "73b2a679725938ffcc6db0093c95cf5d7499e8ee9725cd4870e9882e14fc331a" 102;;
Hashtbl.add pfgsetmmprim "cf2931af6ab0b59cc20e27cd89b34f5aa704b79cdcc526355238c696b039dac8" 103;;
Hashtbl.add pfgsetmmprim "895b4d3fcbd51cc171165f29d6c39de58867152a675fe8b40240144f77b98f95" 104;;
Hashtbl.add pfgsetmmprim "08dab7c277e4e2dcff656297eb038eee517b0f2c3ddad12d414a6d908f0b9d3c" 105;;
Hashtbl.add pfgsetmmprim "83a41d232c0208161c7237c4a044622d406e91396da37a43d151d740a2b85708" 106;;
Hashtbl.add pfgsetmmprim "5efaa552667f58d7c9b05d0d6476f331237725e12bbd727805352f8b7315b3c8" 107;;
Hashtbl.add pfgsetmmprim "86b1cbd1c5733475139b336f36fff52f2a0789e2e351f408f107a21516272a32" 108;;
Hashtbl.add pfgsetmmprim "3002a66bdf6927d81273e52a00bf84841ff289a2f4e354a4f67d8515b49c1065" 109;;
Hashtbl.add pfgsetmmprim "01a1c4b8f3c30c02da2527684fa0dfa761460cc7bc08fd00a4afdcf156138002" 110;;
Hashtbl.add pfgsetmmprim "b75d12ad31e36ced8cc9d89b139cdfb1aea22702d907359a97b5d2243fd088a4" 111;;
Hashtbl.add pfgsetmmprim "e8c56aa9105b9df55018d28cfe5a76ad7df661e6af45b10af34a43abe8b32df3" 112;;
Hashtbl.add pfgsetmmprim "8da8d56e93077afc59209d759a8277336df2f916a3ebacc2710b930a812d0577" 113;;
Hashtbl.add pfgsetmmprim "dbf7b61259fba7a534860d29d5fd5cd4bb83afb5e9510c11c1782c398df27efa" 114;;
Hashtbl.add pfgsetmmprim "421eda20ae912cddac4a85dbf6960f6f0692b4d457757e904a2fc4cd370c72c8" 115;;
Hashtbl.add pfgsetmmprim "5630a9b8a62c0816d9dee08cade54b52bea3f0d26d8ae7867015af6c5f5b030c" 116;;
Hashtbl.add pfgsetmmprim "b7a59aa4bef51a90895905f1721ad236773c3db0247424203041ee0967967898" 117;;
Hashtbl.add pfgsetmmprim "339260f77cc9d0b120788fa27295b51b8bf18502b074b7bd6328087af90b227d" 118;;
Hashtbl.add pfgsetmmprim "97ae8e2f36ee1edca3065a87125dadc40b09a7963d0c8c545de68b70e994b1a5" 119;;
Hashtbl.add pfgsetmmprim "608b1f6732d22efbc51a4d758aa927750042be3db92319321a581781d1bfafd9" 120;;
Hashtbl.add pfgsetmmprim "8e6712d4678152d3d58224917bed80990617d68037bc6b444b3b3f613d84ec2a" 121;;
Hashtbl.add pfgsetmmprim "868f06e2e270b8a3b65a792f731bda1f7c208ff2a5f794d1d180508640baa43e" 122;;
Hashtbl.add pfgsetmmprim "dda458ceca8917faeb5033a71e9cde0889fd63159f03edd097a1b4e8989412d5" 123;;
Hashtbl.add pfgsetmmprim "25c86d19841e191f0db645b677f2e04eea9d5db5715d434772913115cfac53f1" 124;;
Hashtbl.add pfgsetmmprim "e1e2ccc9c7dd04acf4662a860404742d87eb32af6ab616d4d93eb64c62e84768" 125;;
Hashtbl.add pfgsetmmprim "280f761ce57612f2db1a86abf43bd74aa3625bd68e97d863a68de812442f7d81" 126;;
Hashtbl.add pfgsetmmprim "87d02717f138b8881a09cc1278ed8f6f04cc9698542334c5767bed7fb8e313b5" 127;;
Hashtbl.add pfgsetmmprim "40ab2ea08c825f331cfb905b98700a467f1fdc88d8a2f34dd1e2a5af81d4fd07" 128;;
Hashtbl.add pfgsetmmprim "99c85d69e687c2b708e9a75900ada1c2aa02052d4ef17bf6af985971697eb5e3" 129;;
Hashtbl.add pfgsetmmprim "a98d70057d96f2edb85615ca6d259f9a58234c01e02dbe8addcf2fcfa4938817" 130;;
Hashtbl.add pfgsetmmprim "4f5f81d1c63dbfb051b8235b14ed648641a7130db2491f76bc6d4207ffb8dba4" 131;;
Hashtbl.add pfgsetmmprim "adb86e78d1e91654ec08f68283a45c62de60ac064dd17ea1b477d35f6ecd67fd" 132;;
Hashtbl.add pfgsetmmprim "409de4346821d106ad32cbd826111793762bdd2e93e05fc09df43136689cb4fd" 133;;
Hashtbl.add pfgsetmmprim "c2d9f14ffbdffdf059c7c135c3f031834acee96701dc8685736d1b5b06fa303f" 134;;
Hashtbl.add pfgsetmmprim "afaf8292b03cb6f022bfef9e094db948c3a723355753490f8daa0bd24af2f544" 135;;
Hashtbl.add pfgsetmmprim "3e46286fb932d0cb88df270aa3d794b373f73d110d5bd9ec9c54022770e87ef6" 136;;
Hashtbl.add pfgsetmmprim "596745353bf209fc9a3e08bb82f5773fff37eefb00fbb6d09e44f6316925b45d" 137;;
Hashtbl.add pfgsetmmprim "5116bfa6fe9c3d0338fa1fe8a2072b76c53f359e9907d53e3d5422c2907d90d0" 138;;
Hashtbl.add pfgsetmmprim "a9434e28ecff3d5b9a117d1eca6d6f097b6c1bb8343b33d1d1fd5c1b8d4f1ad9" 139;;
Hashtbl.add pfgsetmmprim "cc5ab368f9011332d6661390d944dd78b2a8153838135b83f60290c33598ce68" 140;;
Hashtbl.add pfgsetmmprim "90203f43e5cd9a6151503f14dea58d5d49188f4e0ed2f01e8f516558221affc9" 141;;
Hashtbl.add pfgsetmmprim "7fd5c34108ae1bbf499ae4759975076bc78997f16c038c8b06b4fe5e898f1f6f" 142;;
Hashtbl.add pfgsetmmprim "3fb89ef9c9ccd8494a9477fde80afd39ab7b5162c173d52e987803df8e199624" 143;;
Hashtbl.add pfgsetmmprim "cd78cc317f44ab8e6e355a4f530eb7221e9bb4eca73280fd540a04a9e9d3310b" 144;;
Hashtbl.add pfgsetmmprim "e2b8be7d550830dc9c50b868d87aa5292eb27b3aa55ae9eb7aaf539a96b49b95" 145;;
Hashtbl.add pfgsetmmprim "cdae52a0eeab6042a3bb5ca9f67d78a9d625d5754521cf2b253ee490253f98de" 146;;
Hashtbl.add pfgsetmmprim "bea1fd82f3782bfaa6e5b73e2f9215453966282235a7b655c83c11b6d4e2056c" 147;;
Hashtbl.add pfgsetmmprim "34ff5a522243a8ace1f0e4dc0a31738b69157554de1705ba54e5d36e6e85fc36" 148;;
Hashtbl.add pfgsetmmprim "1064ccdbfd7e99decb09cdb22914c93cfbb8deb24add6b72b5cd3dba808edf47" 149;;
Hashtbl.add pfgsetmmprim "4b786c4158c478022bdf2a76e7603da349036638a2d49b9af37e0054165e905d" 150;;
Hashtbl.add pfgsetmmprim "6973e1641a849c4212be6b9633df66a1b0262e6abf1e8436084fb4017c1b0565" 151;;
Hashtbl.add pfgsetmmprim "c112c9486d31cb18aca4db2d91468ef61289a7bab1c7337092b6bd676269996a" 152;;
Hashtbl.add pfgsetmmprim "6bc9e73d946e4e6313e3bfa555c9a05ec7eacbbb8bd720fa2356db4c7a8a64b1" 153;;
Hashtbl.add pfgsetmmprim "8cdd1f517bf3b4ffe94022c3f8521dd0ead2d0104feb405749b382cbb095cb93" 154;;
Hashtbl.add pfgsetmmprim "cc6bec136fd2e56c56ad033dafb4861a2df80f681daf639962167c86ba0adb3f" 155;;
Hashtbl.add pfgsetmmprim "cb644120eacd98b04e315a79da029e0174a21116304520f69024a88b33fdc8ea" 156;;
Hashtbl.add pfgsetmmprim "634abc0d65ad60b03227df09175d58b7a3444898ef2208c05901b2d60ad58eca" 157;;
Hashtbl.add pfgsetmmprim "ab9a218a2c846e11fd6abbe35e9c88abfb440189d739e7549a930664d446c28f" 158;;
Hashtbl.add pfgsetmmprim "53325b462529cc06bdc9f782c1dbcc5954098cbe31e93135e6c328b84c1f10f3" 159;;
Hashtbl.add pfgsetmmprim "fbc7d734f0e49e487bed927d9cceac2227ad09e23852b45c7e173ef61cce45a2" 160;;
Hashtbl.add pfgsetmmprim "75176890da3bba4199a36bae051d87c67c2d97dc91bdfc26326c2f8fa9d1e379" 161;;
Hashtbl.add pfgsetmmprim "a784dd5e2c5e4541872772e84a1c53905ee3c05f90242f11e9ef9887543f0799" 162;;
Hashtbl.add pfgsetmmprim "97d9bd480bb14fcfa87248fce96b34ce7d6076f1374e75e84854ddf7b5ef827f" 163;;
Hashtbl.add pfgsetmmprim "1b13848d77bd117aa66d525f1db90c4d626d342975a49c5f9f543bbf820d30fb" 164;;
Hashtbl.add pfgsetmmprim "1aeff56c619e5dfebc2f012bfab6a46a3fcfa9b54f5c4caf0465abf08b7a1d33" 165;;
Hashtbl.add pfgsetmmprim "7e0064bdcab1b09f1e469a4f386e8688d67e4c2ed59fe0da20d4e5bf4e6989e3" 166;;
Hashtbl.add pfgsetmmprim "9abed591cc14ca27d7b207efb56b296f89b8c6c987fb6e7aba139d944586428a" 167;;
Hashtbl.add pfgsetmmprim "566a2282ad95c63f39ee96be87f64583b5c1ded9ab1021b4b18ca9f508d6a543" 168;;
Hashtbl.add pfgsetmmprim "3f55219711f9822f6db5501f1d6f9584df1baa603ca7aca6a5be86e997480f5a" 169;;
Hashtbl.add pfgsetmmprim "079e648377d0932524c24d1c2d2533cee9fab16afe16c1b971a765c30e7d00b7" 170;;
Hashtbl.add pfgsetmmprim "d41c778a1e2c87a4acbee79c27ec757f7f41fa815255b5af0b2423ec25b82947" 171;;
Hashtbl.add pfgsetmmprim "1417eaa921795c45b07e75fa140112b452d163b20eb65b9b71c28301adc7e1b9" 172;;
Hashtbl.add pfgsetmmprim "f90d5d36013ac43b982851aeebf8172e581759d827683e280731c4edf8208b44" 173;;
Hashtbl.add pfgsetmmprim "cad6f5f375c926e8e7623c6c446494eed4c5921399896eb176332f53fef52c50" 174;;
Hashtbl.add pfgsetmmprim "0540afd69f72e49367b5f7f228ee59a55b94819ed6adea1efe9fdec02b28f654" 175;;
Hashtbl.add pfgsetmmprim "4abbeb7f039411ea24cdf990e785a226ed4cd7c250016f095ae06d936d5b9873" 176;;
Hashtbl.add pfgsetmmprim "c5a7b022f38a7000cfd2b65185b04ecb2a28225202312644175de886b378da51" 177;;
Hashtbl.add pfgsetmmprim "5142fac5ca0d6013299cce256eb74c7d0e42042d81a205a374e21a3a6871dc00" 178;;
Hashtbl.add pfgsetmmprim "3a14d729f5e23d69f768a1e285bc17e2879bdf9064bde8b08ca3f397e737a79d" 179;;
Hashtbl.add pfgsetmmprim "1563f6f24e4c9ece28d43f0b44dd151766bf14a4dbb4e6fa7b6d0c89d4a01302" 180;;
Hashtbl.add pfgsetmmprim "31c7085f504c11d9972a3bbc348bc61de4e6545ad3f9bdf64e2f1ff2205fac5c" 181;;
Hashtbl.add pfgsetmmprim "288f78031d485d9ef67b66bd34b3bce6fab075823771f715ab41be47e100f23b" 182;;
Hashtbl.add pfgsetmmprim "96198e166d88191091d2059d4f1c7208123f49ec0000856b5e6a65e98e2f2c44" 183;;
Hashtbl.add pfgsetmmprim "df824badd2b419f245157c72f1578d16e94557ab05eb0fbd3a451519f6909b86" 184;;
Hashtbl.add pfgsetmmprim "b9f46b579dba7044ba70ee78a6eb96fbcb44b485f3b8dab7d31bcfd0f9fa0415" 185;;
Hashtbl.add pfgsetmmprim "fc4daae6fed26b61329c32f50be639872ebaec0b27d6d0ee8a3f542c917fd3c2" 186;;
Hashtbl.add pfgsetmmprim "46fb101685ab094967e817f2ae838614aa8665149ffee38efdfb4de6fa52ddc1" 187;;
Hashtbl.add pfgsetmmprim "3861951b4ddc7b18004d6fd8a3dd3a12de4c02337311407a30d00d1bf3f115a6" 188;;
Hashtbl.add pfgsetmmprim "561cfc3bcc1ebcb0999bc5721ac05f67cdd5ea0dbe47f1b9f1e6c9285b921d84" 189;;
Hashtbl.add pfgsetmmprim "8fa8cddb8bc046875d7cd9b05935570c56885bdc2da0d74ca05d7ea820465e4b" 190;;
Hashtbl.add pfgsetmmprim "155e921e246399b0e871839d2f6067085514343e7f531596bd7fedbf0edb6b4e" 191;;
Hashtbl.add pfgsetmmprim "f70a8dd690068520273dc31a59dd2e5ab16b85656ed2ea2f22913f5d8eb3336f" 192;;
Hashtbl.add pfgsetmmprim "99e1b4011cb7cb9f7a4015f75e048eb844529f4bab29d173c1c95a5884a75cbd" 193;;
Hashtbl.add pfgsetmmprim "15b6fae1665154c79fc79dfbb4a9848d14ee5e00a7eb3fc8ed8c50980106d276" 194;;
Hashtbl.add pfgsetmmprim "ccf489ca0fc5773d752e1904a694a613a698cf966b00f1526a8fb1f745045dcd" 195;;
Hashtbl.add pfgsetmmprim "c04c84537cac16e673ded5d29798fc655efe9602f1fd40a920a7d83e67d90bc1" 196;;
Hashtbl.add pfgsetmmprim "802df88978a96b0bd9ec08fa550ab740b9528fcdb8d112188e9758afc7e4837b" 197;;
Hashtbl.add pfgsetmmprim "9a836b580a73875a399ba2837ed4e6558d2db940a57d39121e5b91e3da928aae" 198;;
Hashtbl.add pfgsetmmprim "443434b4edeb6ffd8ad1513b26cc663d2a305d167578577580dbfdeb6bf0b196" 199;;
Hashtbl.add pfgsetmmprim "e89fc0292e3179ffadd9bcf68e145794590563b45fe073bdb460a6a24194c9aa" 200;;
Hashtbl.add pfgsetmmprim "7d3bbfa76e7d001f7d37bb71d9e11b5a06ac54cc6774905ea381583a171b5535" 201;;
Hashtbl.add pfgsetmmprim "a1c76a93a612ef76eb31764b3a7febea0930f27f730159a12f92791b30b87ded" 202;;
Hashtbl.add pfgsetmmprim "2c781db8b846d7315e8f485afb109db85064caa1f5cc96395fb55da1ce558694" 203;;
Hashtbl.add pfgsetmmprim "316bb3dd1de77b3dc90db548f7df3484de7381f86d071a182ee2617199e59bfa" 204;;
Hashtbl.add pfgsetmmprim "7fdd81162507efa0dbc0c33c9051f4862e13e6f79b3b5c8ad52426592e95ec13" 205;;
Hashtbl.add pfgsetmmprim "161134b1ee3def253bf2bfa3650c752858b9c09c47cfa6e2dfa0e3aadc010019" 206;;
Hashtbl.add pfgsetmmprim "607a05eb8da659b488d50c097d284da13c4585afa9f5260fd60300ec66479fcc" 207;;
Hashtbl.add pfgsetmmprim "a8f039eae686e62f385800eb64bec1ca837fd1ff57d1228c160fe52c8decb421" 208;;
Hashtbl.add pfgsetmmprim "fb4b38f626a5ddaf2c03850721154946d05d09bf129375c02526a48612dc92e4" 209;;
Hashtbl.add pfgsetmmprim "f73a11e8d76084ec8565c58dc17e50eb3f1de8f394091fad67a0ea9c050bcd56" 210;;
Hashtbl.add pfgsetmmprim "3c5c42d8a2fda74333e4e0910ea788fd87d900000c3a23d7d5c60362f50092e3" 211;;
Hashtbl.add pfgsetmmprim "e459dae15f3db6719b94cf4dfea57b2b32d7acf1a044bbc67609776d7e963950" 212;;
Hashtbl.add pfgsetmmprim "5dc5199f45e6dda917db0d04a792d2266ced7700a7a193c3c9ed5e6ca95dc6ff" 213;;
Hashtbl.add pfgsetmmprim "fb93f15097d574f61ac8d6f02032bb5466bfce53a372baa889c643e6fc8515d7" 214;;
Hashtbl.add pfgsetmmprim "0875942acd509f02975417070ad2c9ffd035d71ec5f99d9f3d5264bbae5cc6d0" 215;;
Hashtbl.add pfgsetmmprim "6040f0acebf03174abf3ab2a538dd255a7ec27a198fefc66e125599d4a9972e9" 216;;
Hashtbl.add pfgsetmmprim "56483cd17001e45e71781b87a5e97669e9670e580727156bfb088fdca09e7cca" 217;;
Hashtbl.add pfgsetmmprim "b90e141f2ca9c116d67c7d5f63c5de4986a4a7081dfbe45abf84673a8706bcf6" 218;;
Hashtbl.add pfgsetmmprim "cbc0297b65d5c5d9c533ac19f20564aa5f54b7c93f3c4ed4dfaa2e5c01a7e2ad" 219;;
Hashtbl.add pfgsetmmprim "18452d9fd31217ffcd86142c707f4ec56a78348143b8e76a55cc67f05884724a" 220;;
Hashtbl.add pfgsetmmprim "9fbb4f72334c39eee4887ee370bb15c7be26ee1cdc87b3eb740922d4d6af586c" 221;;
Hashtbl.add pfgsetmmprim "91800bf36214551d765d3935b6813786e54fb3bbde45dd8b7c80092a49796709" 222;;
Hashtbl.add pfgsetmmprim "e07019d69f53df0e98c5288ef70485220f85fddbecd06eae913407b84a1f0bf7" 223;;
Hashtbl.add pfgsetmmprim "6b187c0a8301ebac9ca8fb3c85ed9ae8054b6c5ada321bd7ab7f790d6ddebfdf" 224;;
Hashtbl.add pfgsetmmprim "8b02ddeb73fce5649d5d00475d4e178104feb1bd02b817fd3c26fd047316a2b4" 225;;
Hashtbl.add pfgsetmmprim "20a31e327bcc024067410f98b8c57c90e53d7f4c11e6d9aace04796b6d7d07d9" 226;;
Hashtbl.add pfgsetmmprim "d8912ed45eb19a6c3cce9bb01d2e2d4642fabdb909cc1b877b97d412311905fe" 227;;
Hashtbl.add pfgsetmmprim "d50d8d35584e02a886526ca1f78dd766379ec6a4010008f80bd21a29fe959816" 228;;
Hashtbl.add pfgsetmmprim "5ade6f0eecad08980c177f0f9dd4ed2eec0723187222e4cd87b88349aecca586" 229;;
Hashtbl.add pfgsetmmprim "b47ca0e7785b31914b801c853a376fcfb0328ba32617a12f26db5c9ec094536b" 230;;
Hashtbl.add pfgsetmmprim "0557aca1c58c762640615e46c0960986fea01db63a09356304df72340bfaf845" 231;;
Hashtbl.add pfgsetmmprim "4608df791b7c12255e6633a3309d838e2258cfce6901a61b380cdf3de109a6ce" 232;;
Hashtbl.add pfgsetmmprim "2e557507c46f0a3ad0c54c0f1f77b58f94579d4ef6914f4060a921b9ba28d615" 233;;
Hashtbl.add pfgsetmmprim "18722ce625ed1c84fe624da9b09e4a944e0a0ae376a97e18a14654f21ca1a550" 234;;
Hashtbl.add pfgsetmmprim "e38233e8f2b3b84393af1121551e726e7c64b64bc7032c069a4245400552c035" 235;;
Hashtbl.add pfgsetmmprim "2fdb7ad89d1ee31b2270267a4c230ec5b6e40263bd28e3b9a5a6361baaedf46e" 236;;
Hashtbl.add pfgsetmmprim "5cc41db8de305d3ab5b1389acf5ed8b0bffe1687e510a52c3d532a708814d3fe" 237;;
Hashtbl.add pfgsetmmprim "7edacff0162fc356efbf543fe4801dc34a0edb6568d28baf8e2487d64e0d5cee" 238;;
Hashtbl.add pfgsetmmprim "d85c734937ad7c3eafc91eebfae2577be83da519ed6b87d4af56ef40d092abcc" 239;;
Hashtbl.add pfgsetmmprim "950de0b8403875fb8f63626ac774e1ba0c3e88478a2d20fb3b4d78cc68bdbbf1" 240;;
Hashtbl.add pfgsetmmprim "8c47bb8e6adf3b8071f772f36a3a3048c0e44a87df7ee7564d335e501fbaeef2" 241;;
Hashtbl.add pfgsetmmprim "504f3b01653c5f0311de9b69f103b01bc529a01fd6fffbb51e3a0220ed328ec5" 242;;
Hashtbl.add pfgsetmmprim "03a96f368ae142d59e9118a957e90e7e1355ee3acebcb79a0aaf81e291dfc898" 243;;
Hashtbl.add pfgsetmmprim "321c4f1fba9441f6d9e28e3fc0da6a43009c6c5e86c3f2dcfb89bcbfbe4264bc" 244;;
Hashtbl.add pfgsetmmprim "f93abfaa0e64edaa0a2eb877ca36fe2d58f29dc045e5b9eda5a325fac16ae6d4" 245;;
Hashtbl.add pfgsetmmprim "99ae07541fd75b693d2f34708aad827351b01b541cda607b46a14476d76fc613" 246;;
Hashtbl.add pfgsetmmprim "e1f46a769b4a3ea57f106404a35251a614d4ec37c369dd1d5b4d4e0425d6c8d1" 247;;
Hashtbl.add pfgsetmmprim "d274623d9d8737907490d2dbacb92996f567c777b645c9e22168e52d7ea393d3" 248;;
Hashtbl.add pfgsetmmprim "15b3edadd165c72d107300c4e08455ffc4168a5a34608c20678bf700a81bc697" 249;;
Hashtbl.add pfgsetmmprim "584cbc671270e1b04731b7c0727a868e93aa86d98c0baa6f414ac1c6518ff64f" 250;;
Hashtbl.add pfgsetmmprim "5e655f5a91acf03724627a64aa90d94cca5968080a7abef0a782c974e4091d7a" 251;;
Hashtbl.add pfgsetmmprim "42fd656e2a9ec74fc26c54670e11a6b16d66ec0a4bfe6492eb516c9e723681ed" 252;;
Hashtbl.add pfgsetmmprim "b6af9b1732f49e012ccfe69c8ff7a3efc5fd6e8fecf675a0e5238fe35c68b0be" 253;;
Hashtbl.add pfgsetmmprim "1cf0cdd44ddf97a609a5b45e3bf87bd29476f471c0a9e1fd5d53ab062eb99b4d" 254;;
Hashtbl.add pfgsetmmprim "07e659766348cc4c0e67004100250197fcced17a8305f44193b5249047534194" 255;;
Hashtbl.add pfgsetmmprim "df16240ffe338a1bb23911ba1773053f4687fad8bddcd6f476420321a0665bd6" 256;;
Hashtbl.add pfgsetmmprim "c887a3d4753cd16a8a9dcf10e217d012148f31b1415b98e9ae49ad1660bc84db" 257;;
Hashtbl.add pfgsetmmprim "72d7a205f3b3a7d06cfa3ff1a5dc67b995fc9b6f4865a1cbe6f2af37a01d8cca" 258;;
Hashtbl.add pfgsetmmprim "48d9dcbcfd9248337466c18d4c7e956aabe2e0354b8a63304ce56f59e8323aa5" 259;;
Hashtbl.add pfgsetmmprim "c4dd0f09cad5b41681895d54274820b8e3433267b3af6210ec3226806c0b045f" 260;;
Hashtbl.add pfgsetmmprim "aab41410ca55b6ddf4f7528d4723c696244bd33fb41c8fb18597fcbe8e3108c7" 261;;
Hashtbl.add pfgsetmmprim "c43c69057f7af0bb6c67d0d7106bd03080c0176a16949ae4299b8c62a0608003" 262;;
Hashtbl.add pfgsetmmprim "428fef121d9b4f90a1bbe1c1c4a999ac918f3053ae4cbe9ce5f606f217b98e6b" 263;;
Hashtbl.add pfgsetmmprim "fa6175321e84a0fc396ad322e45de81190b56de7a1bc748ab9191a117d04d795" 264;;
Hashtbl.add pfgsetmmprim "b0496d1f887f6d6426be75e2740b69813628e4088dd018eb9d996fd65e421469" 265;;
Hashtbl.add pfgsetmmprim "23b392c65d6817e072c15eefd8a86aee50e3785090a36c55878f55842bff515e" 266;;
Hashtbl.add pfgsetmmprim "41a9794dac6c666cbf70617186e5c36cb09aa9f2280d67c75488159692e700ec" 267;;
Hashtbl.add pfgsetmmprim "25ec020c676bfe41a735c4cc57b5aeaee367e7935687b08993e89b40dce4bb56" 268;;
Hashtbl.add pfgsetmmprim "a0a8c95e28ed3e122b97ef31e2e3f0e6cad1dda80ab71aa9e4d3127e32d228a5" 269;;
Hashtbl.add pfgsetmmprim "fa251f898c2a65e73e27ba46c00e8d7e4bbfcad9a384e22ef7add11ac1a6a19c" 270;;
Hashtbl.add pfgsetmmprim "76115836588d80466cf55c73a4a0e074ffdd98f51ea28af727d61a4075ab33a7" 271;;
Hashtbl.add pfgsetmmprim "bdaeddf046963f18a1d176d0939d7a41e7e63d839332bec5d5631228122777f5" 272;;
Hashtbl.add pfgsetmmprim "99f12526d84ad4430134f97fde68d5d1b758b372558340dac5d51262aef3165c" 273;;
Hashtbl.add pfgsetmmprim "2c5cba53a98e09bd9f07b88b515d9c3894fe1b0a3550a64c070b66b001e26ea3" 274;;
Hashtbl.add pfgsetmmprim "50033860f67ba1a1775c94561cc8167e4dfb33c70c70b5cbad03a1a83bb4d200" 275;;
Hashtbl.add pfgsetmmprim "6f6510895e47ff22504ad5bdb7f27ef75691629fdac426ed498184f7af5a92ed" 276;;
Hashtbl.add pfgsetmmprim "60c4b43d0540a4bf1ca0662dc67eb38beb1ac3f967b278e7e2ac228042142993" 277;;
Hashtbl.add pfgsetmmprim "0a2196781c72b99b0423995bfa7b3b01d48c9756dc2a7b299b574b2598780c4b" 278;;
Hashtbl.add pfgsetmmprim "d68332cb521fbc39dab28c242092f06d8804534b0da70e4eaa88c801c1518d1e" 279;;
Hashtbl.add pfgsetmmprim "13b885eeeaaf6dd9bc1ec436cd92a80b3170e66186541a308c7fd61d6a2967f1" 280;;
Hashtbl.add pfgsetmmprim "bd10b7b8a5ba136b4d0c65873aba2f10e6a8bd4cd36d53703ca656208eb66728" 281;;
Hashtbl.add pfgsetmmprim "37a4d6b9f088688dbcdff9a36d586d2b3543175948115044f4e19292bbfd8d8e" 282;;
Hashtbl.add pfgsetmmprim "856f418e9045fa669f28bf013e8799c73013ce354824747c548b38024294538e" 283;;
Hashtbl.add pfgsetmmprim "b44085e26606c8ce67a06669310f22a952c208d4f99b9f456300d2e1a765046a" 284;;
Hashtbl.add pfgsetmmprim "7054c4aac7dad82917b02bff9cdd48d11b3d05e25a3a633cba1d4b4e7f0a5843" 285;;
Hashtbl.add pfgsetmmprim "c56e1e7062b84938aa05752c0cc4a6feea17c3ec52fe0854dd5969ca33a05ed9" 286;;
Hashtbl.add pfgsetmmprim "1d73d67d9d6cee80f51a4416a0efad6de80eaa1a72a29654886a99d9b0d25cfd" 287;;
Hashtbl.add pfgsetmmprim "b1e18bfcbf93503725957b154b70e3bb1be135d472ebe07bf4633587cf1ac570" 288;;
Hashtbl.add pfgsetmmprim "353f11fd6b1501d8b8545fbfd3b0e6042a3c2d32533eee7bcc355d7fefb0955c" 289;;
Hashtbl.add pfgsetmmprim "ad3792bb7572ebd279861ae43445d87da555e81dcaf085a353f84c5cd9589da6" 290;;
Hashtbl.add pfgsetmmprim "9303db85cd7e9ed737aa0fa0b499e9d9319aec58c6e8c6c6127afde00be45e96" 291;;
Hashtbl.add pfgsetmmprim "646ff9f9a12d24fc873a3343a75afaefee0596b130f66ceca4b607f65b35cfed" 292;;
Hashtbl.add pfgsetmmprim "b1d5dfd78a4b3fc879ea637534531998edfbaa3752b6c0d5e878d18251d2e20a" 293;;
Hashtbl.add pfgsetmmprim "74b277ebb2151675a0404ce9c21e7373fc98d956f54e499ba6bd9baa294eb2e6" 294;;
Hashtbl.add pfgsetmmprim "b820054347307644b57a166c19deb1d6c81462c39d3879000d1b067e55237636" 295;;
Hashtbl.add pfgsetmmprim "31ddd278360f230d0a1e8bef870b56bc8f5d283775ed80c48cdd567f5da78c78" 296;;
Hashtbl.add pfgsetmmprim "8af8de3033d8349b48bf695819e687852a97bd368501e32cf6e92f249945b733" 297;;
Hashtbl.add pfgsetmmprim "31219c9c9a1cbf4f3ed51ba078ef8ef5fd028538cf32e70a23d9275529529a8f" 298;;
Hashtbl.add pfgsetmmprim "6488e8596b97a2cfa8b27dcc075c60108d5628a940fe8e1a766fa79824760dcb" 299;;
Hashtbl.add pfgsetmmprim "825b263d1a732f0d41f817dedffab4fe64be3130bb8b8be97460c61827e34518" 300;;
Hashtbl.add pfgsetmmprim "a940ffe3167f8d586c548498afdc3a013054b2a53ebb11da729287431a288e08" 301;;
Hashtbl.add pfgsetmmprim "1deca6026a709d2fbfd63eed7fd10d9627f4b65a04e76cf95dc5f389a8abb1d1" 302;;
Hashtbl.add pfgsetmmprim "c139b4966df1f4cbefff96e57a08762932fca4c284ebcb1283625b7984b16fba" 303;;
Hashtbl.add pfgsetmmprim "171c7e3e234bc6d8e2592618f20b5806b583b4cca4a116f9d16d47a50c4df23a" 304;;
Hashtbl.add pfgsetmmprim "ed736366ee2447625818887ef1b27a046bf23e1a5053b533d5368e12f42e8239" 305;;
Hashtbl.add pfgsetmmprim "ec107e7939f78f5cbd2416197acbbfb944f7682d033b773ccf2241071850d4ac" 306;;
Hashtbl.add pfgsetmmprim "341b42ee9febe6ca63b3cd9d51a2e930b261c629fff87f8c16b976b2540e6c45" 307;;
Hashtbl.add pfgsetmmprim "fb6891cca3879cc4d06ab5d89ed27840c62f17fe6175425f85902a8a3540c480" 308;;
Hashtbl.add pfgsetmmprim "d50bc5f338d7a576e1b4a8ca70ea6de20a632d94f71d1df26432ea400fd2eb23" 309;;
Hashtbl.add pfgsetmmprim "93b77fbf322413383b98a660774a36d464d939f327dc1d900f0ccb7ce99ce4c8" 310;;
Hashtbl.add pfgsetmmprim "046cbab0c82b29c506872ae56fe47d1a852b3057014d8d0db81a1ba2b184fbbc" 311;;
Hashtbl.add pfgsetmmprim "76fcfc83fe52cfccda239b507b12755f2f6799e35ab96099e30a10a28ee8d267" 312;;
Hashtbl.add pfgsetmmprim "d25cf6b5287b808e5f90250e43f7722b97f856905a9e906dae101a859c561d66" 313;;
Hashtbl.add pfgsetmmprim "53558a60eac3dc4d46714773154c2a23bdfb2be10f6e2022c986ee998d879c2a" 314;;
Hashtbl.add pfgsetmmprim "faf785ed14b57b297cdd6a77051eda9ee145bcfe63e20aa833095dfd3cfe3063" 315;;
Hashtbl.add pfgsetmmprim "8c537457b726a74276111ddbe47d1fa59c908387cc7d67eb5fa2dac365cf03e9" 316;;
Hashtbl.add pfgsetmmprim "2b1257bddc9200bc00d16279b90b987760953b637f446d0d7347e1b86079aaca" 317;;
Hashtbl.add pfgsetmmprim "284b4069470f9bd58fcd40287b9686ff26554b7ded5d46844d9b8b71c9837143" 318;;
Hashtbl.add pfgsetmmprim "a58ce30ff6062d641818cc98665fd4525a0b9ace3f5ff83f7a315eb64c6975b4" 319;;
Hashtbl.add pfgsetmmprim "b5d03cb5ef1feb6b0f314c5f23cb0b6b7d63a829499d8a94fba0bc949bba5bd0" 320;;
Hashtbl.add pfgsetmmprim "24b986d9952ef21aa342f96cc84830ef7fae2771ae93990223b20c90d9f1f821" 321;;
Hashtbl.add pfgsetmmprim "c6671ac7c8cc7cc32b0b4b8de1ba86c0d4c37513067662f773d89ac59ce3b15e" 322;;
Hashtbl.add pfgsetmmprim "a2aab653fefa4d4893f410958d4f31d37393c6cca8d0499283aedc6b85bd74de" 323;;
Hashtbl.add pfgsetmmprim "2c0d5a1feb41d348ddd37d44126ab51b477be07f6d3033b294e3898ced09662b" 324;;
Hashtbl.add pfgsetmmprim "c937ff035f5336c6fdf910440df1cc40d717eb566ff8e0b9697e6e6678afe0c8" 325;;
Hashtbl.add pfgsetmmprim "9bab5d8041186e5fd37dcc6d71d90cc37165033dabe241fa809b088c2fc6098e" 326;;
Hashtbl.add pfgsetmmprim "916ad2f475214b09070f179801f7d146ed22bd70e49e25404aff1c99aff5335c" 327;;
Hashtbl.add pfgsetmmprim "31732ae2fd5cb8960d8fa5505cebd2545bda5fe7a9c8228172b46b4d92c507ca" 328;;
Hashtbl.add pfgsetmmprim "38b0842d0bea66c0cc733ca1e8004fafc93a5c8ff1880e80fae61e8195949f2e" 329;;
Hashtbl.add pfgsetmmprim "e23ddc70c27669b1e9adf88a7c4b9aa7c1b767433312c33ac24771b0246518ba" 330;;
Hashtbl.add pfgsetmmprim "92c08b102214f3c4b8131089d136041a288f320b89f8d3ddd6cabbd4c38fce03" 331;;
Hashtbl.add pfgsetmmprim "784437c146adc852627c802fd01219da3e98897d42a8cb6d8e12fcbf90ef2466" 332;;
Hashtbl.add pfgsetmmprim "a3f8dc6d89fb5e15dd65e1e354cc416be0cd1cb667a9b49e55591f6d221b2b27" 333;;
Hashtbl.add pfgsetmmprim "6deaf637fc6cc2ff512b6641c14be0f733122e60e281e7f77ba9f7ac480c0b5d" 334;;
Hashtbl.add pfgsetmmprim "01ff66d2b5310a69835c11e4a953776041a2c4b282daa5491faafb3d474ce8d6" 335;;
Hashtbl.add pfgsetmmprim "26c2f9ba83ea9b836e0fddf2f21487b83548a2ca838732c1b309ae92d8e698dc" 336;;
Hashtbl.add pfgsetmmprim "be41a512b545dc31059930714d9815948c9f4f65db24dcf9169a53286c8705a7" 337;;
Hashtbl.add pfgsetmmprim "c1c332ed2668749c0084fbf1e57bf49cc070c068195a99a01ec887e8e040f6ec" 338;;
Hashtbl.add pfgsetmmprim "af3b9a4314ad476dc4bac9cdf60364701719a7149707c7528e535b4616840ab7" 339;;
Hashtbl.add pfgsetmmprim "9b72bf779c7113fc5061ef03f0387595fc5e8c743ac5d5af89cb6f8a6e59ae6b" 340;;
Hashtbl.add pfgsetmmprim "4edaff926262e0f1298e56f408f66f3ad1800e03ebb42ed770bb9736bfc017bd" 341;;
Hashtbl.add pfgsetmmprim "e811b2a94d6df237585d9a0a886eabf90caae20289279baaa6659e0d76d5d99d" 342;;
Hashtbl.add pfgsetmmprim "05d807e60b5a891f3a5ab9a62496bbdbd734fd5830b0e8d88285fe8507de62e4" 343;;
Hashtbl.add pfgsetmmprim "1a4216a277e881ec8dd978f344b430b0c04f490c863ec6da5ba2706fbee0f5e4" 344;;
Hashtbl.add pfgsetmmprim "9146d05cd4bf1c60390f1d1fd540a0cc50379d6755d0fa916fdbb516fa85dbb3" 345;;
Hashtbl.add pfgsetmmprim "f70bace54619688c40a1f6d7200e048cb54b6b86c721fe3ffda7f6ca8b8127a6" 346;;
Hashtbl.add pfgsetmmprim "56224c1b7e546fb4189f559dacb1c45c645f7252e8752f123deed4c58e5156cb" 347;;
Hashtbl.add pfgsetmmprim "cc16a180df47564f86ad8c256d1aa1317fe7784e3acce749625fddeeb90cc85c" 348;;
Hashtbl.add pfgsetmmprim "a5398cab233a0f65725e6a0eb25f7a282a4c545d308327cb91e78096b6144375" 349;;
Hashtbl.add pfgsetmmprim "acd43a7a2f7133da05029b0aa396b134f6117ae3f1e548164979e07423c858df" 350;;
Hashtbl.add pfgsetmmprim "c19feaf75701e025c626ca8d2fb7bc7749482e95c14166bb58dcd31520f52414" 351;;
Hashtbl.add pfgsetmmprim "ca396560d4c335f29c07ea25ae71bd95958c5d374e228d679e2df4890abfcb3f" 352;;
Hashtbl.add pfgsetmmprim "f83961feb100afdb925fbe89d803c06c3371f9e790bcc12c4ef1022871673586" 353;;
Hashtbl.add pfgsetmmprim "bcc6d8c0b5fb769f58742de972dbedd0b9132e342ae1606a7cbaaa1bbc404aa5" 354;;
Hashtbl.add pfgsetmmprim "86ba491720014efa9a2ec7c113e958a024a8418f71b70c604f1745f99a294630" 355;;
Hashtbl.add pfgsetmmprim "6128fd8baf3c5f100f7ca91e9ecd0872371b6839ea05c485e237fa3f559b1633" 356;;
Hashtbl.add pfgsetmmprim "54e15e49b61ca5d30327d312f1a26a517e152c1b9e54ac56e26aaf18a0fdbb01" 357;;
Hashtbl.add pfgsetmmprim "240322a817dfde136015b5c59bb8991b76058ef86d8885268e2a8e2ae3bdfeeb" 358;;
Hashtbl.add pfgsetmmprim "c54c365d76ac9f1dc1e4b73649f05c3b6b7680302f621e25dd198d006ca3ecfc" 359;;
Hashtbl.add pfgsetmmprim "e78fcf40a29d50ed93e87baf23266c721e956024bc8d679c9dfc63b79b485c3a" 360;;
Hashtbl.add pfgsetmmprim "633140f45782db1026c55cebf81031fc332bb499c53fab8c4c06944b9e5b5bc8" 361;;
Hashtbl.add pfgsetmmprim "865a8f4d9241396346dbe5e247318452b21e72fc7f301b285fa99de65aaeea04" 362;;
Hashtbl.add pfgsetmmprim "8882781e65fcba091d6037436ab73dfaf01ad021e286ce80e79081cbe7bd6708" 363;;
Hashtbl.add pfgsetmmprim "9d414623c681853ff42e2069fab36cd29933dd783de2be3b9148d9bdfd1637ae" 364;;
Hashtbl.add pfgsetmmprim "8998e3afb594bf9acf9b0e23a877ac9b2245b77f172072a0001887f1f679aa91" 365;;
Hashtbl.add pfgsetmmprim "96e6e0c5c1ddb1338203e9c1843da6c59e965cdbc036fe11eb9361dd0f414786" 366;;
Hashtbl.add pfgsetmmprim "c0578a1e34b7d54504adc006989e0e26b4a404c5ee4b1b3b2caad53b43f51900" 367;;
Hashtbl.add pfgsetmmprim "c108d5dafbc85d752f76717318a2578c849fe357ac46c0997bd09fd8bfab0eeb" 368;;
Hashtbl.add pfgsetmmprim "085f366d9f1b0440972ff0153ec107ddfd954ec311fc2bd3b16b2c7b9b8e6658" 369;;
Hashtbl.add pfgsetmmprim "8c51b4d3989721551a5c70caa0af2d3fc7716cefea839d130f02282ffdc0166d" 370;;
Hashtbl.add pfgsetmmprim "8a3f971ffcb58e07374dbed6d44ffef70f3bab8685cac28d1dfceed83672f446" 371;;
Hashtbl.add pfgsetmmprim "9513c50e88ae107aebdd63d78bbe7a618ae57c8597cf3e07311115e4e80c2fc5" 372;;
Hashtbl.add pfgsetmmprim "335f38fcecb6454b81bf3dbc3215d6f343e63791a8621790f5105fbc6df153f5" 373;;
Hashtbl.add pfgsetmmprim "47359f126106acd7895367ea9e5b8f626f869082a0a2408ca1abed37fa6587b2" 374;;
Hashtbl.add pfgsetmmprim "8dd5018c08ff63918a20a9661d8e15e847d986b417124cd401f954f17cf8503b" 375;;
Hashtbl.add pfgsetmmprim "7240e8bb1f27c3ffa9779909504fcf22ffd3b7597150b72accdd31c4c805ef9c" 376;;
Hashtbl.add pfgsetmmprim "ad0dac34dc9764fe979c023300026e858913faf825ec419a89d4e7650089feca" 377;;
Hashtbl.add pfgsetmmprim "4f9395bfb3b356562288cdace5aabb80d80020176921fad377f0672dfb8cb3c3" 378;;
Hashtbl.add pfgsetmmprim "b59eea9d2a45facb07ee925d7a36f0c36e976a0d2822fe6aafff5253b4ad8ee2" 379;;
Hashtbl.add pfgsetmmprim "97b5b6a5dba8b6b8e2f58175079e28ab2c3c3ca83ea1c37fe1a10b5c12ebb391" 380;;
Hashtbl.add pfgsetmmprim "d7b7b58728e89870f688261a9bce90a5929af19f137303af54f2d58062e476e3" 381;;
Hashtbl.add pfgsetmmprim "ca7fa93102ad058c9e9e2beaf27e7514f9e7bd0c31af5fc9a48e2f33c0b4febe" 382;;
Hashtbl.add pfgsetmmprim "13a7aeb7bb9c499e2dbc95c3a81817b77340c4f93be840907667acb54d6af55a" 383;;
Hashtbl.add pfgsetmmprim "2d1edef2bbf78bca3ebb5a47f740a9f2df087acd143106f68847148f71c9b051" 384;;
Hashtbl.add pfgsetmmprim "dc278e68037d0f92d18d35c24faabbf7ed040ac3f189283b7a9502e4f25dc482" 385;;
Hashtbl.add pfgsetmmprim "2da1b130d5dae5046f4aebd2571c1095c479c3d0ad7818dce40b6f79f5c2e684" 386;;
Hashtbl.add pfgsetmmprim "3ffa84c62530d3d2ddd4b64dd7367584a573a73d241e51954d4627e8f09ae1c6" 387;;
Hashtbl.add pfgsetmmprim "efe0c29cd392adc11d7a1285216acbd14a948465d3f71c65d482f5dc2e6555ba" 388;;
Hashtbl.add pfgsetmmprim "9167497d7dd306b1a469f0cefa2901127db402670e23a18563f556c073220431" 389;;
Hashtbl.add pfgsetmmprim "5570e3a31db1be32efbc63cc9e051509591d25e1894f3fcb2bca1df5b20f2a99" 390;;
Hashtbl.add pfgsetmmprim "088b7ea603c024517607439809d8b3c9985a6f9f4bd5e841a70d03cc86968d97" 391;;
Hashtbl.add pfgsetmmprim "bd5ac2f65785caf17525bef44a0fd96cf35b95a587dd16e8bc322a0f791d33c1" 392;;
Hashtbl.add pfgsetmmprim "60541cfdd6b30df0e4a07d07738ed330ea0e7dbc1dd5aa985f329f13248a63aa" 393;;
Hashtbl.add pfgsetmmprim "b766086c6fdacae52290a3c7d3325fc5c7624023d1c1623029b870f156c60a29" 394;;
Hashtbl.add pfgsetmmprim "e034269c6d5b9dc56624ac8869e302279f0a8d2e23e0963a24984541a8c87fe9" 395;;
Hashtbl.add pfgsetmmprim "d56c09acbaf378608c18331c671478097aee2474141a765d58422a4ef90f09ff" 396;;
Hashtbl.add pfgsetmmprim "470a22c7a3dd3b9422c41ab2391a4d88b3fb7d6b32a376e1b60821a5472f42ea" 397;;
Hashtbl.add pfgsetmmprim "041aa66c3cabc6279d3a4898644befe193e6daf840e474276630dd52b17b8eff" 398;;
Hashtbl.add pfgsetmmprim "f650cac111418f9fd23d79761f22beb9e1407f02c31e443ab23bea2cd33a637e" 399;;
Hashtbl.add pfgsetmmprim "b4b2ce89054831c6c7eef88c8eda9e8c726bda94acd25ca2e44db9d3a82628ac" 400;;
Hashtbl.add pfgsetmmprim "aa6706eb5d3d4785aaec3772e0218515f499b2595ae32cc19ceb5dd6e1db1aa4" 401;;
Hashtbl.add pfgsetmmprim "96d711fa46f00117f9a9235ecc6065e018fc8a9c00911a0ca42fcd003abac485" 402;;
Hashtbl.add pfgsetmmprim "7c42a2321659fa49105067aa37333dd8d0f4a5a9a6706240b0cbefd28a9b84f3" 403;;
Hashtbl.add pfgsetmmprim "37c76c93b361e0b86edc18c26a5051c424b074222cc43349ead813cd10dfc74d" 404;;
Hashtbl.add pfgsetmmprim "cbac81ee91fc0730facf49eaf7aaa23a2eeaa809e78fe58f1edeab97892993e5" 405;;
Hashtbl.add pfgsetmmprim "1c5318623d24054bb61ff7b758c1f6014e8536f6241ec238906589e5cf5b12da" 406;;
Hashtbl.add pfgsetmmprim "95c7083cc0421c4bd65f626dd547012e39829d4e7815345266daf743bdd8c3d8" 407;;
Hashtbl.add pfgsetmmprim "d1da5d6357a8e26db9f6b099f6559036169efd3b079a82128dfb8f42eb2eb62b" 408;;
Hashtbl.add pfgsetmmprim "6689d47148a17fb2fa5f139aae5d9c71b0e6018292a6bcfb3ecdfd6e0ecd04f7" 409;;
Hashtbl.add pfgsetmmprim "5a2c6b0a84022f5da869a209a107c9c54cf03951dc12245585f3561894219b28" 410;;
Hashtbl.add pfgsetmmprim "9af065661b2172320136cd711512bffe2d7aa29cb2db823f9c64cb560623ec03" 411;;
Hashtbl.add pfgsetmmprim "84a32f72a9fd854b3b55bb05e13a1675fb2e681ae463634a4cc785fc96f75530" 412;;
Hashtbl.add pfgsetmmprim "5607d4b0106f5b456bc30730ac1c8fc3559f130d28207ae0f0816aff80521856" 413;;
Hashtbl.add pfgsetmmprim "0e170b5d365c64869fbe4b57555f39c0450101772351a5de22b195fefbc75d19" 414;;
Hashtbl.add pfgsetmmprim "70af82a662bd2409483b02252859927936562b116a105ac54767263334ea21fe" 415;;
Hashtbl.add pfgsetmmprim "9af5361ae2ab1d35459cd7e1d4ae42ec105dc6de00604deb490a626c35d4fd32" 416;;
Hashtbl.add pfgsetmmprim "56775491f288d369796cbc4dcd187f85ab04f9849758226436d2a42f4280fba9" 417;;
Hashtbl.add pfgsetmmprim "9edb5f11bddd9c68a56bef83dce63833d829c9098a8573fba89a8306844f0b60" 418;;
Hashtbl.add pfgsetmmprim "55db45afe6dce97b5b1ce9f725f321d04476b5a5cddc93a2b7ff42f6c7e2ff93" 419;;
Hashtbl.add pfgsetmmprim "f48e8fb479296a0674d07477da7ba88a0a5ddce23df343537cffa6910c39f92f" 420;;
Hashtbl.add pfgsetmmprim "9b1a9333ed1af16e38d0089c9fd56209f02a328193d1c32a51fb21d9de10e7ec" 421;;
Hashtbl.add pfgsetmmprim "40de8fdc4d56c4776bdc9c18bb0f8a5df3df91e1fd6a9f1ecbf65fdaeed26624" 422;;
Hashtbl.add pfgsetmmprim "4b21748328ec33f011f30791e7a0382f74b936e619e3b9382ef60501ae1bd952" 423;;
Hashtbl.add pfgsetmmprim "3c5d623a20ecc73e52809f2c7f346b574554d428e9277d941cc081614510edf5" 424;;
Hashtbl.add pfgsetmmprim "0c5bd3c7ef40f13724cdaab46793fe78ccb8acb07a6136bad3fdf6af1d594aef" 425;;
Hashtbl.add pfgsetmmprim "a555be8dcd3c2685176a15a67accb73a7ccc4b2c7771d2959019d08440b003c9" 426;;
Hashtbl.add pfgsetmmprim "43949f8098a3c62d9e0d0c529e311691b37d283f8134b435a9f5bebe041e8f32" 427;;
Hashtbl.add pfgsetmmprim "e4fb2eace3e0c3c52ab99b16e04afa954ba83bc275097e24eda77766ef046707" 428;;
Hashtbl.add pfgsetmmprim "c3c4ee53c83a8b381aa82b77e58c2472cfe7e508b0a86f91bd2829e78ff72794" 429;;
Hashtbl.add pfgsetmmprim "17b3f5c81312e6eb09ef45951896c2deee5a1cbd63c46d3610011764a2902003" 430;;
Hashtbl.add pfgsetmmprim "9eb9a2b0cb487eea4bea498d4373b15e86b5f2a3e162cf1e5757c20c7193590f" 431;;
Hashtbl.add pfgsetmmprim "18174200917e219d1a46831765c6304cb4532b16854f69e49937d9d4f34d5d5e" 432;;
Hashtbl.add pfgsetmmprim "7a0175ef5eec9774c278fabe2ea3a1a63fb1d30ad7b64425b5e40859cf87d2ca" 433;;
Hashtbl.add pfgsetmmprim "d82fb37a35392843c18309e29b3873083201b350816ff05728a3d6a8fd44958b" 434;;
Hashtbl.add pfgsetmmprim "0991bd3492bb6bfabffc06c26f2b35cb9c43e51a2a61cd7d5e93199462d31075" 435;;
Hashtbl.add pfgsetmmprim "addd8766436b9d5134f8fc22ce96f9c43476cf0ff7f37cf6b2a11067fd0db81b" 436;;
Hashtbl.add pfgsetmmprim "1915b680fb91c0eeaa17d9785006a5e3bd0eac20246cf31ae23ef6ed90fb1a8e" 437;;
Hashtbl.add pfgsetmmprim "0a0a494a70e9407b86ae30c5c3429c4ff5f2ccd5dd0084da6dd0e9a711ad5658" 438;;
Hashtbl.add pfgsetmmprim "8d02e656911ccc1b3eb8f3fcafd727dc4a78ce23826cef44030790c7e0f75594" 439;;
Hashtbl.add pfgsetmmprim "1ac659f85c680d75d85d64a6caa78f174775d61b56a0c9db7ede300e37753fed" 440;;
Hashtbl.add pfgsetmmprim "e40162b6259249ac4136f00429a35b4aee2c3e7a4ea3461d18314a673c188d4a" 441;;
Hashtbl.add pfgsetmmprim "89ce84184b2069617cfbb64280548a72a4f0de37a8ad1a83d8ac9e949fae6a3c" 442;;
Hashtbl.add pfgsetmmprim "4939e70819ccb6b56d8f0bd31c06a6c9222ee88c66bacd79dd292dd16805520c" 443;;
Hashtbl.add pfgsetmmprim "99871a41fa5e63d2732fdf1cf9ffc4853ca40eaf6fc1c0159bf18b5ae7f059d0" 444;;
Hashtbl.add pfgsetmmprim "d5fd944ef454e6d6a3549ab317db551a48cfa9c006de92b775bd50651c6f22e0" 445;;
Hashtbl.add pfgsetmmprim "88e7fbd8010b655d867dc6dc01e1d4e67ef114272490b9add789b22605b2894c" 446;;
Hashtbl.add pfgsetmmprim "f3021093bf12b57b88d95d0c02cde82163f665e4002516bb1acb5cf5579235d2" 447;;
Hashtbl.add pfgsetmmprim "2b61a7c3ef8665f64be124eeeb17637e92dba9e23954607346986c38a908e15f" 448;;
Hashtbl.add pfgsetmmprim "34cdbb23ddc9f3e8222d9df232647c2782aed6d505d110a4b362e2f34ddc6ebd" 449;;
Hashtbl.add pfgsetmmprim "3d794d761c330e3136b2838a15ea9c0889145c785c6dc1ecefa7aaeba8ef7643" 450;;
Hashtbl.add pfgsetmmprim "79c03c05db2e688d3fcc74c5f44549fe848f9fe0adb795b75def52b5ce84074e" 451;;
Hashtbl.add pfgsetmmprim "4492b390d399555ab8f6731694c9fc039fa44558625b5671486246118b737173" 452;;
Hashtbl.add pfgsetmmprim "53ce440c5026cb6204144633457aa3d74d1b112e4cbdaf3bd8ef03dc6697313c" 453;;
Hashtbl.add pfgsetmmprim "03f88be2fdfe1ee6332ec843ea702255766983c595b8c367795bc6fee1f04c45" 454;;
Hashtbl.add pfgsetmmprim "fd27d359879679a8da9d39229b1acd048332afd86f9258726e3af0028d79d8d4" 455;;
Hashtbl.add pfgsetmmprim "b8f27b0bbfc20af91a8618a92219cb98461fb45ee07a1d9f1cdabe69598eec0f" 456;;
Hashtbl.add pfgsetmmprim "90e5a25913b4ce1f3c3120dd541d1e984bac1a15be5dcaf9d940af5973be44a0" 457;;
Hashtbl.add pfgsetmmprim "9428f4b9a4a7a25404dc7672ea42f4ccf4bdd166cf1693a3ff5781f5601c32f1" 458;;
Hashtbl.add pfgsetmmprim "f9f3c6949c0becc46120f4e945f44cef392d5c8cc316d8867a1eb310f2399255" 459;;
Hashtbl.add pfgsetmmprim "b259f95852b0e004dabc36aef37433286b4d6fdd262fe512f32be32f57bb44f1" 460;;
Hashtbl.add pfgsetmmprim "1fa1b3362f08c59edeae4690fe70d23bb332b52ab8825be05dc267b06a20dfbe" 461;;
Hashtbl.add pfgsetmmprim "6660310330452f6f0b585994e1c576e084b5fdc26639ba6d1f4ef35d0667e7d1" 462;;
Hashtbl.add pfgsetmmprim "a12495f3664ef36d18918c2b7679fd67186040adebbb77f7f662f03487310187" 463;;
Hashtbl.add pfgsetmmprim "8efde9319fb59bd1882607b279b06bcf787c3e08ae5a59b5e6abca9e0e443ff7" 464;;
Hashtbl.add pfgsetmmprim "cf1853dba8952a6db29b1fbdcb9f6179cded532fc217821548b7a87e3bbaf88d" 465;;
Hashtbl.add pfgsetmmprim "1be090fa5056ec6449f70b9e7e893bcb51f9117ad12d43f34d74ce8f51b33184" 466;;
Hashtbl.add pfgsetmmprim "7a799ee7276a5fcf3ccac4668fb87dca6c1baea5441219aa10f2af28eafee03b" 467;;
Hashtbl.add pfgsetmmprim "e04ee50cc91be8a65b5e60be33d7b66a74056ca87973660fdc0f6b3ba47508dc" 468;;
Hashtbl.add pfgsetmmprim "60022dd5adfc3229c2a7d49fec83f9e4ecaf2877d83e601e7e41af3538f19e37" 469;;
Hashtbl.add pfgsetmmprim "ad9fdf1412674adbc6ab9e6e78bd3a6d2246ce095f30c213f79b385a372d70a2" 470;;
Hashtbl.add pfgsetmmprim "8c9531c35ec467a2cd190ceb0eb298f5440f9a84452c5d74aa6840e6bd9d2e24" 471;;
Hashtbl.add pfgsetmmprim "7819bac4e9ea59a4d0d7c74f67d5f9d15f17072f8d7567c9fe11af1439b1297e" 472;;
Hashtbl.add pfgsetmmprim "e794bb079307a6916402f7dfb02f3208e31fe2cfe34590c3c18d7ae2cca16e98" 473;;
Hashtbl.add pfgsetmmprim "530d9d67c9e3761292d744a888de4e3b8bfefbcc5617504da3a60ecc9be41b51" 474;;
Hashtbl.add pfgsetmmprim "5768041ce3f986f864ced6399b81d53bfb54bb1effb9e6ff13618d1a71a869c7" 475;;
Hashtbl.add pfgsetmmprim "73ab819aa02cc8834a42c369c43cfa98b16fb05d8083bfa5bd978f9c8c0a3626" 476;;
Hashtbl.add pfgsetmmprim "aec85c67ae2ec3ba332e39c5f855f39a5c6fa3e6fc1d8cdb1fa6ee3ec54978f1" 477;;
Hashtbl.add pfgsetmmprim "7a71aacd6b62de46b730bedc6eeb98935bf70991a2eda3fd92b30d65e6d8ef2c" 478;;
Hashtbl.add pfgsetmmprim "6118748b68756b64bb18b96f456fff8f7aa089fab58a4013278692cfe34766bc" 479;;
Hashtbl.add pfgsetmmprim "6ba9444f61f459eb1a8a26983ad41ba1b8916d9257e83ca2b00864e3e4ce666f" 480;;
Hashtbl.add pfgsetmmprim "d0d5196d2ae2f9a9dceefc579ab16af74dc3addc15abdd7b9e2d13675de6c051" 481;;
Hashtbl.add pfgsetmmprim "d5438d0d1fafefbc0b078e608db2dce0b97b1d7a6e2ed4c2d315dada28081a62" 482;;
Hashtbl.add pfgsetmmprim "e8c26cdb526559b12e2684d4dac698286e5395657201afb402f3ca279cd1b75c" 483;;
Hashtbl.add pfgsetmmprim "cd2793576610dcbe432e65126e873c1612cd1c0a44c48c37b6e728fb0b4c34ed" 484;;
Hashtbl.add pfgsetmmprim "f5af00dc8508a1e79588aee9d6c118b51c69f9062d62b0f257a012334892a632" 485;;
Hashtbl.add pfgsetmmprim "61c4b5b2f400dd6fa10e641c56dab83180d7721ba44213380061014bcdd05af2" 486;;
Hashtbl.add pfgsetmmprim "ab6070f0ff9e736fbb379bff68d0c351a0da819973c18b63d22c921d24988e35" 487;;
Hashtbl.add pfgsetmmprim "85260d5f47ca7f4bfb05305b78e57f6b647c5e4b1143d66624ca2739af844037" 488;;
Hashtbl.add pfgsetmmprim "4aea769a1fef43872a3e358a88de9b4f3f4f3d2e3f4ba4adebcffc4c862ce43e" 489;;
Hashtbl.add pfgsetmmprim "8c106ba8df94f58f42d24b223c6ca52a825baa4265d2541ed36c878912464c2a" 490;;
Hashtbl.add pfgsetmmprim "c84be2d0c91c44d2aedb4ed50fc87c9bd6bee3fa028166d3a9cb233919b9e0e4" 491;;
Hashtbl.add pfgsetmmprim "707a56f2d4de470fc509c025be4e44f165ae01c8b24dd973fdfe1eae4d097253" 492;;
Hashtbl.add pfgsetmmprim "347955631a367124f02c48a97764fb44cf211b25b2d6d3f3d598a2e5264a72a0" 493;;
Hashtbl.add pfgsetmmprim "08b393c8af640a2f535a964af8251863ad44829b919094eca1daa0f775d9921a" 494;;
Hashtbl.add pfgsetmmprim "195b5f6654f37b469462303d36579dc9bcbfef05b60cc8cfdd737ccfb3efae3f" 495;;
Hashtbl.add pfgsetmmprim "e3a448f2fbe1ed6c0c8437f8fd3655152ce585a2688854caafc5315b1143ca27" 496;;
Hashtbl.add pfgsetmmprim "a4cb63f0deeefac72bf649e7788bf29a03d7e206415faaa79b1a5d3c8f2fd84e" 497;;
Hashtbl.add pfgsetmmprim "9f7d8cace0af238d156cbe7942bc3bac36c8176786062cb1a075822f23ea1a30" 498;;
Hashtbl.add pfgsetmmprim "9e294d310beb299b8cc06cf047b547fb1ec9e8f38cd395d72dde17e270c4364e" 499;;
Hashtbl.add pfgsetmmprim "70aebed8f989c6f5c8ca0f5c2c861b7f949bb9bba4cadad1cb128fd159011495" 500;;
Hashtbl.add pfgsetmmprim "a21a01d68378f791efe5c4030ec0916c9a33281c1f187bb98f6c8d1f1f71c305" 501;;
Hashtbl.add pfgsetmmprim "abd7500b57bb683d6db74f04b7a8462966327d5e2f07b727b63da501bbdba611" 502;;
Hashtbl.add pfgsetmmprim "8c4da203e452c948073393a9f9faf0d640f91d19de77f4670aa65f61833ba7c1" 503;;
Hashtbl.add pfgsetmmprim "ce13533c96f681ba4214e7c151e77ed4d6bffc8fa92e7181a1fa00fed3041a50" 504;;
Hashtbl.add pfgsetmmprim "86e050799873e003a0880db698ad82fe06c3cc2a5b31bf823a4798648262e116" 505;;
Hashtbl.add pfgsetmmprim "8d6f3bf44bb7f4a8b1deb1586e8fe4b33ec6faad7e8738d53442580fb4a16812" 506;;
Hashtbl.add pfgsetmmprim "e44d81f2e15ded4ab75f94cd173c3359697cfc1f02d947fa6f9c6747fbc35e26" 507;;
Hashtbl.add pfgsetmmprim "1e8bc5cfb6186d87e17c6bdbf116ddad70d5db090597ed907372eadd73d98b2f" 508;;
Hashtbl.add pfgsetmmprim "ec82b04458a67cb92116d9669dd299ece9cf1a3e4f1a9629ef5b7c7f8bacc8c1" 509;;
Hashtbl.add pfgsetmmprim "26137b807e8bf3b7b27bc4d100c6470afd3ca04bf4594c1128fbd8b4dde60d14" 510;;
Hashtbl.add pfgsetmmprim "3916c6d9fb3ada0e8ef85d4770f9febc178dc25c6ca59d2529d2ff861d3fe261" 511;;
Hashtbl.add pfgsetmmprim "584b7391144de80f8bee3685ea90035fffc74dd539bd66a9d705c10b945ab59f" 512;;
Hashtbl.add pfgsetmmprim "a94d206e8acd454047c7e34d88b9cd866949f9dc379598b8362ba7af411b7735" 513;;
Hashtbl.add pfgsetmmprim "a19e3870f9f9e3cf9cff57e5868b1db54adba27e84f150a6148e3c6d71424f27" 514;;
Hashtbl.add pfgsetmmprim "cbe8b2cc940b0730c6d475f8a169d6c0e33e975e5620a3e792bf6a1d421cb560" 515;;
Hashtbl.add pfgsetmmprim "81d16f635113c7d4fa87777b7e3699c0bcdfb4410a37bafcdef1083e18ca25a3" 516;;
Hashtbl.add pfgsetmmprim "73e7a618b220e2857c37aa45d3d75891db78deb782087134357d76d94becc349" 517;;
Hashtbl.add pfgsetmmprim "bf12a440a60b5c28c09b34ffdf7e02766bfa1e3a4828b1ef5de3281b93322ec8" 518;;
Hashtbl.add pfgsetmmprim "50c0b1326338f92188b2afc35a8df33b997622fa880ea49d576b6bd548e25d5f" 519;;
Hashtbl.add pfgsetmmprim "8743b44841cf4240b0f8748819f7d20c48ce9fa9882e4fc9bc8d83e8b9232c5d" 520;;
Hashtbl.add pfgsetmmprim "f29a752e04b2a693704f933f78e98496b3b17c306514885e70be6a33362fa23b" 521;;
Hashtbl.add pfgsetmmprim "30aef0b067f643c6f2d6d31b0894dd57c4e65c4721adbce4a06e2dd26d6ea950" 522;;
Hashtbl.add pfgsetmmprim "e105f71fe34adab907ec5775518b95fbda38d1531f599528a99e2a63817a0f24" 523;;
Hashtbl.add pfgsetmmprim "6bdf47ce6dbdc4efe23680710bf536e7ffe151ee3fb4dc4a804ce9579ae18226" 524;;
Hashtbl.add pfgsetmmprim "4d293438b1c659fa8362fda099d3f523d15d83eda55b8616d0b978dd957da50c" 525;;
Hashtbl.add pfgsetmmprim "1fadd47f3b653f0bdc01e24b59ac70ebad7b74454fd22ff32eb526cda239a477" 526;;
Hashtbl.add pfgsetmmprim "c563f1269d178a009cc662d9591042b46d75bdcd4a966a714ce18302c2b28809" 527;;
Hashtbl.add pfgsetmmprim "52ccecd86a0c965f4935b3b26d16704f254d00e6475ef8fe23bd10228d60018f" 528;;
Hashtbl.add pfgsetmmprim "3bb0dff3010f1016f6aa6befc2eb9b0e068731599bc5a5bbe0d69a230c09e653" 529;;
Hashtbl.add pfgsetmmprim "45a086fea509042314613a9201ced41cf22255c2f4b24b08498055c0c5893114" 530;;
Hashtbl.add pfgsetmmprim "d83f54b56f66ee3ec5b31a07fa765e1e8fa2e3c6067fbb381f98752078a8a08e" 531;;
Hashtbl.add pfgsetmmprim "793f3a1b013250eb199d86f7b8c02a3e187728199578736b43124b6b6b62c775" 532;;
Hashtbl.add pfgsetmmprim "a9d3998ec6a88d9a1b37d5cbe1aa9a3cf697ba9dc703652ee7bad342567db3aa" 533;;
Hashtbl.add pfgsetmmprim "03be974d1303f065969d1c3abd9dd23b23d1260c59c6e7c23ad3d8416778a74d" 534;;
Hashtbl.add pfgsetmmprim "10878ce3def7b3eb793fc3ba360f78192570a2e545ef57fbab6db30f30c9d348" 535;;
Hashtbl.add pfgsetmmprim "7292c7eccd1b8ac1c3515a416eec0864a309d08597b9d7903aa8bf4423162717" 536;;
Hashtbl.add pfgsetmmprim "3a27f7a0c27ca53c03d37e38548ec33f0b898cc398f5080ce55393b3f5a7fe50" 537;;
Hashtbl.add pfgsetmmprim "6d1343b3c95373befdc1f4b13d40e3b7983db4573bc17879fe962f83ba7339d8" 538;;
Hashtbl.add pfgsetmmprim "048c956636802fa3414557c16e28c16e92804c260d41922d39650a181e67d7a6" 539;;
Hashtbl.add pfgsetmmprim "86a7dd5a6332d25f1a54cc0489c5c04196a1dbdb4e24d578cf79dfbc7674cf30" 540;;
Hashtbl.add pfgsetmmprim "9768f7cc9008c64fe0ba5c85a13e90816e84ddf5481748d4a1963550bc0ee93f" 541;;
Hashtbl.add pfgsetmmprim "41d543da92e334c259bad893615769856b7a996c2456473c61db2076f0ba6517" 542;;
Hashtbl.add pfgsetmmprim "e595d985683aa6cb8f6871fc6a2fa2df50edf02d18424befabb4e6ad680d49c1" 543;;
Hashtbl.add pfgsetmmprim "ec069220eed7b9ebc1fd3225e60b026be30c516cb3944a38a6dd493d039605fa" 544;;
Hashtbl.add pfgsetmmprim "be40bcf995bff462cd8758eada0c4162ac7e6998de3fb58d14b931f73802af1d" 545;;
Hashtbl.add pfgsetmmprim "5f34cdb880dc3c510f0979f2bdcd0cf45a218d68d5d3cd81b2a6ed028c30d295" 546;;
Hashtbl.add pfgsetmmprim "0598f7b7d4a0d6aa069ab43e5b91732291a6fe2a43f4e763a3fb30563639d2bd" 547;;
Hashtbl.add pfgsetmmprim "be004766f12a2c38a1b8a182633d24282d7c9df0149250ec4ed79b4c21871706" 548;;
Hashtbl.add pfgsetmmprim "7b3e0690475e83bd0b437d92bdb86f899b8f6ea93af54ec7b6876f22da788eb4" 549;;
Hashtbl.add pfgsetmmprim "3e9a278463ba447fc1fedf415314bd1a3ef9fa5d8ee3c3bad3e34f115e4cdd57" 550;;
Hashtbl.add pfgsetmmprim "42200236bfe13df31e920067a541ee039fc2969aef7c870a1eb1e156cf52e4bc" 551;;
Hashtbl.add pfgsetmmprim "424c5ad44a14dd60129a26eeccfe050ceec26d181e1910d14e0593a457a96f22" 552;;
Hashtbl.add pfgsetmmprim "d7a40497ee9acf81300dbe75deadb044070ffb9ea3ad94bf40267c152480a86a" 553;;
Hashtbl.add pfgsetmmprim "5c2d44f06d7a5531fab22412bc9f6046beecaf43b1b90404409d18600b92b4ad" 554;;
Hashtbl.add pfgsetmmprim "36e92fd1866830199c8edb1ef172efb0d4bb239ec1e80f337e00912050d1353e" 555;;
Hashtbl.add pfgsetmmprim "2e2bfae6eb3fe6e94e4a796ac488ab507cd19ce8f9918f5d283935c24f1ffbd7" 556;;
Hashtbl.add pfgsetmmprim "2dfc8b41ace24c80be0fb47efefab38d973b0438d49c29d729053f6a0294ef37" 557;;
Hashtbl.add pfgsetmmprim "f2bd5036cf9f587df0009184922eeee0f64b5eb43029188e245122b7c80956b5" 558;;
Hashtbl.add pfgsetmmprim "57dde0c9560ff0a9a06dde50ce4fcf69ca091e12f789e03ae184426bab515844" 559;;
Hashtbl.add pfgsetmmprim "b239b9265199547a9e9a44443997967c8b693751e87677048dadc2b5f8588406" 560;;
Hashtbl.add pfgsetmmprim "bf06d9c70f452131a3a87755a72db325403f108ea3a747167144bf1fb4862e3f" 561;;
Hashtbl.add pfgsetmmprim "a574116609154fab6b78af98c16adc413315e9dd1fb333e0dbb018bdddf6b3d4" 562;;
Hashtbl.add pfgsetmmprim "0ae978a69666e6f5aa2778e59792f0b59721431dfefc8bc667fbec90859ea4de" 563;;
Hashtbl.add pfgsetmmprim "8ab5ffd54c25b69134d49f92c9745c1e473a1cfcd2933cd44de79ab69294b153" 564;;
Hashtbl.add pfgsetmmprim "6d5c8705c8999b496f4be7a3cb439ac7354d82b49c1767dec7adbf9995c12ec9" 565;;
Hashtbl.add pfgsetmmprim "3e1a6199b3e16223b6f5240dd6ab1fe37c0d1a3fef8585b58747ccf931e7ef89" 566;;
Hashtbl.add pfgsetmmprim "b26524d7e570883aaad510a2d03209fd0cb0a031faf10a07a42c8defb9b3e57b" 567;;
Hashtbl.add pfgsetmmprim "2252df29438aac2b86f2f318eba46b693598aa7662e33350eaf28e429dae567c" 568;;
Hashtbl.add pfgsetmmprim "2bd3cc60331e06db56cd06c4e0f5643adb9f74eb98fa6112d6e9876427091946" 569;;
Hashtbl.add pfgsetmmprim "fc62616e8f728d16b6ddd4a4e83d5e8652e4a1a97d173de98f36f17e186490d3" 570;;
Hashtbl.add pfgsetmmprim "3a2e3c9162303214240e93509206903480bdbec365cd1b0424ce6b0043d52d22" 571;;
Hashtbl.add pfgsetmmprim "8d3c2ec4a2c76f501f6201e7886a9070762fd48aa3f4798cd7ca75b61004eea4" 572;;
Hashtbl.add pfgsetmmprim "2b5f86eed69110c5c7c95d8546aa3ed21e271c8f4e75f5a0057d5cac2dc8d5a4" 573;;
Hashtbl.add pfgsetmmprim "4d3f94bd7fb5872085f094944bf1fa9c70768a2e2dda855aed30615d9d76de49" 574;;
Hashtbl.add pfgsetmmprim "a6d821d07a446ef9ee5d8aeacde5e873f15abd3640ef983b3d2f7e16c63451fc" 575;;
Hashtbl.add pfgsetmmprim "a09390067ffb531d0d1b08d073028b8ca200a4ae9c9da307fb6ced959f816c21" 576;;
Hashtbl.add pfgsetmmprim "7fe3add1cb9c0e24e7192b106be7aae428d473b17d0e4c64f56bf064be7d64d0" 577;;
Hashtbl.add pfgsetmmprim "d5e789ce33d12c5688d50884f1d26b8bda450046d45bae0c3b67814e989a7246" 578;;
Hashtbl.add pfgsetmmprim "f5ec66c5a2df358bd5f2c702abb6c1223cb70f6faa0d57b8ed3b076c10a3dd21" 579;;
Hashtbl.add pfgsetmmprim "31870a4d00299e29d1815ceffc1155f79af4a57f1c38007aa5ba3489ca07b2d9" 580;;
Hashtbl.add pfgsetmmprim "fd1c7896c127bb4896240aaf696ee25118772011e433d76e8afbe903bb6731e0" 581;;
Hashtbl.add pfgsetmmprim "4ca8716312e7da42cb397b6661b30a6a42d365fe2cce1cc93c3d652fd5175b84" 582;;
Hashtbl.add pfgsetmmprim "7d22ea80f998dda42e7f082c1e93fe11959748eabe1222f7af8bf4a1b081e265" 583;;
Hashtbl.add pfgsetmmprim "bb93f39782ee7010532092bb4935fcbe6902213314396d7cc68beeeece116eb1" 584;;
Hashtbl.add pfgsetmmprim "3a4aff312112d5b2a508c46bcb9c194cd2919fb07476e2fed7486ca4e980e4d5" 585;;
Hashtbl.add pfgsetmmprim "99da65c50ff966494eb2eaf9c198344d012f19d2f4a7cd138fc02fd4af5db14c" 586;;
Hashtbl.add pfgsetmmprim "3b3e285fd8fe02cdf44a5c2994dba7b176879c3a01cf619458a04b8695cc432b" 587;;
Hashtbl.add pfgsetmmprim "b87bb756b5ae438bb17224e649d6bed60a37d249a52f97f96ea7836bde4f6122" 588;;
Hashtbl.add pfgsetmmprim "c2d8efbc972d25a2356d3f83b36d55377e525ac49ddb6ff5425cf8546d0428f3" 589;;
Hashtbl.add pfgsetmmprim "dfd9a1a7e71752e05ce429a06222f8768690e767fd76efdc84aac737eca9d6e1" 590;;
Hashtbl.add pfgsetmmprim "08fd2342c930f165e3847060dba0a0a95d697a81e1e0d9a142a556f7c62843c3" 591;;
Hashtbl.add pfgsetmmprim "c21f1b6b290d9ca028c52199e4667244b356745c0668b8d8f92e0f4a9d1fbe6a" 592;;
Hashtbl.add pfgsetmmprim "8b7571d306d0128bb871261a1270a59fd8c97c868dc9a581d2499c764fe40dc2" 593;;
Hashtbl.add pfgsetmmprim "4c6f6384108e5319b7a8af6f4ea2f1519f6bea4b67b1cf7e5dc1f21f0f05ae29" 594;;
Hashtbl.add pfgsetmmprim "2124f8ba88c80efd2671382bc3519534e8095d921fa8d0c478288c6ff1d4d550" 595;;
Hashtbl.add pfgsetmmprim "da04b17183642324032726da838c7b527fe9dd106092c77c9f9c9c836aedc207" 596;;
Hashtbl.add pfgsetmmprim "6bde6eff01a040b945bb15d816264ffcec77813b033302f54ee3b2a4f1a2e30a" 597;;
Hashtbl.add pfgsetmmprim "d55c147084cc87df3d323391b2ced23f1ec435a7d4f080f6bd6e01039d042bd0" 598;;
Hashtbl.add pfgsetmmprim "409257760ae69eb3c22889dec15c0c8327e5391afc74fb87457d02697cd98c4d" 599;;
Hashtbl.add pfgsetmmprim "6af119873cb28a33e41d91e2ac9d360ec05423e559b1fef2c05d41bee536c9b8" 600;;
Hashtbl.add pfgsetmmprim "bf948d2d9eec860e25c0a92ae5fae4a48249de1fa0ad0634876374edd4358d43" 601;;
Hashtbl.add pfgsetmmprim "57455c6200ad926c27adfaf29ad837a2b68ca606f479af1acde37c3224de0114" 602;;
Hashtbl.add pfgsetmmprim "175c375e7384ac59cef77ce1b01cff42ee11b0367fe143da49af9ea20563c193" 603;;
Hashtbl.add pfgsetmmprim "1cbb29f1c8813030ce9cf9a2f853bcd4537bb64fe2789905597de05c1f7c0fa5" 604;;
Hashtbl.add pfgsetmmprim "76c455b82d7c7a87923850aae7c81649d6e9b14255199cfbb6529e0ae8b24e8f" 605;;
Hashtbl.add pfgsetmmprim "2c7f3f9fd4775e2cc9f08d439b894bab60dc4332005a448d2a2970452ff5e08c" 606;;
Hashtbl.add pfgsetmmprim "f747ac9194d740cf694f7c7fd204244f754ce2fbbc8637a114a526fa1e96156b" 607;;
Hashtbl.add pfgsetmmprim "174595d51bde846a713bb935aabfe51134c8f09e00cb882d86dedcc2f71b4b73" 608;;
Hashtbl.add pfgsetmmprim "49ad1fcabc8966d0df1f8e884a307f7ab14f8d5c81a4f0b7c2da610bddbf691c" 609;;
Hashtbl.add pfgsetmmprim "9004d461ab418cb65cc4ca03e79bbc6587d4f3ecd702f44e1fcf1af026c00515" 610;;
Hashtbl.add pfgsetmmprim "62a45888b7970ad6a2798066a82eb9fbb5bd6e16679a13866cf66c8271711920" 611;;
Hashtbl.add pfgsetmmprim "74f3dcdf89b9b55200c8f1623615d863ebbd76a898ea68c3470174bb898ccf70" 612;;
Hashtbl.add pfgsetmmprim "e85cde8d81eccc17b4e6216712aca04930ab319241f9636dc7bd205bd6b4173c" 613;;
Hashtbl.add pfgsetmmprim "209c9e737023d3b50def1e4fb7d63096cb5c171b26a9c721138a34640bfe4c35" 614;;
Hashtbl.add pfgsetmmprim "45056ed79b2499a4c8042b0a60509015b8b580ee5280bb54b70a3667936a3a14" 615;;
Hashtbl.add pfgsetmmprim "06bf0bebab67de7420cc96793925d3ad57edb4c2c484af71d15834b75fd4219c" 616;;
Hashtbl.add pfgsetmmprim "06a36825d5a4806f763dcc61f2fbe7a3a9e0b7f2bdffb67f0c3f226955c9eeb6" 617;;
Hashtbl.add pfgsetmmprim "ca6288fd0404b16431ab00120d1de9be80ac6767d362040fb3d2421f8b28dbb8" 618;;
Hashtbl.add pfgsetmmprim "fd86a34801b5449f9fc9a9739771dce9cb515c8a9a728e5c0160c03bd08b0610" 619;;
Hashtbl.add pfgsetmmprim "086023cb3a7a1a91f4823f2f4442e9c7f93c1044b5a1b9b95c6d9f805a758edf" 620;;
Hashtbl.add pfgsetmmprim "a579bf2e9475c742381fe75847cb7bb1f76d7efbcf55f9539233c081e16afa3b" 621;;
Hashtbl.add pfgsetmmprim "cec3b50199fefc7edb217ff0e04fb094ed3e4384107f62d76e3201320fa3207c" 622;;
Hashtbl.add pfgsetmmprim "914c1d9982e7c4b0f8c983fcdf4a40fdb73fb9644cbba253195bc9fc11d5fa38" 623;;
Hashtbl.add pfgsetmmprim "185094ddddcbd1c599407845b82f5ac41f813f0fa1d94c5c4b15e623fc62a5a8" 624;;
Hashtbl.add pfgsetmmprim "87f3602b907d9b5ecd5e89e5b56575077b93f114330cbcf7d46c494ab481b7b1" 625;;
Hashtbl.add pfgsetmmprim "7a481055eea7d5565ce41612ecb7351796b70388c6380436d4c46daedaa746d0" 626;;
Hashtbl.add pfgsetmmprim "59ca47c5515495e8a431d13200005ff3ac6d04a16b922317eab5c957ec9f63a0" 627;;
Hashtbl.add pfgsetmmprim "a13b9c49fc4ef4bb13bd6ac2e4a5ddac122bd28dccafa6fd46e3bdae7cbadf5a" 628;;
Hashtbl.add pfgsetmmprim "ce9fcd2afe98bea5cdfceb20c5c36a3de3e648f925064eb09dcd00de1150e766" 629;;
Hashtbl.add pfgsetmmprim "b4135561b3d1dd66451a3b25181b230ef981f08c8fa64dd48c610bd99dc22492" 630;;
Hashtbl.add pfgsetmmprim "521f84310a34afb49269aadcb0e715511ca21950ee6cecbd415bd9c5e33088d0" 631;;
Hashtbl.add pfgsetmmprim "815ffe4c1f49d2293b73deaa3ddb33cb020c9df1d1b9f85991fa7fc36cb8c9b4" 632;;
Hashtbl.add pfgsetmmprim "de64240436fa95513f304a70461dca913ffb665795f69faf50418e2e86c498d2" 633;;
Hashtbl.add pfgsetmmprim "cca3703629759a9bbbd9cfd5ac9c42d34f2ae79d0480a0e12448a1f5078fc510" 634;;
Hashtbl.add pfgsetmmprim "a0a19a2032b523d7dfc18fd356f4900c99bf5c80addfb3e1fdc4836efa324915" 635;;
Hashtbl.add pfgsetmmprim "80e9d7cd26dcb138ec95a8ce14be55c8c14c6693e773bb76c78df4e1213b57ad" 636;;
Hashtbl.add pfgsetmmprim "a2b51f570fb63709ba8c56c0b0c3bf39c3a92a48e620ba56dccb696cd077a49b" 637;;
Hashtbl.add pfgsetmmprim "d1ac28776b4220adbf23b1d6de46a97a8343e30c95fa7691f4db486414b08978" 638;;
Hashtbl.add pfgsetmmprim "ddaa2223a9462ba88489d954d3d61a6e4eea1924ca60657e11fe315dfac34d11" 639;;
Hashtbl.add pfgsetmmprim "7c12cf1c7229814c050030058e52fcf83e64bbb51fadc2ca3b41225a166e642e" 640;;
Hashtbl.add pfgsetmmprim "d91dbc96b94528291ccbb142396d169c257a3d80372964977e2cdde91613e67e" 641;;
Hashtbl.add pfgsetmmprim "b77be179932ebcd51e4f1b086cc779e1298bf0cdab1f6ae7ba6ced5c3280e1ad" 642;;
Hashtbl.add pfgsetmmprim "b368587453fbb1a9004f7034ab77028c9e078fd7c9a1c5f9f1ce74d21760a983" 643;;
Hashtbl.add pfgsetmmprim "dbbe72bb0a545dd9657dc0c4e0df6c2abf7fbb4f77558b33f554563cacbb1375" 644;;
Hashtbl.add pfgsetmmprim "d1648ef1d34e9e9fdbf9fcafac66a68330d9a52c21dbf22f8241aecf5ca1e710" 645;;
Hashtbl.add pfgsetmmprim "c65399f64932ca621eba58813595648a477f11ea6b4bf2e4c4448bedb3eb261f" 646;;
Hashtbl.add pfgsetmmprim "aca508bf53edec36195bc917ad649993d6cdc149e9e9229deeb578b6547e49ec" 647;;
Hashtbl.add pfgsetmmprim "a4728dc126a1dae8cc2c7a9c56041aa3be7a4826057eec710e06aa7b21c09879" 648;;
Hashtbl.add pfgsetmmprim "2d02a311f2affe5babdcae6ec975093ee168346e957489ac7c7994e773808218" 649;;
Hashtbl.add pfgsetmmprim "7ce258568346778f9b775b5f6b521e03f996bcdb498275814318e421050b13a2" 650;;
Hashtbl.add pfgsetmmprim "b31fc957ae1b1a0aeccf27fa5d1b870c52fec65f2ac4ee1a37a46e5025c3b9a1" 651;;
Hashtbl.add pfgsetmmprim "67e0f111edc497a34b9117d5407aa4dbf4b9c1e5431cb22bd5e4fb1f7c623fd3" 652;;
Hashtbl.add pfgsetmmprim "28469c7ed4bc9376976c3e0f1c9e56e3f516b64a22a2a85271834457cab009d2" 653;;
Hashtbl.add pfgsetmmprim "4089816d9a79406b8b3d46678022ce6d8a9bfde4b7c5db0b7a5f8dcbaf9f81f9" 654;;
Hashtbl.add pfgsetmmprim "a7cbd4848a4a7c4d61c53eb36b2ccf7869c5a72c67e41d61bd4ce50c35313449" 655;;
Hashtbl.add pfgsetmmprim "b3030585d4de605e200c02e70bda9a1b2d1a8017b0e1edc6a981ca6d39b7dacc" 656;;
Hashtbl.add pfgsetmmprim "4870f9c807dc5da4a8d37fda655f780ec51f15eae737e2d9ef0ddf3321afc878" 657;;
Hashtbl.add pfgsetmmprim "fa729264bcff807eeacb620c6923b7778ff1a8ca4aa1beb6fc1580710b777fe7" 658;;
Hashtbl.add pfgsetmmprim "8dd9124fda5651e52920a864c0d0a1c04b0947678b29c04a2e1d9b0a845526ee" 659;;
Hashtbl.add pfgsetmmprim "37f135f76c49af2c8d8de5318373bd855b8161bcca4510eb4616a481cdc53846" 660;;
Hashtbl.add pfgsetmmprim "611fda729742da6710c1f235b8a28599e71baaab0b2ce449c5d0beb4317ee8a0" 661;;
Hashtbl.add pfgsetmmprim "c3a9816c26b33b220a2b6c88d78d02395006256e93ee2926a9addfb17ddad50c" 662;;
Hashtbl.add pfgsetmmprim "aa763295ddd017d8dd7de3d654013a7ce3feb91efed093fadc05e844946be14e" 663;;
Hashtbl.add pfgsetmmprim "7f72c8551eaf4e3406e9bc71bbc8de328d275cf4371ad9f3a51ddc96907a8745" 664;;
Hashtbl.add pfgsetmmprim "aab4da0624e31487746ee834e74fd1334d554b08b0b0b5c5ddcac17ed0c4e7c7" 665;;
Hashtbl.add pfgsetmmprim "e31c6d954a9a4ef5684ff8a1091d6de716c9b269d22b8ed652700d5a97180a95" 666;;
Hashtbl.add pfgsetmmprim "9d5495cdee29d28b1ef374b9131f255d1ef88a971a1178c9452d78ecbf7352b7" 667;;
Hashtbl.add pfgsetmmprim "4151a2d55291414b2d2d60a534292ba4403f182c8cc2fc5c95a44a7c9947ee59" 668;;
Hashtbl.add pfgsetmmprim "7daac335f1ce63a7e24006331271e11f783de5d53dfcc76f832db9ca3490b103" 669;;
Hashtbl.add pfgsetmmprim "bdd80ed7e8b2970bfe258e5b847edc42294c6c34b4adaf4f1ad72305813dc476" 670;;
Hashtbl.add pfgsetmmprim "8d6eae93ed5c4dbe09e1e1001040353e04316553c53d8ad85915e9b606e99475" 671;;
Hashtbl.add pfgsetmmprim "836974e42b5d87a1a185977656c7cc90a095b712d6de5c11f598992f23e81c76" 672;;
Hashtbl.add pfgsetmmprim "153030dd5c7948d9d12d094371650268641d140426a95d2c5d2c61117dae0b57" 673;;
Hashtbl.add pfgsetmmprim "d30af91e953e1e74b765e87160bc77cbf88b42f0514dcc312e266621cadb6fc3" 674;;
Hashtbl.add pfgsetmmprim "181e3014858eea68e145d7318d24b7eb6a70100b01e56b3f96f835999d0a8da1" 675;;
Hashtbl.add pfgsetmmprim "76813171f2b1d3dd5e8d2c3df923a5af1669f4c2b1d957d1e53e9633751a84e7" 676;;
Hashtbl.add pfgsetmmprim "4f4216e7ff252985815ea5884c12ea8396731f748e6d2b03f3c5587c8e9e90b2" 677;;
Hashtbl.add pfgsetmmprim "4510e7ceef3978eeb0317884ceb29513a1deff7d9b572db0e32f4bcda545a220" 678;;
Hashtbl.add pfgsetmmprim "706a69a78b933b1706b12ec6007a429d720e4f3547af760ed22c120b782751d4" 679;;
Hashtbl.add pfgsetmmprim "cb6fa04ab08c798a6fd3ec6b7c2743518a6b6d67cf8ae38db981982f638becb2" 680;;
Hashtbl.add pfgsetmmprim "d1a46729af49186d60ef200f4de9cd5118726638ced7734ce5ca446d730d316c" 681;;
Hashtbl.add pfgsetmmprim "61bef6df170e24d6b4d5bea36e53d1b2856d52dd9c6e29e4352ae1cec4c6c23d" 682;;
Hashtbl.add pfgsetmmprim "bbb91470b7831d2b97e89bce237702109084ea4a98030c9ecc7448f6c3de3fb7" 683;;
Hashtbl.add pfgsetmmprim "f7f041c97648f9068ebd22e3d96bb15975c9cf79b2bb4737b82b595d09b47249" 684;;
Hashtbl.add pfgsetmmprim "322cdcb309c3445be4cafa3d1b83ef3081f88a3da8a4be86c9071d888984b816" 685;;
Hashtbl.add pfgsetmmprim "12ea6f8c603f666799936e39ea4536061c5deb37a192e4a85a1abbfd8ca2a6c5" 686;;
Hashtbl.add pfgsetmmprim "30345f3ca3d3daae24fdf59b7a3347731a48ba390de32956a02c054f8b73c3fd" 687;;
Hashtbl.add pfgsetmmprim "715107c1faa26146a3ad75d1d28b8c4911d243b821814b9d195d16d6f92b0fcd" 688;;
Hashtbl.add pfgsetmmprim "4ff0a5636bb9bd1656d12878283fb36d6b72c5fee49c894c537e8738c24f1977" 689;;
Hashtbl.add pfgsetmmprim "55fb7fad0ae8bd80166f57c15be2075faef55521960900e7213b6734a2db34d5" 690;;
Hashtbl.add pfgsetmmprim "c1c5ad793c10b3405b04dda353ef1797b593757ab9450b1933fc312b6bf9e691" 691;;
Hashtbl.add pfgsetmmprim "d33075c2f95f986d2290fcdc5c68bd4d895847addc2e31299bf6ce233db28b2e" 692;;
Hashtbl.add pfgsetmmprim "40802b1f3a65d15d3cb3dedea1fbb3851c3e4ba0e6a95578fb0202ddb3a8dad2" 693;;
Hashtbl.add pfgsetmmprim "47bc67447e205e472b0e022f636927356ff4703ba2c3e76293eb84528679ab65" 694;;
Hashtbl.add pfgsetmmprim "8b5f1a031438f2783261382e18d9c79a9180c77b0828f22ef7b75c3856e4cd8d" 695;;
Hashtbl.add pfgsetmmprim "0eead7480fbcfe444e880f5f49cc493399cf68938974a511633ec06c544ed9cc" 696;;
Hashtbl.add pfgsetmmprim "ada6b68295313841bf9ae7a223ce951a8cfe66284b5f6f138fa1c789c00a1dba" 697;;
Hashtbl.add pfgsetmmprim "16a81adba8a9d6bf74f50c08a855637fbed51398a900564fb06b87e223ee2177" 698;;
Hashtbl.add pfgsetmmprim "19138c44d1bb69ed206323ee9c74e395ec9a348d7284f9c4ed0b7d949fe37f0b" 699;;
Hashtbl.add pfgsetmmprim "37829d7d219b1c7a3ef5c0f06b627913f1a5bd8a7ed034b2f755ae64859b5707" 700;;
Hashtbl.add pfgsetmmprim "7fbf4b03a063266ecf0a2130b07fb7dfb0f0bac5ade40d723a25743e4fc8c943" 701;;
Hashtbl.add pfgsetmmprim "6fe22105045b6f35135a8a4e376bb9e030bc79e63c0e6920d19776575d65bba6" 702;;
Hashtbl.add pfgsetmmprim "13785c50e51624c9076918e9af33226a675f72144657de295b688e1069e8c294" 703;;
Hashtbl.add pfgsetmmprim "2c6816df50514492c2bdefc23fce5c8a6bbafce25c326fd204f652ecb23ddb94" 704;;
Hashtbl.add pfgsetmmprim "f2674957c89d35b1fb3cf07e95528389a437f38b6449ac198f2249ad49f0acf5" 705;;
Hashtbl.add pfgsetmmprim "2c96bf424fe0d246414d17e9c2da7bfb48e8f837d7ea0d284cf4c4c2e4762be8" 706;;
Hashtbl.add pfgsetmmprim "e9490547518b5aa99f462e317fd65d39ff5ac40898876d27aa4beab91d7bfc84" 707;;
Hashtbl.add pfgsetmmprim "ded70275765eda9bf1b1dfdb7a019cb5532d3f5a59c0297d84c01588c206b191" 708;;
Hashtbl.add pfgsetmmprim "f06c9fa8e56b0ac204252f191647e7c3da5ca0881ea8281f50db719fc804be3d" 709;;
Hashtbl.add pfgsetmmprim "603c0d981a5a55866300c4a4675201d56c7d6aaa1e948f44edecee9acd3d8454" 710;;
Hashtbl.add pfgsetmmprim "2a34871fcc4b06e2a063ec7c86928d731cd38b489d8e38184bd01f246a4fcb44" 711;;
Hashtbl.add pfgsetmmprim "9f7441672b4dcf38f3d0f974dd2aa49181783564afbb12d4333105cbbe7c4fea" 712;;
Hashtbl.add pfgsetmmprim "7ca85242a748607b83d19a209a2f970533d1f88d4f13a217b53df3639cd87b08" 713;;
Hashtbl.add pfgsetmmprim "caabae3022641769eb79e91a72eab9da42feb83b93bb42289befdd56b0646e23" 714;;
Hashtbl.add pfgsetmmprim "831a8dbc82333a25be3366b080cdc369ac6f943c53b8e301c297b04af7e789ed" 715;;
Hashtbl.add pfgsetmmprim "8f6ea8bd041e78ac2d8afeffed60941532d7b1d7700ba077331b1141e663db7f" 716;;
Hashtbl.add pfgsetmmprim "97d3ff674c7d3ab5a3985a032dc21315d02bcf9e4e7d411d0d8981a7472e77c3" 717;;
Hashtbl.add pfgsetmmprim "1da74f1316fea3a489341fe14044c82e34e2fabbc6f8cb3ffe10d327a29255ce" 718;;
Hashtbl.add pfgsetmmprim "4984f9bb2fb2c312bf834ddf99ede01e597cd87582cfc41824fc3699a13a71f8" 719;;
Hashtbl.add pfgsetmmprim "3ab69460d82730f5042d54ac0b6e91f76514034f74b598ef260862d4d0e68f2b" 720;;
Hashtbl.add pfgsetmmprim "25d4af5aa910dbadcbe545d381f33a27977b7011ff1ad816da3896110662db8e" 721;;
Hashtbl.add pfgsetmmprim "cbd9c2b09e70231c177502609bcabd8424525e7948a83ad78d97f3e47b64458d" 722;;
Hashtbl.add pfgsetmmprim "645dae26f8f0d12211c01e57fb8fc7b181c3a72e2fed406ec8e2291fbe846c9f" 723;;
Hashtbl.add pfgsetmmprim "efc2394a4ac49ff92f023637555e0dc2dd39badd9d82a9d73b7efa11ccbb2b87" 724;;
Hashtbl.add pfgsetmmprim "c078f583c73e20c4cc508da50c73d357ac1d3f768ac5d9bcf93934946877d413" 725;;
Hashtbl.add pfgsetmmprim "f8fbd4b42698112be76953d091cba69296e04e23c86c4211056d9f22627524d6" 726;;
Hashtbl.add pfgsetmmprim "8c1fa120abef6ed9be964837bf6aa0ed9f6696c90e7a132eb55598782460257b" 727;;
Hashtbl.add pfgsetmmprim "f1d8c7bb60b46f276a59d76eb0aa8b12761a30bbe99cf26624c548d03b17d4e0" 728;;
Hashtbl.add pfgsetmmprim "63de2918eeee39dbf4462f8fc7275cf1dd84c71a958297347bc8751c18cef44d" 729;;
Hashtbl.add pfgsetmmprim "eae00a6088637a0ea2c89b1d33d4c640bebfc8f96efeb1c2ec145fce7e87a6d8" 730;;
Hashtbl.add pfgsetmmprim "4cc956d8076b2d2d48580157905ad0a7ff105c1762a2580bada12249182d1663" 731;;
Hashtbl.add pfgsetmmprim "2b81005fe69f1538609e3d1602c9fce5ffcd90216bb5ac24899de614efd6e483" 732;;
Hashtbl.add pfgsetmmprim "574e20f568bc81c9e175dc71e5fd4214373f492c47c3345e6e6280a042e3466e" 733;;
Hashtbl.add pfgsetmmprim "d7aa3175ba07351868efd560a079960d9a818ae48f465c3d1979c2e9465d5d0b" 734;;
Hashtbl.add pfgsetmmprim "725cddabc5f69015c8901320e6e13c1e704c6ac08cc23076422a4f05c7d62d5a" 735;;
Hashtbl.add pfgsetmmprim "3a9e369af29659ab31002ba90b006cebdb35f90149bd0b052e35b184d7a322d2" 736;;
Hashtbl.add pfgsetmmprim "0c730f26aa8db03b19a12ec53fc9915019614440fce049e880da73396ebc78fd" 737;;
Hashtbl.add pfgsetmmprim "24595d1daa4f1da1ab1c0e8b4373e7074dd25209d37469e3b3f9f1c7c6ff41ff" 738;;
Hashtbl.add pfgsetmmprim "393bc7f4c4ed2988a17767bb2c5225096baa97451f0c9c1b27e6529d8195c293" 739;;
Hashtbl.add pfgsetmmprim "ce29e6c599aaf819f08a4ff74304b319e3e4b61de8a72e064f1197ad3d093df7" 740;;
Hashtbl.add pfgsetmmprim "d4e082bf41a7ac64de2708d7f5f9d61fd873a9c16a3826f899d81d84a48a8c06" 741;;
Hashtbl.add pfgsetmmprim "015bf68ae23b59738221714e37452bac7850155b703cf7b841aa2d1fa5ea095d" 742;;
Hashtbl.add pfgsetmmprim "9f1f247635fe6f9e423a9c4e7f944f7f29df212db7ccae4de075907118d8e2d0" 743;;
Hashtbl.add pfgsetmmprim "76f9c207be3b02b7a309d48f444da54f4d005dc88d545b59d0502ec7e01f986f" 744;;
Hashtbl.add pfgsetmmprim "ca64ca05dac8032a0f6948b071468daada52a0c6c536cb0d9b0623fee43de8b7" 745;;
Hashtbl.add pfgsetmmprim "0a1e134ae1d60a8b1bb1bab8fbae35e240770a84e1645625196e614c4522f9c0" 746;;
Hashtbl.add pfgsetmmprim "46334e6a06e4b482086cfc5e9bdf3881efb95a88ca21673ae743e7defe304602" 747;;
Hashtbl.add pfgsetmmprim "a34c189222538e3ef9d9fae3c62d3a47486cd92b13b03b313a81b8932190895b" 748;;
Hashtbl.add pfgsetmmprim "192ab346dfef8d2fcdafffe9ffbc8b42d64ff3002b6e63be19f4fbe3dd2fc998" 749;;
Hashtbl.add pfgsetmmprim "2b5d72fc29cfb71b8b5890d8ec42470c65cd72bcaf29850447be1784760ab77a" 750;;
Hashtbl.add pfgsetmmprim "907b1851533a5bc23193febe5912ecbbaa3a58317de46299a4201513e49ea355" 751;;
Hashtbl.add pfgsetmmprim "217cc4dba16877c52fb63fa29b1e92164c6c019337a39211bc0a53173d065f5a" 752;;
Hashtbl.add pfgsetmmprim "ef2444f228ae074c11fc2d18b6e0ce0c64a65e2a5be29fbb0a5fba33d55d5bdf" 753;;
Hashtbl.add pfgsetmmprim "e0373225b40eaf33ede51b18680986a97c720cd496040bc0d52cff3a33f681c9" 754;;
Hashtbl.add pfgsetmmprim "cec4362bd0dba3ddd282cb6c73ac638efccdebf906ae58dd63f73eb71e1a61bc" 755;;
Hashtbl.add pfgsetmmprim "8bcfc95aba325604cf0ce4ebc0445795f08f0ff447b1d8f38b3d1f6edde5f2ee" 756;;
Hashtbl.add pfgsetmmprim "c5770cafc01e034d2d3ab1c9f04291161daa20409f230b2c95c85214d3717333" 757;;
Hashtbl.add pfgsetmmprim "331749c8ee43761fe4d40390d83c33d9056603725aa3d5f1e8d7f0a8bad5dda2" 758;;
Hashtbl.add pfgsetmmprim "ecc0ac528611588095170efcbda22249f2f73a17bff398df8587fa59a0932bf7" 759;;
Hashtbl.add pfgsetmmprim "1ad6a2c4d5a753ebd3071f414f5a1b0a10d067a2848c59b7ad8e3a3b6b5d8d32" 760;;
Hashtbl.add pfgsetmmprim "a396e763c23fafad1c1f2e40a01493aad1c56d543de3aa1396f0487c4de77535" 761;;
Hashtbl.add pfgsetmmprim "1e7ddabd5dab121c55172ab25b68d77832db210694e869d01831abbe930f36fb" 762;;
Hashtbl.add pfgsetmmprim "c0a17ccc244d5309a75d823f2fdceb282155ee39dcc71e8c52a04e728cbbf23c" 763;;
Hashtbl.add pfgsetmmprim "2af037175f0da69ad639f862298b3ab39872b1d9fc7d5ef05059fffd8a4d4652" 764;;
Hashtbl.add pfgsetmmprim "4f5a91bd8a05a00f959e6077809c2fba8d689a3cc53704023cadfee375c725d3" 765;;
Hashtbl.add pfgsetmmprim "79514a25d20de3cf27adbe7b7a5e9ea43fbad420ab9a6d74aeaea4fda1aca7a7" 766;;
Hashtbl.add pfgsetmmprim "8e8415252794a093c3200bf1807ced8b783ea7f13827127d75ece5cc15a68bf7" 767;;
Hashtbl.add pfgsetmmprim "5c2cf3237c8c0d126331c0c9a01331f5204f3caf8dd4591ae09b376d84f17862" 768;;
Hashtbl.add pfgsetmmprim "7846273bb4e96b5afd08022826c72a782012deb6c10f5f1311706d05db6f88a7" 769;;
Hashtbl.add pfgsetmmprim "9bb5c12b2942d85d8022753d432cdd0dd584657511be4b59de87381fc1e98c91" 770;;
Hashtbl.add pfgsetmmprim "79b10b3545fb8c859f9501ae75950ca0a438e62e94eebce7a7e77ff99c36425f" 771;;
Hashtbl.add pfgsetmmprim "83e32d9ad99ab7341de499c971587ed87e0353eb5504283531cb4559b27eef64" 772;;
Hashtbl.add pfgsetmmprim "9edb228e7028c5870902bac629e46909261cffe5da5610c4add88496e7bd5bb2" 773;;
Hashtbl.add pfgsetmmprim "972aad5e24cf153efe8965bba1becb4fabd8e8d4c5b126f6506034b775b824e2" 774;;
Hashtbl.add pfgsetmmprim "fb3b45a6f46740adf931ec3a05e1d8d235307ea1b62512c024bb206c67d55227" 775;;
Hashtbl.add pfgsetmmprim "e9be1daf6bcfaff7624f92c91320e93870432747385e596d7eb138cdbff04d04" 776;;
Hashtbl.add pfgsetmmprim "a9867c61fa27b8ef8637d6f872a55bf64568035b708e234d41a37871562628f3" 777;;
Hashtbl.add pfgsetmmprim "761f56ebd446f9b38780211aa9ec130cc454438d90d12b448fbc69216a78d53c" 778;;
Hashtbl.add pfgsetmmprim "1c409506d4d4d98478bfcdafd872649a44ba99ddbd39ef69d649ed69b7ced050" 779;;
Hashtbl.add pfgsetmmprim "a04c1a416ff3b7f3aec59b7f493cd9f38caed81d0a948a6073936807fdc2b786" 780;;
Hashtbl.add pfgsetmmprim "a12263966ce74c9142ece244a8621a2fb7a932f1de2c8aff19ed599f19287870" 781;;
Hashtbl.add pfgsetmmprim "0e879f046303797488b42fec713a9ac4502e963ebaae64d05b891e7dece18a29" 782;;
Hashtbl.add pfgsetmmprim "1e2c31cc8287fdcfc3aef1d62022738277c5ef51269a46210021f6bffc4a01c2" 783;;
Hashtbl.add pfgsetmmprim "639984621aaae23c42043bbb35b0a8071ca67649cc2ec64fe2cd22e71d2bcb66" 784;;
Hashtbl.add pfgsetmmprim "98f1a623ca990f5cecb0c53638ba83bcf438731dcd2a848c803ade70781b25d5" 785;;
Hashtbl.add pfgsetmmprim "a5baf8b596313cbba11e723c388bab3acbfc600d6c142062236f5d5a3b0e6cdb" 786;;
Hashtbl.add pfgsetmmprim "64e24de1e70ae705d3641473d077e28653d8f70af1910cd5e4e4f05cdacc1c4e" 787;;
Hashtbl.add pfgsetmmprim "65e1d18dbac8aa9a9817d63470d47a63475dc4484d49f1f7973a37df4bbc9a70" 788;;
Hashtbl.add pfgsetmmprim "e6b3909b4988cb1e968a4396789cd47acd48667452d31e3081e69e1b574e8089" 789;;
Hashtbl.add pfgsetmmprim "5b4ae8cd9ac5908692f6de9d958934ff8935d426b80119f01728265a29016dd6" 790;;
Hashtbl.add pfgsetmmprim "db019ce52b98606dd3f761d05d99e1c698397040a929f7bb2b02ad6bdfc4d470" 791;;
Hashtbl.add pfgsetmmprim "166805adea534dbcba4d4ad84e37c3efdf11870796a6161cc7331a234caf1d00" 792;;
Hashtbl.add pfgsetmmprim "83d1c8b0527016cbf65ce106eef6702aa180c9906bd538d65a61234906f653e3" 793;;
Hashtbl.add pfgsetmmprim "64899eb32854b7220142bcd9c5567330b6bc226804b41ab628fdc7ceb8e5f7e9" 794;;
Hashtbl.add pfgsetmmprim "81a078074850f383b2414a59c95449db255ef2358cd783e2ee25bc9453b143b4" 795;;
Hashtbl.add pfgsetmmprim "6cc27d410c8c21ce6fa4a729398656676ffcd69b46f151b1770615c496f2c254" 796;;
Hashtbl.add pfgsetmmprim "dad010ff875e6d541c3e5f7aa2509aebd76e0b8e545651b3098cc43aaab49493" 797;;
Hashtbl.add pfgsetmmprim "e28eacd338f799e975d647859b3ffec8918ce86bcb2d9609a1070d80dfb08ff6" 798;;
Hashtbl.add pfgsetmmprim "b911cd2ab72d04bd0e6f10e42b4362021b3a0f208281c60819adc80501e4a184" 799;;
Hashtbl.add pfgsetmmprim "886c31120ab84752c9fe8065b2b0d162e3f9a332755d63ce04a8b1bd90885846" 800;;
Hashtbl.add pfgsetmmprim "9e8b8aec554854d0283ba2838d5bb0eef1e450b62c0a3d73276a8c4ab2380b02" 801;;
Hashtbl.add pfgsetmmprim "23546d97aef054f799c3f1d1f6add8195500225b08e118e58b2c35c0a499fe73" 802;;
Hashtbl.add pfgsetmmprim "7506ce490b7c7b77c5a23eb7d2dcbac07f36a106c70a0f63d0c60d3c06aac6ec" 803;;
Hashtbl.add pfgsetmmprim "12404b6f3172598de5c52bcdb2c31a0fd3cd537c4e8ed1519ce5190679addeb9" 804;;
Hashtbl.add pfgsetmmprim "2381790fd443714d18cf51555b0f0585861b083ffa8708f9ba073921090087a0" 805;;
Hashtbl.add pfgsetmmprim "9ad9e8be4cb98d2986bd7139e891674e8e9289d5976bb245d9ca81ed2cbc8b45" 806;;
Hashtbl.add pfgsetmmprim "19e883c292c4241889fcdbccc3ea6f951d925003425606646f06478dec3e928e" 807;;
Hashtbl.add pfgsetmmprim "a2d3e5156d64b5f0a53e2c4f1bba02ee3921278ee298aceefaee6e1f4d07afb8" 808;;
Hashtbl.add pfgsetmmprim "30ff4f938fafce6e981de868e25a151f08ceef53cdd112f8d1eef0066674f136" 809;;
Hashtbl.add pfgsetmmprim "c2458a246dc3dd3fa4258f4f8f4aa37c57171cb93cc71de5eb209849f60f7179" 810;;
Hashtbl.add pfgsetmmprim "086faf70da961534d59b6299289f0aae8b68521def1c354ee7344b1cbe050823" 811;;
Hashtbl.add pfgsetmmprim "29f952fc4b808a1fc1b8c113fc81b4e85f27ddf298ea865a4ce7c6b519a33b6f" 812;;
Hashtbl.add pfgsetmmprim "1b421f03111380f5e5cfe9c6e7b299c46fe5a881dbfdba87b2b9b0f00d21dbfc" 813;;
Hashtbl.add pfgsetmmprim "b2b383a15d5aea8eaf6683b18b50e3c8c0aa14f9e6042d27614bed7323f722bc" 814;;
Hashtbl.add pfgsetmmprim "c2ec6282cb92cbd09d10ded9616adfa17f4950a58a07952487f064e5cfe56ba1" 815;;
Hashtbl.add pfgsetmmprim "6d371e951f83f0ed9f7aa08acdcb157515ba2d8f0f9bfebbe864b28128cddc74" 816;;
Hashtbl.add pfgsetmmprim "8045092d6e8bd4ed0999bc1c0e4855c9b505e278acb564d0d7c79ff4008664f7" 817;;
Hashtbl.add pfgsetmmprim "4dc70f89715ed698476e77892f58f4fd3d39001e570e63b35e29f65bdfe866ed" 818;;
Hashtbl.add pfgsetmmprim "f0d12c3d78ff1aab70713603fae3166e8ec7ad0d204804b6b93ae8486b691b8e" 819;;
Hashtbl.add pfgsetmmprim "d21855fe337a1827321fb8b0241da6380434c1d0c406d1e6538d0d16e4019501" 820;;
Hashtbl.add pfgsetmmprim "4d322a6487bb7b2d87b17c3a330b4aeb345c437f1a45fc4977695937354ab069" 821;;
Hashtbl.add pfgsetmmprim "db20375e1d518db3d535ac7059ee6bb5a61b935abb82b9f588e41603ae341af3" 822;;
Hashtbl.add pfgsetmmprim "0b679f5b0c63fda1382379d4b48f4dc70f36cd78ecfde89112617567b61f0501" 823;;
Hashtbl.add pfgsetmmprim "5132bd5e1e64609b8ed1fc7addf0801cc6702fa61deb76e74cda1e27d5e4c112" 824;;
Hashtbl.add pfgsetmmprim "43b1e180ee248309fe7515afa59a47ab1dabb6933082a4c778d050a3ccd4c6da" 825;;
Hashtbl.add pfgsetmmprim "f96d33ecca963c7a3656ac2c088c02837ed1efc00155eb3f9418ba6779fb6c29" 826;;
Hashtbl.add pfgsetmmprim "4930af8ae98703e4aaa7ff2d9a612e4e68f357fbde1e3d101330fa9d1b7a3448" 827;;
Hashtbl.add pfgsetmmprim "f971491abca28ac645c9c1b37a0226cc5f523073d764db50ea4d2943b436dbcb" 828;;
Hashtbl.add pfgsetmmprim "12cd9f3b2ec562bdcf45a7220d7812351c4b68accdee1e234b5bcffd8165bab9" 829;;
Hashtbl.add pfgsetmmprim "80cdd840cbbc29f4e1b1ff957145634f18f6a199287989cf33caf6c2f56f2f28" 830;;
Hashtbl.add pfgsetmmprim "5977b9ba6729eb7839ccbe9b6afe4ba4b65426336255e91375a1f6edbbec645e" 831;;
Hashtbl.add pfgsetmmprim "3bed1b44a00e975bf31c448f8d7681e0a0f6fabc93f176195819b437866c8114" 832;;
Hashtbl.add pfgsetmmprim "290832b94ebaf9f5e30138b948c86554e21711f313e6c6f97a1fde18e0a5fb0b" 833;;
Hashtbl.add pfgsetmmprim "d09844bc318b431693fa7f8f6703582067de026a6ea4b1d653ae48cef26bf13b" 834;;
Hashtbl.add pfgsetmmprim "47345023bc65c1fabb68f163ec470d2e7f7908eed38c3455a35b83cff0cbccc5" 835;;
Hashtbl.add pfgsetmmprim "1999959641d7c5f7f3ed48292a3fe7194d4e7047fa2b57eb63dd761b12fb42cb" 836;;
Hashtbl.add pfgsetmmprim "9ba15e6c3b13322d8830a4b567d45883f7b58d789b850966c54591385cf09692" 837;;
Hashtbl.add pfgsetmmprim "ffe9e2698b575de46b00dbba16aef605df11290d776f32dd23dbad29e8ce05dd" 838;;
Hashtbl.add pfgsetmmprim "69efb1431cceefa265e509400d87e8f6675ec6940bc490d1821bafc624c4923c" 839;;
Hashtbl.add pfgsetmmprim "4cf8bffead6f48cd31456319c69a71ec399eaa179c9f30ad974a935b889ecf64" 840;;
Hashtbl.add pfgsetmmprim "28366c82f242417ae11df8dd8b8d25d9916c577484416b624e83d05324ea5dd4" 841;;
Hashtbl.add pfgsetmmprim "5cc5140f6a59854a08d28ee1c2c37207b7865a9cd1591639061a7f7b1cb45bd7" 842;;
Hashtbl.add pfgsetmmprim "461d1b6229aa5ddb9f34bf55e746e2aa7b8ac94408a6a61f5b9da1ee5ad188d3" 843;;
Hashtbl.add pfgsetmmprim "237bfb38d024385b591eaf5cbff60f213d7ca0f15d050ffe28cf6174ef99e2c3" 844;;
Hashtbl.add pfgsetmmprim "f0c82614004d6f8dc8b14c36233a1e8735c3fb6c008bc957b5c2975546f1c857" 845;;
Hashtbl.add pfgsetmmprim "4a5757f4fe64e519463b4ae3ae73c45b353cd5a100634e5dbb61ed75a5d99e2f" 846;;
Hashtbl.add pfgsetmmprim "6bcaabe6750f806fe6ab3186c5c85b9b702e6df2181aa3b58feddd368492457d" 847;;
Hashtbl.add pfgsetmmprim "df0b7968f44a5fddaaa88971212b06c62671b9ad151fadd4568a26e53dbb56db" 848;;
Hashtbl.add pfgsetmmprim "2dc5ebb10d0526b3b9e1d9eb712836bfbd1b3e17c642a2dfc332285f63ce74aa" 849;;
Hashtbl.add pfgsetmmprim "ea96bfb534cb64baf3df4305f6510a2352fabf240518ab58be407b6acab69e85" 850;;
Hashtbl.add pfgsetmmprim "17c5086303036b0a1c1df146d0a4bddd2b09c0bb21e423deed48cb9c26a6af76" 851;;
Hashtbl.add pfgsetmmprim "96162265f852470a462d877ac6360699503ffe2566cddf18c27e05d955840f79" 852;;
Hashtbl.add pfgsetmmprim "3fc8212abcd022ba73956ede6594b281998b690f7ce5f1e1996b94df545f1166" 853;;
Hashtbl.add pfgsetmmprim "a85cae193f59373dc05df5e0d94891b9ec7cd52b77ee1c1acf3e4c8894b4b4e5" 854;;
Hashtbl.add pfgsetmmprim "af7376eaac8b4ab57af213dd88ce60ce5387cff16e3cfb7d8e298f48ea65c093" 855;;
Hashtbl.add pfgsetmmprim "110e030cd6fd6ec93fa22c1c348175483e1158240d1be4024e7abe3d80b61b15" 856;;
Hashtbl.add pfgsetmmprim "26b22c8995c7e09002c44cbac4c479bb253a1aa94d8506737238cf4b0bc8a8e8" 857;;
Hashtbl.add pfgsetmmprim "74bfc2a215d7faaf9cdc392075ace9dfcf2fd3e4bdfd71d2d3fe8470618490f4" 858;;
Hashtbl.add pfgsetmmprim "9fd31c766eaeb0fe6bde7aa440f6c9444adcebc3009409e8e3bd3b362a59c42a" 859;;
Hashtbl.add pfgsetmmprim "f7dff31030b9da03553a8c72eebc095a3e239b05c88fd0212bc38e47a10448ba" 860;;
Hashtbl.add pfgsetmmprim "fc61a1862668e525a841af852e75d6bb2581484ab890c8b31292a6204251e4ad" 861;;
Hashtbl.add pfgsetmmprim "1e0363788b15dc7690f526456d39a8c59c71d00e673eb5548facd07675671ec0" 862;;
Hashtbl.add pfgsetmmprim "44cb677e0c4cdb41c9cd882e9f7e0c095f212df3cf88afc3f3f069291be88878" 863;;
Hashtbl.add pfgsetmmprim "a2625ad46db46dd61ddbd8fb3f8153b752fcf4a51a89074f6a259212b0cb11c4" 864;;
Hashtbl.add pfgsetmmprim "79acbf98b292514b5250f9f0d2d3de58752176d6d7615af784515b4cadee1c79" 865;;
Hashtbl.add pfgsetmmprim "e4b5bebb81542ea7c8373984a6210b88adcaeb64e74f8e3c3e252f0ff3706bf8" 866;;
Hashtbl.add pfgsetmmprim "754212c105d95ce96086fffd25fce4d3ab1ef6657bcf100002e3b4513da5719f" 867;;
Hashtbl.add pfgsetmmprim "d1e9276f934fe807649118d42bdf1e21eb3305e45af57ea9f441cae5bb125a9e" 868;;
Hashtbl.add pfgsetmmprim "2e6758216796e0b9c2ff9e7a9500259a408d686c3d611a87785cc791cd1dc22f" 869;;
Hashtbl.add pfgsetmmprim "3694babec2e69fbac57d6b377b306656c17402cd063de81d15ad74bde8a3fb53" 870;;
Hashtbl.add pfgsetmmprim "9a8eb1319e5c2fc45b6c62adabf68d5c1582886d760c7d1ac255705b89097f50" 871;;
Hashtbl.add pfgsetmmprim "540b96f93e74179ba1a65dc25baae15f661c6b08c8a3b0bd7bf860dc40369708" 872;;
Hashtbl.add pfgsetmmprim "1cbb9928fd0c9823e4fd2079a8964aea3f2c57a68c0c180d56457411b607919f" 873;;
Hashtbl.add pfgsetmmprim "74b712eaa422b15c3d6d5979ca83c2e736ade45dbdf7c1dd8095cc061ef3b932" 874;;
Hashtbl.add pfgsetmmprim "eee99c3efbbab9a6ab38616a776468742dbf9850fb1d9ae64ece50491acc9e18" 875;;
Hashtbl.add pfgsetmmprim "8e32fa389f9fd90a77b9cfa57165fcae8f743ef43fc49860be3af318ce822021" 876;;
Hashtbl.add pfgsetmmprim "84c9c0fa6b15b4662e17c1e7b947dec73ce78887d427f8f12bd2890d5aca0c1a" 877;;
Hashtbl.add pfgsetmmprim "8fc05f19f077c93aba7be1b0d13b5e909261a2a0e1b8579d9c63c26eb082cfd2" 878;;
Hashtbl.add pfgsetmmprim "8715939004ce4304fad0a584dab9008b26e0aeff5a72b5202f12b82eae4c6588" 879;;
Hashtbl.add pfgsetmmprim "f072206a77a958e4153fab326e8b0d5ec49cc2773572b2e6eff71277ab1a77e0" 880;;
Hashtbl.add pfgsetmmprim "ba593d259efd2dac04a4f37c7dfbb5dfb948b02e31ea3196f8e8d03f0caaeabe" 881;;
Hashtbl.add pfgsetmmprim "331e633464145073d619c6281b3d00a96ced196ea6f3672de3149e455d9c1a12" 882;;
Hashtbl.add pfgsetmmprim "f1af3a74c1256497f6df72b4e3d2f0a232fee67fe8da7521d4702ff9fec6c9fd" 883;;
Hashtbl.add pfgsetmmprim "0ff568c1538911b2fd2564f8ae010e293d638e03d7471db6e844870d4fcc4c56" 884;;
Hashtbl.add pfgsetmmprim "f25a3bf5ece575a2f755631acd27615a03a4c49fd9128f81c2ae06c146eaf9b2" 885;;
Hashtbl.add pfgsetmmprim "e0c1a0dc55514e727b5a14e3b3f3fbbd09b6ea50b88b56f8ff2b00431bb47df1" 886;;
Hashtbl.add pfgsetmmprim "7cea3961534b92fef764d58fca67ffcd07a9f675118c5a4bf970f1dd04c59a2c" 887;;
Hashtbl.add pfgsetmmprim "37c611007601187676d968cef84420aca50cf4fe2464c7a9fa20dd4cc1860218" 888;;
Hashtbl.add pfgsetmmprim "26a2083f13d34aba9100c26079c52f8d0336e06887cff39968ecdc69044dd31e" 889;;
Hashtbl.add pfgsetmmprim "b030167973e5418fadd941c37ee448f4ad510b53a3fd03367764ad91d9b600f0" 890;;
Hashtbl.add pfgsetmmprim "67b7408e183150630b8cdf4574ad1692ff99771eef4c400fc1a660034f14aae2" 891;;
Hashtbl.add pfgsetmmprim "321f8a3153ed29eebc968d5ee007173ed5bda6a8efead4bb0c07424e569d4554" 892;;
Hashtbl.add pfgsetmmprim "ecc0a2fce0a345848576b26028b26a4d0f86393f2e5201ec872fd58451de0f81" 893;;
Hashtbl.add pfgsetmmprim "278222d342f49845c14affb3d72e4e3a50536ef312267cb16b154bf0fddcc194" 894;;
Hashtbl.add pfgsetmmprim "7e93fbf2e7b4a7ed48e894642d8d0f747a0d920005e94b704a6d3d9c79b46847" 895;;
Hashtbl.add pfgsetmmprim "1caa84ee389d630776f37f8a471c165066c59fc45faedf06392ad91a52702807" 896;;
Hashtbl.add pfgsetmmprim "986f471250eda8f65e22ffe2be9e0c425e785ffa6bfec2ea80fce1cc261708d3" 897;;
Hashtbl.add pfgsetmmprim "68ba66bcf21afd28d663d7c30d71f6cbd4290f35ef0e781d162dd3eaf3f4c687" 898;;
Hashtbl.add pfgsetmmprim "6528ae8df48dc5090714e86920b68daed18f1bd65354615030a0327c1722888a" 899;;
Hashtbl.add pfgsetmmprim "2f42049bb75edd03c845d80246a5dc6f7ffec3f3290fc14c2cdda526a7787d9f" 900;;
Hashtbl.add pfgsetmmprim "f79052302c08a70ad6ac58b84453da191de016f46b5cca923b8af74562c5ee2c" 901;;
Hashtbl.add pfgsetmmprim "dddc117227ec28a0e99c579dce5a14c93e431d9769c29c5b429a42dd0887b9fb" 902;;
Hashtbl.add pfgsetmmprim "35a6c39621849850caff0f4bb12a23bf0b1198e91cb86ea76f1e72ac371ec21f" 903;;
Hashtbl.add pfgsetmmprim "d10d205c0d174f758217633add6c80280263d01b7af16e02eb9acefee1d3b352" 904;;
Hashtbl.add pfgsetmmprim "4e618e1e9db49008b4a4546a6decf675c81e66c58e487249d2bea024554c7836" 905;;
Hashtbl.add pfgsetmmprim "7e103d1b1dcceb6f6ba585c72d5dcdfeb6db424b87827a66d3ccbbbba250f20d" 906;;
Hashtbl.add pfgsetmmprim "fbc90b708d02597318796fdf0c8e2fb617c33a25e28d011c79dd5f6a0061f686" 907;;
Hashtbl.add pfgsetmmprim "2be179997346c162ff6dbc47463033c1e432fe258993008ec222042cc8b67cd8" 908;;
Hashtbl.add pfgsetmmprim "7f0f60dfcab5d07d658c7b15262cd79f067c385161a137c68d72cc96f72534ca" 909;;
Hashtbl.add pfgsetmmprim "65058836b4939358c216ddb95b56bc02a4b009024907bf1eba84e3ca86d4d86e" 910;;
Hashtbl.add pfgsetmmprim "cb00de7dcf5e41929a6f8afc5a79121199f31396e437f9013dde3b3f39c509de" 911;;
Hashtbl.add pfgsetmmprim "0c08c4cf4ac930477d48cd87daace29d1864ea033a7ca451431705c057f59ef2" 912;;
Hashtbl.add pfgsetmmprim "fc6894b3b46419254e0878f5710914eedbb7f184be403ad9f4822158173f73d7" 913;;
Hashtbl.add pfgsetmmprim "ae27dff45ed03f34e99e93ab1c8d81e8817b8eba1988292f5dbc85ec07716619" 914;;
Hashtbl.add pfgsetmmprim "2d618619d43f59e938654a4ffc5c8e37f6222956e270b96ff1235d6444cd4304" 915;;
Hashtbl.add pfgsetmmprim "8e454ac9d487438df46ac8ebb98bf82cf5df05549ee35914e79962ae523d1ba0" 916;;
Hashtbl.add pfgsetmmprim "0e87cc32273ddfb3989b34c3f285c2f1b04694710f3dfc52575131258d815a68" 917;;
Hashtbl.add pfgsetmmprim "2f75c475819a4897e5437e01c67c697c89191a34fe018daed1c60f026bb88469" 918;;
Hashtbl.add pfgsetmmprim "6afbec01ec653da7d5058e670a3572788d73254e68ea8ea14fa9e55edf246754" 919;;
Hashtbl.add pfgsetmmprim "19d468de2a479fe1f6642a416d00bfe2e1788875baad8cd5934cbcdf588c1164" 920;;
Hashtbl.add pfgsetmmprim "4e129a5067d28ba14fd8919f3be7a2d0afafa1a5562baf82d6c5d465c0b1b5ec" 921;;
Hashtbl.add pfgsetmmprim "9532ee17abbd9123a785ae8d800a34174af0d6d17ed90b69828c7aea31e36186" 922;;
Hashtbl.add pfgsetmmprim "0150339659881fb0470df87fc39917cc68ea0d056bb5722611f29eeeb9cd0d61" 923;;
Hashtbl.add pfgsetmmprim "293a9fdcb462fd411871d84c130354eae4548fe5eabc654959b95c1eb1328790" 924;;
Hashtbl.add pfgsetmmprim "76d741c47e4811495f33d2003650b2f2fc0d071b076d55ad2a28bbfc8991d141" 925;;
Hashtbl.add pfgsetmmprim "2da148788a8d50d6efd00a56574ff2ac5dbc1f3467ed9e56358f35825bb1fd8b" 926;;
Hashtbl.add pfgsetmmprim "4ce0197522c877ec493b5b6668b98ba51b68701c059c647f547903f61dc43770" 927;;
Hashtbl.add pfgsetmmprim "aa48e8896590cf748970b961c1bc8004b5f52171f4f2802bcd44a3982edfc863" 928;;
Hashtbl.add pfgsetmmprim "bdec61a380d62f2007562a61ce7ba23511bce4b4e63f46fce426b8787c6cc03d" 929;;
Hashtbl.add pfgsetmmprim "8f45b6834651647af171cce3b2d174daea03f6455862c58bae6d14a6000da802" 930;;
Hashtbl.add pfgsetmmprim "8e7723e1cc0a634aa1752a4358dd286a8473074c68f62821809b92c3f03643cc" 931;;
Hashtbl.add pfgsetmmprim "05e6a73b94388dea849c58600ed3c898227c3d314d4285af241d8eb6e6904f46" 932;;
Hashtbl.add pfgsetmmprim "8c257802cc7df77c238ccee93ec8bed29c51861d4d2d6c953caadbbfd4d8a68a" 933;;
Hashtbl.add pfgsetmmprim "cd18664937e784a5fd302965894bc6c43259cc53ed4ddd9737fc0dac9e171f4c" 934;;
Hashtbl.add pfgsetmmprim "c133a183eef1c0aee70a0618c46b6446a708183de4785832dbddb73994b05a15" 935;;
Hashtbl.add pfgsetmmprim "5313dfc5bcc348a0cc6c58eb3da012809243033d3191b369966e42b58de82438" 936;;
Hashtbl.add pfgsetmmprim "6332fba59129a0a475637c6ec68163966b7084249ecd0ffeac85b02ab382bdaa" 937;;
Hashtbl.add pfgsetmmprim "51999121d6ddb6a807f20c2cd3b325d2d2533eb9a736744fefe15b677d49cb87" 938;;
Hashtbl.add pfgsetmmprim "7eddcfd7ad85aaecc74dde13f4557538952dc938e7a58f82f03d6e8df98c366d" 939;;
Hashtbl.add pfgsetmmprim "eca4da92b49dad92645d7714c1d842e6ec46b895c58e635c20523162174c1ed4" 940;;
Hashtbl.add pfgsetmmprim "6f14e12c446c97e3f9dbc13e6d0f363cd960b3578ccc9244e1b100a59ff2349c" 941;;
Hashtbl.add pfgsetmmprim "3dc52df8737237eba69798756c4a5cc38cb77390b971d7a95755085509d59578" 942;;
Hashtbl.add pfgsetmmprim "19b53863e5f803ed200294b98d9dc6edc79ae7f5b5e8635f1832429cfc8a2de8" 943;;
Hashtbl.add pfgsetmmprim "076e61d6578bbb602f851d4b23786a63d07844e9baa98ad183a8bfc13a306912" 944;;
Hashtbl.add pfgsetmmprim "602e326ce51c3368db0866581aa5d6f8be353992e34601308bc158a2c27e720e" 945;;
Hashtbl.add pfgsetmmprim "061df7d67f194494eabdb52709886f098c7fdaae73bcd85ff7adf443ca77a5d2" 946;;
Hashtbl.add pfgsetmmprim "60c57a52850cda97b5a98758f3a4f83898316b18fef54a2a792cafd0a716bf9e" 947;;
Hashtbl.add pfgsetmmprim "a4ed4c84946ff3d8eb41320ce4c4ffbb7094147b50dd878d18178e231a5f89a0" 948;;
Hashtbl.add pfgsetmmprim "ae9308a39157518a01828cf8b38ef7aa8a68125bd997242c5475d1e67da97647" 949;;
Hashtbl.add pfgsetmmprim "a70c13d82b6dc520e375ab88d2de70c7f3012553ff508b6ae3be086036c50565" 950;;
Hashtbl.add pfgsetmmprim "5f4acadd5df67100d59dd9521d2e8b01fda63af525aaf21c00656274e3fdd7fa" 951;;
Hashtbl.add pfgsetmmprim "838a83b607b948b159e975135e019c261b8e3b56d6c2d659d67795b88b5487ba" 952;;
Hashtbl.add pfgsetmmprim "4867d4e440e7c5cd0700c4bcc194dea4f9b359ce25684863b11ab3b2081dedd8" 953;;
Hashtbl.add pfgsetmmprim "3e0368c9b226f53dc627ece6cb81e2a166bafcdd7edc80df6db11ca542600e33" 954;;
Hashtbl.add pfgsetmmprim "3a8eb3256ed410ca7cd430aee696e50958d3f1f45447a0ecacb4eb1e94dc47b1" 955;;
Hashtbl.add pfgsetmmprim "65571b8e60f686d3548d485fd8986980044a52f56b9359639eca68e163a09b5d" 956;;
Hashtbl.add pfgsetmmprim "fc60d914b9df028aa716d9538d83d50bbb98db10b87a1a776d41ca1bba47f1ec" 957;;
Hashtbl.add pfgsetmmprim "f9d206f58e189a1caf1b7f36d0a099b8524c07d2295d04a168fca2658d5d49a6" 958;;
Hashtbl.add pfgsetmmprim "df6acb391cffaa5a59b0600c33bb1562cb71c0f0938c8f15ac21dcdde0341d8d" 959;;
Hashtbl.add pfgsetmmprim "6ac0236fff2d958092e13061428e08dd3880c5e484d9edc4f1ca3a8ebe2aece3" 960;;
Hashtbl.add pfgsetmmprim "4df6c8ac12a8f6cf2a3917e1eb8dba6e72ac8d4702bf8789b06ced0317cb33bf" 961;;
Hashtbl.add pfgsetmmprim "dcb73b7650e20846806930b1e9232a887e6104808dd8871e0805cc17106a0813" 962;;
Hashtbl.add pfgsetmmprim "21be34f551eee2a21606aa63581349091d8c8120554b5778657be796d3ef5238" 963;;
Hashtbl.add pfgsetmmprim "5b77ad28cb7f247edf18788d6a7155645bf83d8875b2c76e5cbe9694746d00d7" 964;;
Hashtbl.add pfgsetmmprim "409015ff46d2eabb27383b8a6c84c4683375750f7dcacd49d7145efe78ff78cf" 965;;
Hashtbl.add pfgsetmmprim "3648ac378a753436eb66a1721b58c25824d419d583120122c1667b87341218df" 966;;
Hashtbl.add pfgsetmmprim "6c513578d45057ac2fe824b1cef44ac20820d44e5389a0198f47340d8f2e0c2b" 967;;
Hashtbl.add pfgsetmmprim "5e1639e2ec2e64321239911617977c8bb4d4e6962338312ea75520a540f7a4ac" 968;;
Hashtbl.add pfgsetmmprim "96e01be752c8e7a19cb85214c1732812f7244aa0d31622c4c24e9d33b158e9d8" 969;;
Hashtbl.add pfgsetmmprim "38494e507ffe1de56d9ca85cbb2102fb81d12af18f9af5c3411c1b15de7c32e2" 970;;
Hashtbl.add pfgsetmmprim "b254992be6fa1d721ceab76c43243084276db85a76ac4b01069453984065c5aa" 971;;
Hashtbl.add pfgsetmmprim "98e6db95a3a6d467e0592eedc4baa151e0c9e7429a4a840869ddf9a3db032e65" 972;;
Hashtbl.add pfgsetmmprim "7325ebee9a157d892f8622cfb1a94c7374d3e55be9da94b3132d0659b0a15db1" 973;;
Hashtbl.add pfgsetmmprim "9264d98d735ac5ab13f03d6460a05ff9be39d3d7ae459b2c3902108987927549" 974;;
Hashtbl.add pfgsetmmprim "923edd7981790021ca4274cf28afcabda7f175335bdf8c44cf7c2e753c60db4c" 975;;
Hashtbl.add pfgsetmmprim "9fcefdff00f355f6e68c34c4f7fd2a456a2920421f28ce61ce6cdfe84bd9c12f" 976;;
Hashtbl.add pfgsetmmprim "d1e73e9c0ae54e447f09e5f15256645abef861d3f15df9fb7c7222fdac68f09b" 977;;
Hashtbl.add pfgsetmmprim "b9291fcebcfbaacc1fa116382bc3a0d1242dcedb540da57ed5ca2f9e83584a1a" 978;;
Hashtbl.add pfgsetmmprim "1ade0766e62bef9fd2203e5e6aae587ec72f010f4e0ad6115d04c56ed65f14c1" 979;;
Hashtbl.add pfgsetmmprim "f04c4493f57ef348370158111222e30daa42692f62c82e643f6f76fc67a73ccb" 980;;
Hashtbl.add pfgsetmmprim "a3880ad7482ae20e1f426724f495ac7666a84290390c92ec8703f86fdfc83ffa" 981;;
Hashtbl.add pfgsetmmprim "ac687dc37af54428cc20f90b228545c75d89b0c93d5ec0ebef22209fff3702d6" 982;;
Hashtbl.add pfgsetmmprim "2ade67a9808f85de2929815ef748ec6f409f5a0b043ff60763dd0ee227b74026" 983;;
Hashtbl.add pfgsetmmprim "bca532f91a4d225bb17c45c1f7a2e1304803f9f072edcd2e9a5c59b67a60926f" 984;;
Hashtbl.add pfgsetmmprim "00ea3829f202acbf39125a136f25fb167204b0e372040e46c39239ee4074efab" 985;;
Hashtbl.add pfgsetmmprim "80468324c9900e4796b242899101d11f0d1e8afc854dc7585c923ca6f121cc9e" 986;;
Hashtbl.add pfgsetmmprim "e4d64718618d5c11964c45e8d3a6d878d403ca4ebf92a1169d159a7a895f21cb" 987;;
Hashtbl.add pfgsetmmprim "3db984140dbb641a5aa92fad44714263dffdf2eb1e55436495d87f58ca303502" 988;;
Hashtbl.add pfgsetmmprim "5a52dd9f5ea39e40407768473b4be9d4548e8d36efcec24811757fe46759ce9b" 989;;
Hashtbl.add pfgsetmmprim "3b0503483e5db047043c10b9ccfbff7e63eb9d8bbdd3531b1d567db745911870" 990;;
Hashtbl.add pfgsetmmprim "ed289401d8cf4b0caf8743ea47a7f16c016c096e3157cfa1466cbeca9b17f391" 991;;
Hashtbl.add pfgsetmmprim "1bb48e8cab03552116b42216e327c5908224a69c91dc20d87ea268671b14fa03" 992;;
Hashtbl.add pfgsetmmprim "14f911fb530d5d5bcc52f9ffe8ef74cf25b96045ed457fceb867ca37088c0cd4" 993;;
Hashtbl.add pfgsetmmprim "791815c921301ab9e4d7fb2d6ed8e9d4d4f28d92449aae73f8a498c841ee4a08" 994;;
Hashtbl.add pfgsetmmprim "8f18b2cb0723786af45d67c0d674a95c94d2fbf0a316bc703c7878ce62db0d07" 995;;
Hashtbl.add pfgsetmmprim "0558c52268d1b1d1c7066f3aa98f122275b84d04b1842104c63dbbefd15288a3" 996;;
Hashtbl.add pfgsetmmprim "2b5205a7ed1e34af9d7188d1aa7eceabc50be8d35f05ae292570b2e2c204d819" 997;;
Hashtbl.add pfgsetmmprim "12c28bf554635b4a99141e0087d5433a34785045ecbbe1e1933ebece81c980b9" 998;;
Hashtbl.add pfgsetmmprim "fd92a08a899776abbba1377a6764b461e30d59169748fc5f6400d3286c308ea8" 999;;
Hashtbl.add pfgsetmmprim "2ed28816934652f220d6a1dea118cc3675adab9417b866d632200a973d0fb4d5" 1000;;
Hashtbl.add pfgsetmmprim "37ccac0b998e37cf23224a5d63f247f04fec0cdc839e84bd5c53abf5ec6d5bdc" 1001;;
Hashtbl.add pfgsetmmprim "f664439c22f4f97786fe4b755ffbc7cdb152807e82bb163e4d5173c80eb83a85" 1002;;
Hashtbl.add pfgsetmmprim "25c2c158e0b0f3ccf1b7ee3a6a814d53b10132318421fd7d1598f96c91a98bf6" 1003;;
Hashtbl.add pfgsetmmprim "1abe7c69650612d430c246dbe4964466b47353bf407a78aa87bc6848a6a71e7c" 1004;;
Hashtbl.add pfgsetmmprim "db7c8f37af0ffbc40a8eebb26320c8ec116585ba4a091befb63ea12a58017a30" 1005;;
Hashtbl.add pfgsetmmprim "119878fd5af8133790ac7b64bd0d9497df0e80be23dceec8a1f9e0a17bf0f934" 1006;;
Hashtbl.add pfgsetmmprim "b5daa010a35b39b7aeccb37693245a6e923eceaa9d232479acf29cb02d4bafdf" 1007;;
Hashtbl.add pfgsetmmprim "7aeccb3253cc5680325f605dcb42e2ff427c2df895599fed83ee1f928644da57" 1008;;
Hashtbl.add pfgsetmmprim "b7dc48cb024c577021b36b554e0a58b889eae4f3b1a08979b3e8e3734292321c" 1009;;
Hashtbl.add pfgsetmmprim "1ce779f43bdb95bc32f191d44f064de89d363c0cc02745adfee1b0053df40aad" 1010;;
Hashtbl.add pfgsetmmprim "01fa8b9a669491e1dd2713739ba739247a15fc3919975706104d89164c6186b3" 1011;;
Hashtbl.add pfgsetmmprim "12cea8e02eccf248da85be8c41c7d82030ae4e221b3dee916cd8663c98219e8c" 1012;;
Hashtbl.add pfgsetmmprim "fc0acb4ba1b885ddf1e5043d10533dcf013813bda985b53cd66d9c1891e0bae7" 1013;;
Hashtbl.add pfgsetmmprim "97e024b53f5178a0bb45228304748e6d0e6f14c6106077d1f02541b1b895298a" 1014;;
Hashtbl.add pfgsetmmprim "5fa9925317b2a364401ce89eaf303d69652cc2cf31de7ff7c935a3177c563183" 1015;;
Hashtbl.add pfgsetmmprim "e6e95e4654ca0433aa6cf1bb210cd25429cd109ce373953152663845814fb620" 1016;;
Hashtbl.add pfgsetmmprim "95a63c73d4e365bbf973669e63fd71a9649ed652e58d60d1f8cfe8c0f783adfd" 1017;;
Hashtbl.add pfgsetmmprim "9510c776c39bb22748d7c58fadecd864b3dbcdd08098ccf539bc6c7f90d19c9b" 1018;;
Hashtbl.add pfgsetmmprim "74150989921ba556ee010ef3ef6aefc3e721c6e6e13cd8ff144baeac38b9e3b4" 1019;;
Hashtbl.add pfgsetmmprim "423b87bc2416c3d14c922c4b565a8d2878477c239e5842a7bbcd205726c5153a" 1020;;
Hashtbl.add pfgsetmmprim "9467b34519a5a983a1f69dd3decbd5e647daa895376726f464f0f98103e27be3" 1021;;
Hashtbl.add pfgsetmmprim "67a0105003d05ab05dffb09dac971faff0d9befc95386b3a91b8299e743f7c31" 1022;;
Hashtbl.add pfgsetmmprim "749ac4d023b773479d67f9d70579a1df726a430351b32f8e2963af35f3ae2b35" 1023;;
Hashtbl.add pfgsetmmprim "0ef9a5055b5a22ab1e4d169b764b9cfa09b9f9770f48a16de3e54926270f60bc" 1024;;
Hashtbl.add pfgsetmmprim "b2abafedaa970df52bd50a10c39d26ce746cc4c726da2bef6ea73c3aaffcf4f4" 1025;;
Hashtbl.add pfgsetmmprim "a5fe99deefaecb794f5d993a2a796e81947e6f1818d29472fe996499a2dcb3c8" 1026;;
Hashtbl.add pfgsetmmprim "b4d6a88ee1fc9296cb64cbcdd31eb960bdcbdf5dc4a8659a577b424ac2e9bb93" 1027;;
Hashtbl.add pfgsetmmprim "a6da2bda3601ea4ccdad05e66a010008dac48f35d157c65097cc713204b39977" 1028;;
Hashtbl.add pfgsetmmprim "f43b0cd36110aeb35a11b5a565aea943ba34215065621ecc339bacd9b999323d" 1029;;
Hashtbl.add pfgsetmmprim "23f8770901175aaad17672e04f915ab2671ff0e5692bcaecd88aec6e8ce28336" 1030;;
Hashtbl.add pfgsetmmprim "36b4045760f2725eccfaabcf26519fbd2dbd64a44e1657328d9a3dde26e4ea16" 1031;;
Hashtbl.add pfgsetmmprim "745e11d6f8ce9c78a0f45589d4db19052095d190bf905ce5923a84ea936b7f24" 1032;;
Hashtbl.add pfgsetmmprim "b51b23c916ec6b3f2cbac615ef034d6fa04d868aee290d87e12c5bd764eeb7ca" 1033;;
Hashtbl.add pfgsetmmprim "9fec3b75e3c604fdb396979c82748c358c66d553b0d1adcf2504482fb988559d" 1034;;
Hashtbl.add pfgsetmmprim "421b0413729876e745b87df406b90eec164d742d9b69c8a2366e51a5ca6acd8c" 1035;;
Hashtbl.add pfgsetmmprim "0c63366c726f6167b644230aef2094279e049d642046a7decc32640f589585d2" 1036;;
Hashtbl.add pfgsetmmprim "488978f700cbf678a8cb87cdbe8c2164a0ffd656d37154ca858e69c1bd274309" 1037;;
Hashtbl.add pfgsetmmprim "fd7e53bc21ad0b59dee539d10d91e42c8e0c24ab8054194f67547cae057cf075" 1038;;
Hashtbl.add pfgsetmmprim "6e5444d6e25ae82ea279e13ae0962eab72953d060530a9ea9a5bd8d46ae3f470" 1039;;
Hashtbl.add pfgsetmmprim "af6590e381b85817076bc3fc5c1d76b1d81be9e13f797200a4ba1c464fbd0412" 1040;;
Hashtbl.add pfgsetmmprim "598069ba61984a983c2165057c6fd07daa89ed5cdbd1ac99c575c365769a26b1" 1041;;
Hashtbl.add pfgsetmmprim "6a0c098df9ddf52926bf24db0e4ba017e710919b4097a9c03f482f737e084863" 1042;;
Hashtbl.add pfgsetmmprim "35c7f82c9dd8efb974da79c4e7daaa5a4b17f03b50fe7aac7738c36c94ae1b28" 1043;;
Hashtbl.add pfgsetmmprim "5716aa2b08653ff03cc7aeeffb69413c90a4e88e073320166888461e75c45067" 1044;;
Hashtbl.add pfgsetmmprim "d5dcb651b53d23236e2c37656acd9748c0a6a3509f66d0b687c231837a00b4e5" 1045;;
Hashtbl.add pfgsetmmprim "b4498dd7128bb3df47ab42a7a5e80876efe2c21ea67c5fa70bc5dbdb0630d1ec" 1046;;
Hashtbl.add pfgsetmmprim "26b3853a117e915a68988bdbb9bbad0ef14bb86415d5baf105c702207ed87cb2" 1047;;
Hashtbl.add pfgsetmmprim "0dcaaf67670005f74ed1c39a4e30f230924af73a13249cf0ece1172ea07cea61" 1048;;
Hashtbl.add pfgsetmmprim "08ceba8b8179bdf6fa46a7dcfc8244116acfba941451c3d33e025e4ea1ae6285" 1049;;
Hashtbl.add pfgsetmmprim "d710205a6cc499a12369c2abddaf70b6b9610658b512a24493b5f93fb71ba30b" 1050;;
Hashtbl.add pfgsetmmprim "754ea17d386e1c6a1f4923de2249dd7eaea4c99a312e8209de01009bcfbbf7ff" 1051;;
Hashtbl.add pfgsetmmprim "eaaf69fcdf704f2778396dae092784f4c7418549b98aeede7b1dc24c23366b19" 1052;;
Hashtbl.add pfgsetmmprim "8986214ea3b193b4979a8fa33c32527a47b777783aefde8923eeddd546f1dbe8" 1053;;
Hashtbl.add pfgsetmmprim "a306b3958b698782e88101304603feab08bc8fd51e0c0b3dd671abe57f99fcc0" 1054;;
Hashtbl.add pfgsetmmprim "ac7ae7cf03d89d8cc64d1ffea9d736f77d07ada018d88a942b9a85b91b8d494f" 1055;;
Hashtbl.add pfgsetmmprim "3e05c30b73a4967ab033027af64c86a81b47a1f9df057d2c0411dd7a23b11a16" 1056;;
Hashtbl.add pfgsetmmprim "4e9e338822da80af88628f8805b526f744a69ce0b09f39cc8e10ab75f04511ad" 1057;;
Hashtbl.add pfgsetmmprim "6732aa57ea5a65c2744f6c4d2b6079e7c1dc503e11c470fea88035eb2280dcea" 1058;;
Hashtbl.add pfgsetmmprim "d8e87f7a395c15291da141d7be81a35c021409f1c4f746facac884d74ac25056" 1059;;
Hashtbl.add pfgsetmmprim "41353ef5f8d82cbc57b4f10a087763a4b7e5b028a3c62c78d31b01effa91d923" 1060;;
Hashtbl.add pfgsetmmprim "2490bc26f0c99d7442d692a3d56964bdebaa743b75aa25af1adf80806fbb5792" 1061;;
Hashtbl.add pfgsetmmprim "7880823f56fbfc34a4ef7ebab0f6b77bc8731ccb124c5d2693b4f8afcec50c6e" 1062;;
Hashtbl.add pfgsetmmprim "28932a3b0423ac8118cf6db8a97241a87df92324aa987e60f811522064a4b4ec" 1063;;
Hashtbl.add pfgsetmmprim "d03c72b8c29f489413d770cb5cb0a970697bc0d46327ea448178b97d54d922ef" 1064;;
Hashtbl.add pfgsetmmprim "b59add6fce21f045681249af14bcb3a430b04d7843d1e0b0d09b4eb7ad830fe7" 1065;;
Hashtbl.add pfgsetmmprim "0dca8d0fe5f38e5a3e188090b6390df18d8ac8e6cac4b04c2593cb0112ab7ca5" 1066;;
Hashtbl.add pfgsetmmprim "e1c842f331b35becd8e9da601f2c95e48b3a2974e33c9d7c6960845964e9c448" 1067;;
Hashtbl.add pfgsetmmprim "3e938e79cbe2e1fbbe80adb13a379cf20b44098c390f7ac911e5515fcb2419e9" 1068;;
Hashtbl.add pfgsetmmprim "f6f1102cdd82ff4980dd75422c0d39414c0f6004782fc28f16cdee2912a1a5c6" 1069;;
Hashtbl.add pfgsetmmprim "df1a8bb468ffefecccc2015f99abe4bd8cdfc37d11af8ff5ba3f2567f42d8fd2" 1070;;
Hashtbl.add pfgsetmmprim "3521913a3d18bd095a170e63678a60623b389c2bee68f3e9740455ed492bb118" 1071;;
Hashtbl.add pfgsetmmprim "ecf50ac526dc20c9aa73060ec2e6e3b8c3acfc96808b687f76d39c5107505551" 1072;;
Hashtbl.add pfgsetmmprim "9ef2409e54b0cfdcdf567e8b62c22e67a4808746c011d24d09a630dfaa852c08" 1073;;
Hashtbl.add pfgsetmmprim "6077f14f56d03e9e9c9922db81a57672d637bbc7264d5eabfa9f21227f9f9c7c" 1074;;
Hashtbl.add pfgsetmmprim "c2eb973ba3e51f63b5a719ebf8c0f090903a88b4e02fcd9832d603716cbc5dfe" 1075;;
Hashtbl.add pfgsetmmprim "e513d7bb7a6c551361eb3a10dbf5d25bb17032a4b8b58e157910c5a6aaabe6b0" 1076;;
Hashtbl.add pfgsetmmprim "848d894ac7f349b0f6fb743d4a2fba55834cfbf378d6a278e0048f355ea892f2" 1077;;
Hashtbl.add pfgsetmmprim "ec15125c32ec917bec1efcec3dbcf6943efe7eb128a475654ddc0278254cbd49" 1078;;
Hashtbl.add pfgsetmmprim "b63e08c0fc2794625855d7c9422ead542270ed6fe8305d36b29176e871c7088e" 1079;;
Hashtbl.add pfgsetmmprim "3152fcaf65095273024657309cf281293956af64c026d6ac16b6eb9124151ea5" 1080;;
Hashtbl.add pfgsetmmprim "377508f8fe6b89bc19451186a4695e1db0c55a732bc03eb23e42f0ab6ee03898" 1081;;
Hashtbl.add pfgsetmmprim "2c97ef405d7d892084abb7df92cc806ae1683a463c139179d0e3af41525c5478" 1082;;
Hashtbl.add pfgsetmmprim "651a2fda2e40c396cf853ecd93e91030fe2609fe86f41b1a2c506601ebaf48c2" 1083;;
Hashtbl.add pfgsetmmprim "203b0736facacfe25afbbfc41ec00d1b0d882ffed1ce7ea1eed10ea913df6254" 1084;;
Hashtbl.add pfgsetmmprim "eb0e824d0d4aebbddfbb4125277e68a43b914f1a99c66b640a7f088fec9ad957" 1085;;
Hashtbl.add pfgsetmmprim "74f2a8a29d9ea0b6abdc54279f02a85b89858a49eeedc3ab4557bf547cf5a603" 1086;;
Hashtbl.add pfgsetmmprim "3f2148f24aa8308cb5b717ff9996a087b7e3fe6e5e0f370640f76c5f53d760e3" 1087;;
Hashtbl.add pfgsetmmprim "b7067e42c3c34c587456eb23eaae62d6f58d01304899c450834dad6775da2f7e" 1088;;
Hashtbl.add pfgsetmmprim "0ab74be3ea75df1486da3533410c3fe002276af5aeecd8391723bbbe66c9d27c" 1089;;
Hashtbl.add pfgsetmmprim "fa5255f6f58c427bcd66fd6c2cdce0406021a864ded233da612a2705eb86bc65" 1090;;
Hashtbl.add pfgsetmmprim "bb8d9b0af2aad762c09e60cf048abf2e5b69f7389d418e8e5cab233cc933f6bc" 1091;;
Hashtbl.add pfgsetmmprim "407226abea349e57da9c563c6b53abbc3ab4389296db4f351a5d1d9c1182f0d0" 1092;;
Hashtbl.add pfgsetmmprim "585f283e98b7dea2b917bc02082f7c444072ae1d080f6374e897bf7a60e822dd" 1093;;
Hashtbl.add pfgsetmmprim "36a3ef6669f93a84f229d801b2253a5bf72f8e52a7a96630a72e5359dcfa1f5f" 1094;;
Hashtbl.add pfgsetmmprim "9e67620f4c5ff5244585a2b2f6b230de05ce12eaeb338e730457f83d50334bfd" 1095;;
Hashtbl.add pfgsetmmprim "72e545d1ce21cf7837a84f889310d4fd620d9c6ee2554974101ca04a26d6ff8d" 1096;;
Hashtbl.add pfgsetmmprim "9631aafe3833afcc6968100c6c1a8383172d0d48e40e8a0a9c1aebe24158edae" 1097;;
Hashtbl.add pfgsetmmprim "f7b43a0174828593a9b787d036f6a806e9047556336b56a7dc0a360be1257fba" 1098;;
Hashtbl.add pfgsetmmprim "f0ef27e91b435961394e6803d6a4cfa9ce6ac5d694e99602997a7aac2f101b23" 1099;;
Hashtbl.add pfgsetmmprim "e34628d32b1beebc907d7b431c9982d46fcf5c6b9375e4da536ae18fc6c53868" 1100;;
Hashtbl.add pfgsetmmprim "b9c9693a091bac22defab892c3dea2636cf8a95e8d90ce570307fd07c2701847" 1101;;
Hashtbl.add pfgsetmmprim "75b8178a23b46f6313e7b2af3db9aee7ad2268b556555de1d0e74282f48ba240" 1102;;
Hashtbl.add pfgsetmmprim "279bf3de4f28eeb9c067cf6706fe3cb22283a07f855cefa2708f593a76aef979" 1103;;
Hashtbl.add pfgsetmmprim "e5c814305d2e0f570182502f851fbccb9d097aff050011ee96f6a4afaba41496" 1104;;
Hashtbl.add pfgsetmmprim "c69a802636652009601c42ff320b25982be902f5110f67ae87da622669370860" 1105;;
Hashtbl.add pfgsetmmprim "e9f0c285e3496a16563e0d3375363a6d468b5c9946c5d6d4f5728e545d1a070a" 1106;;
Hashtbl.add pfgsetmmprim "92882a6152aa0b367d00ee70567b181633b21d6baeb7566b94f555b9cee98edc" 1107;;
Hashtbl.add pfgsetmmprim "3058a34f31e95c44a623e8e6d00f78e16ec6e4ad9d5506c1ce0d7cbfdf49af29" 1108;;
Hashtbl.add pfgsetmmprim "2b0e419106d488651b297d3970f1bbcc53b3772b176913cf0d5b89b9e2b5c881" 1109;;
Hashtbl.add pfgsetmmprim "5a36cf77f12fb599cd8618914088bde50c89e1ba054811057e16b1d151fa9b54" 1110;;
Hashtbl.add pfgsetmmprim "7d63dc4692811e9aa61ee2f7769088fe2ed0d8b06661964507e68baa6a38a955" 1111;;
Hashtbl.add pfgsetmmprim "d62bc88871850452823bcddc2aca1eea358c7fa1e27db12e04a15c18cacef09b" 1112;;
Hashtbl.add pfgsetmmprim "534c08a67adfaf5d39cb2877822c308d30e4cd7a8e39466d14b03199fc15f5e1" 1113;;
Hashtbl.add pfgsetmmprim "a199d276843c46258f6a6a70986d17a0666c210b21f4a8d4a29c9f94927fd5ba" 1114;;
Hashtbl.add pfgsetmmprim "6c7b93775beb6582752c2968fad81982db79aa72e07864917192a639724fc37a" 1115;;
Hashtbl.add pfgsetmmprim "abfb9c098f25738b8b91286120fad771a0871c599cd4ce8972b43ba083017a03" 1116;;
Hashtbl.add pfgsetmmprim "78c0c8e8196afe71dbd6c5158666e56419723adbfc1d0a6c58011f159fc7cc1f" 1117;;
Hashtbl.add pfgsetmmprim "d553864f4669d2648a97c7cd2375d5a526715b105fe5338dd062462f47bbdd15" 1118;;
Hashtbl.add pfgsetmmprim "c4a304e6781e88e7f4ba1ebad49caecff79c8d6ec84752a4cffe152156ca7c73" 1119;;
Hashtbl.add pfgsetmmprim "448a8ab8ddfbfd6b04c413ff833842aa677babd704ca7a1316f94d27fbb4b96c" 1120;;
Hashtbl.add pfgsetmmprim "0708fcf6b9d8fe069f19f64ffc085da37d7d935dabaf52312bdc005a5bfd67de" 1121;;
Hashtbl.add pfgsetmmprim "a6824536b2b7d454f2f7fa0a7a3404cdcc5612b14fe374adb9fb2ec6243cfda8" 1122;;
Hashtbl.add pfgsetmmprim "fb3c2d2c345616ec0070775f0f7fc28575d1793a170df62ffa0623ef7ace3a29" 1123;;
Hashtbl.add pfgsetmmprim "ce457852d592dc1c4608089286b2802a35b4375d6ce18951736dce90c579789e" 1124;;
Hashtbl.add pfgsetmmprim "b085057c333a7f4ee4b064f3f645907973679d769b9905ab4e0ccaf56c263c38" 1125;;
Hashtbl.add pfgsetmmprim "ac1fbd6223a1e782d5e43aadfa1c5594be826ae39b00694ddddc836e32555d72" 1126;;
Hashtbl.add pfgsetmmprim "3f6253aae2362808eaac1f21b06b9edcf17f633be51f928f336f940ec399cdd2" 1127;;
Hashtbl.add pfgsetmmprim "427136bf06bfc430f7b29f13e9a2c2fdec0163f93966f220d815198f84d37cdc" 1128;;
Hashtbl.add pfgsetmmprim "c01da5d3e98bdd01a2d677dd005b789af3e8f28ad318de7e5512e09f2ea39a17" 1129;;
Hashtbl.add pfgsetmmprim "d63632624a4601c18d52503bbd223271ef5962b9dd1331002a54932ac1200621" 1130;;
Hashtbl.add pfgsetmmprim "a2c6e22e9cc2408a64b342a6f3716a3917686f82e083d5f4e7747a2bc62b3ff1" 1131;;
Hashtbl.add pfgsetmmprim "95f7f53ae5884caf4474556f03b93b7a730849394b37c3e41a9d41b5318eeb83" 1132;;
Hashtbl.add pfgsetmmprim "1d44a62dbea15a2ffcae386d647cd28882bdbd14998c3b16e72416241b8891d0" 1133;;
Hashtbl.add pfgsetmmprim "41a6ddc532ba256a91d1d077b9492b04e25fe3eacfa70d12f81cf3a37d601be2" 1134;;
Hashtbl.add pfgsetmmprim "535243f7a1b94616e8b09f54f63367cf1146d0ddfbcf3493c904497301022d2c" 1135;;
Hashtbl.add pfgsetmmprim "500281ed4d3544cf925bb37a025536aa64c78c3dee45f271ec784e149d05d1d7" 1136;;
Hashtbl.add pfgsetmmprim "88dc85b2f88e354f4f6967a4c3f316859eca9ccae1302b089b4546767478f63e" 1137;;
Hashtbl.add pfgsetmmprim "bd7781a81e98977722907adf027ab661b77467124e4bf65c594faf360467a5a2" 1138;;
Hashtbl.add pfgsetmmprim "8c178ee1f8b6b40bb15bab67f462e2aae3c926529ee9a4b7557ad5dd1c0a6bba" 1139;;
Hashtbl.add pfgsetmmprim "c0a948d85c116c4139c7c12ae560916cee8ce9956b1c5f0f0364fefc2c2b8632" 1140;;
Hashtbl.add pfgsetmmprim "ce8bf50aa24b784812f68c2df687e3211d85269e9192c512bb0c1d6392d42e70" 1141;;
Hashtbl.add pfgsetmmprim "03e88b0b9df1a6049e05c4c28ea83b06fb392276e850a2f2bad28613caec704c" 1142;;
Hashtbl.add pfgsetmmprim "6c287086003d1b2616ad9ed225d66e7bb3f3325c2dd98fc73fc61e607b137d77" 1143;;
Hashtbl.add pfgsetmmprim "52928d5e828dfff2a97f71eb7f3612de44dd130525b9b71a38023d7ac7b48398" 1144;;
Hashtbl.add pfgsetmmprim "91eed0de3e161fd11f07bca3b79bb06864e35ce5ebf071a41d4a72b9ca66db75" 1145;;
Hashtbl.add pfgsetmmprim "4e896c83f232bfc09e98b7429ca98aba6fb7058c6dc6086905292b0400c1f21e" 1146;;
Hashtbl.add pfgsetmmprim "c60e627fb085a77f4331e6304124f5b0c9b9dd53dcbec8cae4d325670fe9de86" 1147;;
Hashtbl.add pfgsetmmprim "2f5450de5d6481b853e81aeb801bfaaa59ffa7969273747ea86b5196c989334d" 1148;;
Hashtbl.add pfgsetmmprim "61294bf3274e78e33067a02550a2b09d5b16c0fcfeb69664f26938e991bed94a" 1149;;
Hashtbl.add pfgsetmmprim "81dbf26690faf6521030e92dd564566f59e14bb8a4ca2a81ad7a1d3c2f7318f6" 1150;;
Hashtbl.add pfgsetmmprim "a092dfc076badf0ea53ba557e91d8afbbf20918bec09cb9c36d97c9d6ae653d4" 1151;;
Hashtbl.add pfgsetmmprim "8036d8da758814a1e96790f6193908cc7584fe19171f937f50d43bb9331746e9" 1152;;
Hashtbl.add pfgsetmmprim "f589013abf6edb9401f9c1ead131dca031cae6d6370bf0f4f835e5cc010d8989" 1153;;
Hashtbl.add pfgsetmmprim "bdb0ddd2742b24fce4a1622dc7c7a75655ab001a8c287ceff20f4c09c649b8ef" 1154;;
Hashtbl.add pfgsetmmprim "29d206ecfb1da835eaa025e0fa654235a57a8cecd20e9eb352b5d24374c5f2c6" 1155;;
Hashtbl.add pfgsetmmprim "1424ef772925038b4343c0bdf7604f08a3ba040edb50ed6e6172cc6d1ba90ab4" 1156;;
Hashtbl.add pfgsetmmprim "e54b11ed8f2b2ba0f4245e368b7efe88df887e3443fe2e5c8075073ce6684627" 1157;;
Hashtbl.add pfgsetmmprim "07d99be6a349e916a44998e2f38ef4e45d5ea962b34da0fadf8ab172222b1eec" 1158;;
Hashtbl.add pfgsetmmprim "0c9c3c805f7b3c8f425e03bb4753838ff83026e89406d21e69ad0d9112fee0c3" 1159;;
Hashtbl.add pfgsetmmprim "b003542b75d56a87351faf662ab1ae7ce7a90ac20e44a9a536817fc1dfd8993c" 1160;;
Hashtbl.add pfgsetmmprim "2564f896a7a9b21b5078a2199754c2c054a2419c46013316e4af02aa2e303c0e" 1161;;
Hashtbl.add pfgsetmmprim "61ad73dd9b29b28c9c5f0e6791002214e89789472a662f531ca5176553f371b9" 1162;;
Hashtbl.add pfgsetmmprim "ec42f383ac182d0bc49c4ac16c10c069f2d0039bba437eeb61a02199d2184d70" 1163;;
Hashtbl.add pfgsetmmprim "a7cb32722cb523e383a73ab9b778c81ca444a200d6afc2ed0c6db70a3a04cd66" 1164;;
Hashtbl.add pfgsetmmprim "d16fdcd349b777145678c085a645ce12af27da4d4f6cd42832937b092bec0017" 1165;;
Hashtbl.add pfgsetmmprim "04f430da329c7d0bf269fd56a73a11f970cea7eae5180b15cfb47b942a9ede67" 1166;;
Hashtbl.add pfgsetmmprim "c31eb823fe771de063f84de71e3007563002d311c75110986103680b3f1a596f" 1167;;
Hashtbl.add pfgsetmmprim "dd8f032f2ef172ea325d22043b138d6db03df3e24c80488ba0a0edff9ca3fb14" 1168;;
Hashtbl.add pfgsetmmprim "3b10f688f6218f0d971db215bf7d995eb7278af7dfdab9a408c64e17572cf31d" 1169;;
Hashtbl.add pfgsetmmprim "9560cd6dd9ad8f5490fe417bc8608d283e201655055db8299bbf998b106d36e2" 1170;;
Hashtbl.add pfgsetmmprim "b84d10a8d369cb29e2082b847019bd77ae9c33e3e6ed6e1df52717aaf630365e" 1171;;
Hashtbl.add pfgsetmmprim "c136cde3c162ac1ad927d498de1d6d326d34ce6523acc4559fe119f979eaf436" 1172;;
Hashtbl.add pfgsetmmprim "37008fa8868d8c167e319722b79f7aa156ffaae468d78821f6357a5ee08a4533" 1173;;
Hashtbl.add pfgsetmmprim "bea070a21b4507f8d549c667acc83fb0a02630ffc069aaa66b26f13cea2395da" 1174;;
Hashtbl.add pfgsetmmprim "3e156e41cfd7df8e353e71c7e436d7087ab40a5a35dc734b79ec9a7a80931d2c" 1175;;
Hashtbl.add pfgsetmmprim "481acf4c7af1cbcc78d665fd8fa15efc549e8c7d2a900d070b635cf6848c52da" 1176;;
Hashtbl.add pfgsetmmprim "a3ba49c1f4b914eda6b3625fd4f71d4b980c6417e12086137b51572e3a21cfe3" 1177;;
Hashtbl.add pfgsetmmprim "d4c99a1abd1d514e42c64b6ef13209e51c11513a1533da6d5bf9084286bb41ef" 1178;;
Hashtbl.add pfgsetmmprim "7bee4155fa1b7c2b325bc653072bf104657234e96b8cab011de90d4eca56d5b9" 1179;;
Hashtbl.add pfgsetmmprim "d12f25c3e2ac5a19187dd340d1c32b7e6a599a4a9e998d64c70898080adb97a6" 1180;;
Hashtbl.add pfgsetmmprim "0f7517ccc4f29ac88a3717e05a2119895239434810e9972ac17c60254bde401d" 1181;;
Hashtbl.add pfgsetmmprim "ee1bfce1396f60fe0a944d0876eb870c7dd63231b46ec99c72fcb739fc4b6ca1" 1182;;
Hashtbl.add pfgsetmmprim "0888ffeaec7f5fc1511cbf2dbb9d6c56b2b0744cc9a2f5415cdd9a7403439a40" 1183;;
Hashtbl.add pfgsetmmprim "c401140c81477bcd1d3f819d3adde12af7d930ca79139e61b331b74036f93217" 1184;;
Hashtbl.add pfgsetmmprim "627d2ee3baa48d5cf57fd73d780e94a24714d7994d552039f3152bb7adb94a83" 1185;;
Hashtbl.add pfgsetmmprim "e93f202f365f20d9d53132e002922a522281f1ed15d70ccd6b47b9797b66e058" 1186;;
Hashtbl.add pfgsetmmprim "29fcbe3a8b061f7c1da82eb1698168ee0a82693f93460335dfef8a327fd5a673" 1187;;
Hashtbl.add pfgsetmmprim "ef1ba51716db51cd8c39df02558070bba5db630a71ffb1b952c532fa408ec6d5" 1188;;
Hashtbl.add pfgsetmmprim "7cd86da22adee3f4122ceb5c952e561f3a0987e730686de977fd4359d668523b" 1189;;
Hashtbl.add pfgsetmmprim "17538b29e19b8f08c464e5e509291a3ba4d8d86168988cd578ed172a58ec6753" 1190;;
Hashtbl.add pfgsetmmprim "599c1d2a2c9eaa18807778038590146459fc12e7fa9cdf05c66c2bbb57c11e4d" 1191;;
Hashtbl.add pfgsetmmprim "9cad0071825e8d6503d1b2cd7a59a5021e30947cbd28e27ca4a0060224973703" 1192;;
Hashtbl.add pfgsetmmprim "5dc1c2e7456fe0cd4a3853a95b421faea81b45ba78357088d6c9625bf0fd716e" 1193;;
Hashtbl.add pfgsetmmprim "25bc05450c836741740782ba599230640a37d508e4ee00d5db54335f1c5e0277" 1194;;
Hashtbl.add pfgsetmmprim "a2fb83789b9bb8ce9588944dabc2acdda24ab3d817079df51019dd8bd3c5cade" 1195;;
Hashtbl.add pfgsetmmprim "f98e9d2f2f18107b0433d84f0cffb48a819dec730257c68ec37ecaf23064ce39" 1196;;
Hashtbl.add pfgsetmmprim "28cc1863d6f7aa1aef205d18f8d1978004c081111a14ec69442234e9b1e08b42" 1197;;
Hashtbl.add pfgsetmmprim "0fed9cbde4196fb26c0658472c1d4e38c05479552b1a5da74c7d3d5a304f7061" 1198;;
Hashtbl.add pfgsetmmprim "d431a619d73900e88edb636963a19d52e5f28c3add811c60cfb870542e609e1f" 1199;;
Hashtbl.add pfgsetmmprim "d4644b9769d4141474c6a04cdeac0ad88b7b304dd059df23b7fe0e7232cde1f7" 1200;;
Hashtbl.add pfgsetmmprim "bb7178caf95f9e4ab0aaa0f9cb507e6b0ec19111f164d15e7da398a1eaad45fa" 1201;;
Hashtbl.add pfgsetmmprim "df8e7e660d054b7c1269e7c438bc9418f330361e762534685c1e9c59b4ab7a2b" 1202;;
Hashtbl.add pfgsetmmprim "3e04d58fbf849d15635f865eac3cfdaf73f173491c2c3d36b4927b9e9ffbb678" 1203;;
Hashtbl.add pfgsetmmprim "697fc36e179623a1e86a9b484132b39c658a0bc3a408314cebf98118993c292a" 1204;;
Hashtbl.add pfgsetmmprim "e01442517a72150913206ac0aed7660c17c048ab1e4a99685947af24f4221465" 1205;;
Hashtbl.add pfgsetmmprim "17a7f2d9aa08a9bcc839cb34002c7b98b63a40e6603000b09373585e1db054a5" 1206;;
Hashtbl.add pfgsetmmprim "e1583fa759ef358b1f09e819fc1125e3f1161a2e381d422e014be719ed9b033c" 1207;;
Hashtbl.add pfgsetmmprim "2f7fcc5d82297c67fdf39e6fbfc2c0afa3e95e2c6ad075c0f5edb37ac38d0112" 1208;;
Hashtbl.add pfgsetmmprim "a62e9714908ba4c2621f3128fd7a1c97fbb5e1f87d269fd353adbdc6c51c4100" 1209;;
Hashtbl.add pfgsetmmprim "63dbef6e8461bb2b8d4cf84a6670ad5951eaa651a8d8afd92fd9a899c449b63a" 1210;;
Hashtbl.add pfgsetmmprim "c5ae26d742924b8b0fc1d12d2827dddbbbc46df8d96e5c24cbbf203193f5da4d" 1211;;
Hashtbl.add pfgsetmmprim "a116c24312a2b6a51c2f6a51fcba150171370d562596bc3dbcb3d95b77aa2cff" 1212;;
Hashtbl.add pfgsetmmprim "28d122d855b752f3ae8c084845b1371d44575a0163951a5f3622d6aeb85da887" 1213;;
Hashtbl.add pfgsetmmprim "64f195d21b23626e04e9d9675d7ffa79dc6d6be9e2edf2256dc2751cb52b939b" 1214;;
Hashtbl.add pfgsetmmprim "737ab6e606d4a61061c45ea796956d0b20ed4e6e284ef5a846d014206f915f4c" 1215;;
Hashtbl.add pfgsetmmprim "bc2ad1e217f1808406450d942c31c34054588798e991139b2c6560a1ea424bf3" 1216;;
Hashtbl.add pfgsetmmprim "d9e9d2c2c9732c77426fc8a2dabb1a9cf8f459ddcba42b578aee3b9436538bd7" 1217;;
Hashtbl.add pfgsetmmprim "af19b6b8fb65efcb35aecc4a51f63d2115854a8e5cc16b6b56a50ed3cc7c5001" 1218;;
Hashtbl.add pfgsetmmprim "c5eb4feccd9f6cb30915fa08d337a70b11f410bc7fc8ad160a15015b241820ce" 1219;;
Hashtbl.add pfgsetmmprim "6d7de3c91aa5ea5174c9b23fef2e9b32e51e6b662acecbffc3900a1177901563" 1220;;
Hashtbl.add pfgsetmmprim "78bba32cff191d65d2233e8f3ce2473f47559b62463dee7268c4dfef8a0c90ef" 1221;;
Hashtbl.add pfgsetmmprim "a32509dd8baf3472fc7b37e607c35628ca0194ee0eff53eb4a3c26afa5ad69fc" 1222;;
Hashtbl.add pfgsetmmprim "fe250e8072976d1da7d3104226a37788adf53d7d0d86faf36a03137cf88fc738" 1223;;
Hashtbl.add pfgsetmmprim "f62dfe4c0e0ee1c11f460f33059d31d8c15af089ef3880adcc1f0fc4dcfc68f0" 1224;;
Hashtbl.add pfgsetmmprim "423fe57817d37e9fa2a85397f8238eb8d816afa8284f6b7c310c81db2ec6cfc3" 1225;;
Hashtbl.add pfgsetmmprim "189450c3141670582527a1991839b28700880de4641b18ba646366d57b5b299a" 1226;;
Hashtbl.add pfgsetmmprim "6b8b2f36d52c30be2ffa0b5d1773d160069448609937d63cfe9d54060e0bfb75" 1227;;
Hashtbl.add pfgsetmmprim "2ef103e6e8115631b05cf18cd88c32f86af1eade5a1621a30b5a4c2e3052918a" 1228;;
Hashtbl.add pfgsetmmprim "6bc40e42c7fe63e3a8edd85115d81251736059b1584781578d32a493d261259b" 1229;;
Hashtbl.add pfgsetmmprim "28e3f0f4b9893cb8616d7f35ba58ee3c69f3bdfaded6ca159222f509175591e7" 1230;;
Hashtbl.add pfgsetmmprim "4d6f8fe038667fcd1b631cb21466f7e89f0e77479c0be4683b292ec9440eeeee" 1231;;
Hashtbl.add pfgsetmmprim "238844451541d0deac99c8c96578596862a12fb536fc94f163625c277ceece6f" 1232;;
Hashtbl.add pfgsetmmprim "4ae2fb7608911c994ff73609baac25a8360142aad4adc12d19e2654d5c1033c9" 1233;;
Hashtbl.add pfgsetmmprim "f55451b8b74a90c678ad748bbbfd067a88220cc1f64ce429b2e18a264fbeb38d" 1234;;
Hashtbl.add pfgsetmmprim "08d8bd75545be9ea5ff124c0f81d3bc4468cbab1b9f99c12563d17e8b350d620" 1235;;
Hashtbl.add pfgsetmmprim "92cc887246927bf4aa2fd1af84679ebbe3a937ed3287c30584d212feb2fc09c8" 1236;;
Hashtbl.add pfgsetmmprim "62bbdd4f75d2e8e21a55c716d25f1abe0c63f54bcb453b6a83bbc60c4e6f4787" 1237;;
Hashtbl.add pfgsetmmprim "4caec663e087b86fef815fa3f5a3d954d7be7e6349c99382871f76888a0f7a76" 1238;;
Hashtbl.add pfgsetmmprim "a7d103f6e78645169940f5f6cefe60258e5277988faa1130788fbe3afc23ea60" 1239;;
Hashtbl.add pfgsetmmprim "88ada1ea890cf4889a050d2e3aa4dc784d8147b8dfac7237fa32efe8520d604d" 1240;;
Hashtbl.add pfgsetmmprim "755060377a1e73b3ba9d15e1eb3f1ee80d88e14b501d8207f800bb96cee571e0" 1241;;
Hashtbl.add pfgsetmmprim "e045b9ab080dc7e91c6e97886074b08389379984b009d0f8d098ab1f4c6c66b9" 1242;;
Hashtbl.add pfgsetmmprim "aea1770dbc1d33b60ee88acbeb4efe5d934319d9600fe268f051d616b4b0cbec" 1243;;
Hashtbl.add pfgsetmmprim "fa1b15478933bbf12f730e0a6ecddc47444fdd97be2b82c18903b9c2099c04e2" 1244;;
Hashtbl.add pfgsetmmprim "0e765b499de439a6d9a451eeec4c734841fb71e014c03cd732229696847421b5" 1245;;
Hashtbl.add pfgsetmmprim "69e2edffa16ff8f622dfceef225c08262778402cf2a40f979064f311fa2ff57f" 1246;;
Hashtbl.add pfgsetmmprim "542dab00799028278b9e3dd7893abc5c05ba6872e354d78d0f5a26dc8e19725e" 1247;;
Hashtbl.add pfgsetmmprim "a9663ef91a5047e8a1d0b69c47e228031a31853ea1dfd65c519457174abc11a4" 1248;;
Hashtbl.add pfgsetmmprim "d9dbcc896d4509e929aa1e65e8fca93d4562361d3a5aa762f474ff8f2c26f5c2" 1249;;
Hashtbl.add pfgsetmmprim "a7da4c065544a24a121f54388efe6de8a23d219977d4a6e3bab02d38f511623e" 1250;;
Hashtbl.add pfgsetmmprim "be0ac8c8ef9754513812394dc7ff143d712fe96f9280f37d5b2456cbd0a7de0e" 1251;;
Hashtbl.add pfgsetmmprim "32afc5c286e5f14c4e777a1ba639ecf9079aad3e283fec425a49671b72ecdaf3" 1252;;
Hashtbl.add pfgsetmmprim "bbdf92381a38262b4b84835d0b3d31e9a0a912e78288051e4133b40675939c40" 1253;;
Hashtbl.add pfgsetmmprim "f171bea03e9060eda03f423586e50fdb3550376b614a3d9c046bdda791b6341d" 1254;;
Hashtbl.add pfgsetmmprim "e67896267ec00b7ae5797cf69b27b9be8b61a3ef0615c1be6cf5c4e06eb54464" 1255;;
Hashtbl.add pfgsetmmprim "da55eaca0262b84df09b130309cdff850a53ef2dadb97f079d7943a40149d4a7" 1256;;
Hashtbl.add pfgsetmmprim "3b9535d7772b4f773ec23e28147fb4c37b6ca8ffb8e8bde0fe3a11f11d657573" 1257;;
Hashtbl.add pfgsetmmprim "1e331a6c1c1d9b0fdd06e96514d4b0e73c7b6f91f8dfbea438938d74fc979419" 1258;;
Hashtbl.add pfgsetmmprim "641dbb6593cee664b873c2fe5209bae636194327afa5da0c4eb3e92eb7970fc0" 1259;;
Hashtbl.add pfgsetmmprim "f3e76d0af4242ba88a2de549d5f4454e60b77589c43cc225fe41aba07585c17b" 1260;;
Hashtbl.add pfgsetmmprim "1581dd64b7a17b2292f31c0620b73abc6d337d0ff0ad8dffab0af0126660837e" 1261;;
Hashtbl.add pfgsetmmprim "1bf78382695a339fb54ce20f252bbb65ae30369bf73607aa65343b03347c3d26" 1262;;
Hashtbl.add pfgsetmmprim "fc1df1d0d9d6f49781d7e8f0fc8121368e3f18f92e70bc278ac9e2c52c6cb1c3" 1263;;
Hashtbl.add pfgsetmmprim "941902c4eb234d520bcf72250c9d1c1a1649221251a9d2497fd088a72decab72" 1264;;
Hashtbl.add pfgsetmmprim "daf24d80c22e9d138062a8dc202c4dff69482c70ec99a2a14b1d7afaa7b39536" 1265;;
Hashtbl.add pfgsetmmprim "8305c75be6a4d0a7a359669a8d7fac74185f32aa5307a9830a96ba1b58cbf0c3" 1266;;
Hashtbl.add pfgsetmmprim "c1ad58df4ce74d954a05cd0fac32c0e5fd12d3be4ed3aa7d1bd65c96fdb8c9e8" 1267;;
Hashtbl.add pfgsetmmprim "7f54530a81467c4fea8bfd5a3cbce55de0bab2775e56e5a2d3878ac9b74912f9" 1268;;
Hashtbl.add pfgsetmmprim "60619182011ab650a10b651fd0a6953d015d2da07fa27bbcd790b518e4604be8" 1269;;
Hashtbl.add pfgsetmmprim "1812fc612a34dd6e44c40f1cef7ca5ae65f823610bb1862b0cdb5c8e601cec84" 1270;;
Hashtbl.add pfgsetmmprim "67ac9efa46a82952b0fd67e2e8226e1863ae06b17feb52e7e63491189c709df3" 1271;;
Hashtbl.add pfgsetmmprim "be6b7b037d90698a9fe2be211fc12c6f78e1d40a39193d9970c3d760ea214883" 1272;;
Hashtbl.add pfgsetmmprim "aba06c9e3b0b97bb900c4d675ea7d0fa8a0a7359d72dfed7e8857e4d045226a0" 1273;;
Hashtbl.add pfgsetmmprim "c8291912df9ba33a32c2775fe68a6b7cdcd370e5398bb65f99599900922a060c" 1274;;
Hashtbl.add pfgsetmmprim "844c01584984a937d66301a8edb167617bc7c90103ef747ba0f74dfab1327733" 1275;;
Hashtbl.add pfgsetmmprim "2db32c0ae1696a57800091faa6c53bb58fad74ad77af84395d3e6b572a9a8e4d" 1276;;
Hashtbl.add pfgsetmmprim "2b1ffe68f2b1b72db3fe32071ab07e188c4d0c685fb0c70ab28edff3ab9b76cc" 1277;;
Hashtbl.add pfgsetmmprim "96f337c9a57f04a21970d2764ac0133f9de81729625d7997d18450583267aae2" 1278;;
Hashtbl.add pfgsetmmprim "9875422888572ab4d69fc57b9f086d3b8466a18c5501b056b1c7890023eaa4f5" 1279;;
Hashtbl.add pfgsetmmprim "976b82704553f9c0b7a8a231c0fbd7057663c6875b8e7d61a744a657bbba4b47" 1280;;
Hashtbl.add pfgsetmmprim "d4cd907c23d063aa9f5d9fb602afa5d4195a8b3b709138566d386b63aba2db21" 1281;;
Hashtbl.add pfgsetmmprim "8fef2a506c0cf893f4d20207d0bcea290ebac4b9fb34971c46c92b81b3ab570a" 1282;;
Hashtbl.add pfgsetmmprim "99084bb79a01bbf16f40fe149b76f489a935657335ff4e72908fe66d5cd49cb4" 1283;;
Hashtbl.add pfgsetmmprim "03c3f40a7e6f3f3ef1292097cf9347349984d0b4bccf79c48dd35712e3aaab0c" 1284;;
Hashtbl.add pfgsetmmprim "03bf63f2cf361db05bb72352dea4420c90f10ec8f7d65605499d2f2f0502bf68" 1285;;
Hashtbl.add pfgsetmmprim "4e141c484f506833f6dd50063de405c92c409b59e9f1062e726c606514986e9a" 1286;;
Hashtbl.add pfgsetmmprim "5c0e4de29e40e5acd223161f8558f628d16765f5bfd53e50b29b2fa58e3c7c1e" 1287;;
Hashtbl.add pfgsetmmprim "ec3d35d4b50f5a815ed35619879eb343a6bb75c62f261e7ed4a4f90db91dd1c0" 1288;;
Hashtbl.add pfgsetmmprim "3245825fbe1caebc61b19ef2c44fb32379984e1bd5a6c11b7e6bd3d9a9aa68ba" 1289;;
Hashtbl.add pfgsetmmprim "f0c0fd49f347366ba1b62475fb9287bd47e737bf1826a723fb41113daa6e8909" 1290;;

(** HOAS theory **)
let pfghoasprim : (string,int) Hashtbl.t = Hashtbl.create 100;;
let pfghoasknname : (string,string) Hashtbl.t = Hashtbl.create 100;;

Hashtbl.add pfghoasprim "d58762d200971dcc7f1850726d9f2328403127deeba124fc3ba2d2d9f7c3cb8c" 0;;
Hashtbl.add pfghoasprim "73c9efe869770ab42f7cde0b33fe26bbc3e2bd157dad141c0c27d1e7348d60f5" 1;;

Hashtbl.add pfghoasknname "d4decebfc69ca1960129ec4e292e1ccb592c50bca5d450a12c0bba887817b174" "pair_inj";;
Hashtbl.add pfghoasknname "76b2a66bedf76e57ff081dcbd56ad689d603f4eff70621cd55343f7c04d909fe" "bind_inj";;
Hashtbl.add pfghoasknname "315a2984b1ac53cb8ff29dfca7ce2575250602b580ff9a68928b107ee1db6d02" "pair_not_bind";;
Hashtbl.add pfghoasknname "539481cbfe76d6724bab04370be9feb170330706d71fd7faed0680556c1bd902" "prop_ext";;
            
let currtmid : string ref = ref ""
let thmcount : int ref = ref 0
let pflinestart : int ref = ref 0
let pfcharstart : int ref = ref 0
let pftext : Buffer.t = Buffer.create 10000

type tp = TpVar of int | Prop | Set | Ar of tp * tp

let rec notpvarsp a =
  match a with
  | TpVar _ -> false
  | Ar(a1,a2) -> notpvarsp a1 && notpvarsp a2
  | _ -> true

(*** assume number of type variables is between 0 and 3 ***)
type ptp = int * tp

let primname x =
  if !pfgtheory = SetMM then
    begin
      match x with
      | "wn" -> (0,(0,Ar(Prop,Prop)))
      | "wb" -> (1,(0,Ar(Prop,Ar(Prop,Prop))))
      | "wo" -> (2,(0,Ar(Prop,Ar(Prop,Prop))))
      | "wa" -> (3,(0,Ar(Prop,Ar(Prop,Prop))))
      | "wif" -> (4,(0,Ar(Prop,Ar(Prop,Ar(Prop,Prop)))))
      | "w3o" -> (5,(0,Ar(Prop,Ar(Prop,Ar(Prop,Prop)))))
      | "w3a" -> (6,(0,Ar(Prop,Ar(Prop,Ar(Prop,Prop)))))
      | "wnan" -> (7,(0,Ar(Prop,Ar(Prop,Prop))))
      | "wxo" -> (8,(0,Ar(Prop,Ar(Prop,Prop))))
      | "cv" -> (9,(0,Ar(Set,Ar(Set,Prop))))
      | "wceq" -> (10,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Prop))))
      | "wtru" -> (11,(0,Prop))
      | "wfal" -> (12,(0,Prop))
      | "whad" -> (13,(0,Ar(Prop,Ar(Prop,Ar(Prop,Prop)))))
      | "wcad" -> (14,(0,Ar(Prop,Ar(Prop,Ar(Prop,Prop)))))
      | "wex" -> (15,(0,Ar(Ar(Set,Prop),Prop)))
      | "wnf" -> (16,(0,Ar(Ar(Set,Prop),Prop)))
      | "wnfOLD" -> (17,(0,Ar(Ar(Set,Prop),Prop)))
      | "wsb" -> (18,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "wcel" -> (19,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Prop))))
      | "weu" -> (20,(0,Ar(Ar(Set,Prop),Prop)))
      | "wmo" -> (21,(0,Ar(Ar(Set,Prop),Prop)))
      | "cab" -> (22,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "wnfc" -> (23,(0,Ar(Ar(Set,Ar(Set,Prop)),Prop)))
      | "wne" -> (24,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Prop))))
      | "wnel" -> (25,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Prop))))
      | "wral" -> (26,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Ar(Set,Prop)),Prop))))
      | "wrex" -> (27,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Ar(Set,Prop)),Prop))))
      | "wreu" -> (28,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Ar(Set,Prop)),Prop))))
      | "wrmo" -> (29,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Ar(Set,Prop)),Prop))))
      | "crab" -> (30,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Ar(Set,Prop)),Ar(Set,Prop)))))
      | "cvv" -> (31,(0,Ar(Set,Prop)))
      | "wcdeq" -> (32,(0,Ar(Prop,Ar(Set,Ar(Set,Prop)))))
      | "wsbc" -> (33,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Prop))))
      | "csb" -> (34,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Ar(Set,Prop)),Ar(Set,Prop)))))
      | "cdif" -> (35,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "cun" -> (36,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "cin" -> (37,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "wss" -> (38,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Prop))))
      | "wpss" -> (39,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Prop))))
      | "csymdif" -> (40,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "c0" -> (41,(0,Ar(Set,Prop)))
      | "cif" -> (42,(0,Ar(Prop,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop))))))
      | "cpw" -> (43,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "csn" -> (44,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "cpr" -> (45,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "ctp" -> (46,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop))))))
      | "cop" -> (47,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "cotp" -> (48,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop))))))
      | "cuni" -> (49,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "cint" -> (50,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "ciun" -> (51,(0,Ar(Ar(Set,Ar(Set,Prop)),Ar(Ar(Set,Ar(Set,Prop)),Ar(Set,Prop)))))
      | "ciin" -> (52,(0,Ar(Ar(Set,Ar(Set,Prop)),Ar(Ar(Set,Ar(Set,Prop)),Ar(Set,Prop)))))
      | "wdisj" -> (53,(0,Ar(Ar(Set,Ar(Set,Prop)),Ar(Ar(Set,Ar(Set,Prop)),Prop))))
      | "wbr" -> (54,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Prop)))))
      | "copab" -> (55,(0,Ar(Ar(Set,Ar(Set,Prop)),Ar(Set,Prop))))
      | "copab_b" -> (56,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "cmpt" -> (57,(0,Ar(Ar(Set,Ar(Set,Prop)),Ar(Ar(Set,Ar(Set,Prop)),Ar(Set,Prop)))))
      | "wtr" -> (58,(0,Ar(Ar(Set,Prop),Prop)))
      | "cid" -> (59,(0,Ar(Set,Prop)))
      | "cep" -> (60,(0,Ar(Set,Prop)))
      | "wpo" -> (61,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Prop))))
      | "wor" -> (62,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Prop))))
      | "wfr" -> (63,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Prop))))
      | "wse" -> (64,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Prop))))
      | "wwe" -> (65,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Prop))))
      | "cxp" -> (66,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "ccnv" -> (67,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "cdm" -> (68,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "crn" -> (69,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "cres" -> (70,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "cima" -> (71,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "ccom" -> (72,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "wrel" -> (73,(0,Ar(Ar(Set,Prop),Prop)))
      | "cpred" -> (74,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop))))))
      | "word" -> (75,(0,Ar(Ar(Set,Prop),Prop)))
      | "con0" -> (76,(0,Ar(Set,Prop)))
      | "wlim" -> (77,(0,Ar(Ar(Set,Prop),Prop)))
      | "csuc" -> (78,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "cio" -> (79,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "wfun" -> (80,(0,Ar(Ar(Set,Prop),Prop)))
      | "wfn" -> (81,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Prop))))
      | "wf" -> (82,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Prop)))))
      | "wf1" -> (83,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Prop)))))
      | "wfo" -> (84,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Prop)))))
      | "wf1o" -> (85,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Prop)))))
      | "cfv" -> (86,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "wiso" -> (87,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Prop)))))))
      | "crio" -> (88,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Ar(Set,Prop)),Ar(Set,Prop)))))
      | "co" -> (89,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop))))))
      | "coprab" -> (90,(0,Ar(Ar(Set,Ar(Set,Ar(Set,Prop))),Ar(Set,Prop))))
      | "cmpt2" -> (91,(0,Ar(Ar(Set,Ar(Set,Ar(Set,Prop))),Ar(Ar(Set,Ar(Set,Ar(Set,Prop))),Ar(Ar(Set,Ar(Set,Ar(Set,Prop))),Ar(Set,Prop))))))
      | "cof" -> (92,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "cofr" -> (93,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "crpss" -> (94,(0,Ar(Set,Prop)))
      | "com" -> (95,(0,Ar(Set,Prop)))
      | "c1st" -> (96,(0,Ar(Set,Prop)))
      | "c2nd" -> (97,(0,Ar(Set,Prop)))
      | "csupp" -> (98,(0,Ar(Set,Prop)))
      | "ctpos" -> (99,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "ccur" -> (100,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "cunc" -> (101,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "cund" -> (102,(0,Ar(Set,Prop)))
      | "cwrecs" -> (103,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop))))))
      | "wsmo" -> (104,(0,Ar(Ar(Set,Prop),Prop)))
      | "crecs" -> (105,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "crdg" -> (106,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "cseqom" -> (107,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "c1o" -> (108,(0,Ar(Set,Prop)))
      | "c2o" -> (109,(0,Ar(Set,Prop)))
      | "c3o" -> (110,(0,Ar(Set,Prop)))
      | "c4o" -> (111,(0,Ar(Set,Prop)))
      | "coa" -> (112,(0,Ar(Set,Prop)))
      | "comu" -> (113,(0,Ar(Set,Prop)))
      | "coe" -> (114,(0,Ar(Set,Prop)))
      | "wer" -> (115,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Prop))))
      | "cec" -> (116,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "cqs" -> (117,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "cmap" -> (118,(0,Ar(Set,Prop)))
      | "cpm" -> (119,(0,Ar(Set,Prop)))
      | "cixp" -> (120,(0,Ar(Ar(Set,Ar(Set,Prop)),Ar(Ar(Set,Ar(Set,Prop)),Ar(Set,Prop)))))
      | "cen" -> (121,(0,Ar(Set,Prop)))
      | "cdom" -> (122,(0,Ar(Set,Prop)))
      | "csdm" -> (123,(0,Ar(Set,Prop)))
      | "cfn" -> (124,(0,Ar(Set,Prop)))
      | "cfsupp" -> (125,(0,Ar(Set,Prop)))
      | "cfi" -> (126,(0,Ar(Set,Prop)))
      | "csup" -> (127,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop))))))
      | "cinf" -> (128,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop))))))
      | "coi" -> (129,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "char" -> (130,(0,Ar(Set,Prop)))
      | "cwdom" -> (131,(0,Ar(Set,Prop)))
      | "ccnf" -> (132,(0,Ar(Set,Prop)))
      | "ctc" -> (133,(0,Ar(Set,Prop)))
      | "cr1" -> (134,(0,Ar(Set,Prop)))
      | "crnk" -> (135,(0,Ar(Set,Prop)))
      | "ccrd" -> (136,(0,Ar(Set,Prop)))
      | "cale" -> (137,(0,Ar(Set,Prop)))
      | "ccf" -> (138,(0,Ar(Set,Prop)))
      | "wacn" -> (139,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "wac" -> (140,(0,Prop))
      | "ccda" -> (141,(0,Ar(Set,Prop)))
      | "cfin1a" -> (142,(0,Ar(Set,Prop)))
      | "cfin2" -> (143,(0,Ar(Set,Prop)))
      | "cfin4" -> (144,(0,Ar(Set,Prop)))
      | "cfin3" -> (145,(0,Ar(Set,Prop)))
      | "cfin5" -> (146,(0,Ar(Set,Prop)))
      | "cfin6" -> (147,(0,Ar(Set,Prop)))
      | "cfin7" -> (148,(0,Ar(Set,Prop)))
      | "cgch" -> (149,(0,Ar(Set,Prop)))
      | "cwina" -> (150,(0,Ar(Set,Prop)))
      | "cina" -> (151,(0,Ar(Set,Prop)))
      | "cwun" -> (152,(0,Ar(Set,Prop)))
      | "cwunm" -> (153,(0,Ar(Set,Prop)))
      | "ctsk" -> (154,(0,Ar(Set,Prop)))
      | "cgru" -> (155,(0,Ar(Set,Prop)))
      | "ctskm" -> (156,(0,Ar(Set,Prop)))
      | "cnpi" -> (157,(0,Ar(Set,Prop)))
      | "cpli" -> (158,(0,Ar(Set,Prop)))
      | "cmi" -> (159,(0,Ar(Set,Prop)))
      | "clti" -> (160,(0,Ar(Set,Prop)))
      | "cplpq" -> (161,(0,Ar(Set,Prop)))
      | "cmpq" -> (162,(0,Ar(Set,Prop)))
      | "cltpq" -> (163,(0,Ar(Set,Prop)))
      | "ceq" -> (164,(0,Ar(Set,Prop)))
      | "cnq" -> (165,(0,Ar(Set,Prop)))
      | "c1q" -> (166,(0,Ar(Set,Prop)))
      | "cerq" -> (167,(0,Ar(Set,Prop)))
      | "cplq" -> (168,(0,Ar(Set,Prop)))
      | "cmq" -> (169,(0,Ar(Set,Prop)))
      | "crq" -> (170,(0,Ar(Set,Prop)))
      | "cltq" -> (171,(0,Ar(Set,Prop)))
      | "cnp" -> (172,(0,Ar(Set,Prop)))
      | "c1p" -> (173,(0,Ar(Set,Prop)))
      | "cpp" -> (174,(0,Ar(Set,Prop)))
      | "cmp" -> (175,(0,Ar(Set,Prop)))
      | "cltp" -> (176,(0,Ar(Set,Prop)))
      | "cer" -> (177,(0,Ar(Set,Prop)))
      | "cnr" -> (178,(0,Ar(Set,Prop)))
      | "c0r" -> (179,(0,Ar(Set,Prop)))
      | "c1r" -> (180,(0,Ar(Set,Prop)))
      | "cm1r" -> (181,(0,Ar(Set,Prop)))
      | "cplr" -> (182,(0,Ar(Set,Prop)))
      | "cmr" -> (183,(0,Ar(Set,Prop)))
      | "cltr" -> (184,(0,Ar(Set,Prop)))
      | "cc" -> (185,(0,Ar(Set,Prop)))
      | "cr" -> (186,(0,Ar(Set,Prop)))
      | "cc0" -> (187,(0,Ar(Set,Prop)))
      | "c1" -> (188,(0,Ar(Set,Prop)))
      | "ci" -> (189,(0,Ar(Set,Prop)))
      | "caddc" -> (190,(0,Ar(Set,Prop)))
      | "cltrr" -> (191,(0,Ar(Set,Prop)))
      | "cmul" -> (192,(0,Ar(Set,Prop)))
      | "cpnf" -> (193,(0,Ar(Set,Prop)))
      | "cmnf" -> (194,(0,Ar(Set,Prop)))
      | "cxr" -> (195,(0,Ar(Set,Prop)))
      | "clt" -> (196,(0,Ar(Set,Prop)))
      | "cle" -> (197,(0,Ar(Set,Prop)))
      | "cmin" -> (198,(0,Ar(Set,Prop)))
      | "cneg" -> (199,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "cdiv" -> (200,(0,Ar(Set,Prop)))
      | "cn" -> (201,(0,Ar(Set,Prop)))
      | "c2" -> (202,(0,Ar(Set,Prop)))
      | "c3" -> (203,(0,Ar(Set,Prop)))
      | "c4" -> (204,(0,Ar(Set,Prop)))
      | "c5" -> (205,(0,Ar(Set,Prop)))
      | "c6" -> (206,(0,Ar(Set,Prop)))
      | "c7" -> (207,(0,Ar(Set,Prop)))
      | "c8" -> (208,(0,Ar(Set,Prop)))
      | "c9" -> (209,(0,Ar(Set,Prop)))
      | "c10" -> (210,(0,Ar(Set,Prop)))
      | "cn0" -> (211,(0,Ar(Set,Prop)))
      | "cxnn0" -> (212,(0,Ar(Set,Prop)))
      | "cz" -> (213,(0,Ar(Set,Prop)))
      | "cdc" -> (214,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "cuz" -> (215,(0,Ar(Set,Prop)))
      | "cq" -> (216,(0,Ar(Set,Prop)))
      | "crp" -> (217,(0,Ar(Set,Prop)))
      | "cxne" -> (218,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "cxad" -> (219,(0,Ar(Set,Prop)))
      | "cxmu" -> (220,(0,Ar(Set,Prop)))
      | "cioo" -> (221,(0,Ar(Set,Prop)))
      | "cioc" -> (222,(0,Ar(Set,Prop)))
      | "cico" -> (223,(0,Ar(Set,Prop)))
      | "cicc" -> (224,(0,Ar(Set,Prop)))
      | "cfz" -> (225,(0,Ar(Set,Prop)))
      | "cfzo" -> (226,(0,Ar(Set,Prop)))
      | "cfl" -> (227,(0,Ar(Set,Prop)))
      | "cceil" -> (228,(0,Ar(Set,Prop)))
      | "cmo" -> (229,(0,Ar(Set,Prop)))
      | "cseq" -> (230,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop))))))
      | "cexp" -> (231,(0,Ar(Set,Prop)))
      | "cfa" -> (232,(0,Ar(Set,Prop)))
      | "cbc" -> (233,(0,Ar(Set,Prop)))
      | "chash" -> (234,(0,Ar(Set,Prop)))
      | "cword" -> (235,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "clsw" -> (236,(0,Ar(Set,Prop)))
      | "cconcat" -> (237,(0,Ar(Set,Prop)))
      | "cs1" -> (238,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "csubstr" -> (239,(0,Ar(Set,Prop)))
      | "csplice" -> (240,(0,Ar(Set,Prop)))
      | "creverse" -> (241,(0,Ar(Set,Prop)))
      | "creps" -> (242,(0,Ar(Set,Prop)))
      | "ccsh" -> (243,(0,Ar(Set,Prop)))
      | "cs2" -> (244,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "cs3" -> (245,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop))))))
      | "cs4" -> (246,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))))
      | "cs5" -> (247,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop))))))))
      | "cs6" -> (248,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))))))
      | "cs7" -> (249,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop))))))))))
      | "cs8" -> (250,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))))))))
      | "ctcl" -> (251,(0,Ar(Set,Prop)))
      | "crtcl" -> (252,(0,Ar(Set,Prop)))
      | "crelexp" -> (253,(0,Ar(Set,Prop)))
      | "crtrcl" -> (254,(0,Ar(Set,Prop)))
      | "cshi" -> (255,(0,Ar(Set,Prop)))
      | "csgn" -> (256,(0,Ar(Set,Prop)))
      | "ccj" -> (257,(0,Ar(Set,Prop)))
      | "cre" -> (258,(0,Ar(Set,Prop)))
      | "cim" -> (259,(0,Ar(Set,Prop)))
      | "csqrt" -> (260,(0,Ar(Set,Prop)))
      | "cabs" -> (261,(0,Ar(Set,Prop)))
      | "clsp" -> (262,(0,Ar(Set,Prop)))
      | "cli" -> (263,(0,Ar(Set,Prop)))
      | "crli" -> (264,(0,Ar(Set,Prop)))
      | "co1" -> (265,(0,Ar(Set,Prop)))
      | "clo1" -> (266,(0,Ar(Set,Prop)))
      | "csu" -> (267,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Ar(Set,Prop)),Ar(Set,Prop)))))
      | "cprod" -> (268,(0,Ar(Ar(Set,Ar(Set,Prop)),Ar(Ar(Set,Ar(Set,Prop)),Ar(Set,Prop)))))
      | "cfallfac" -> (269,(0,Ar(Set,Prop)))
      | "crisefac" -> (270,(0,Ar(Set,Prop)))
      | "cbp" -> (271,(0,Ar(Set,Prop)))
      | "ce" -> (272,(0,Ar(Set,Prop)))
      | "ceu" -> (273,(0,Ar(Set,Prop)))
      | "csin" -> (274,(0,Ar(Set,Prop)))
      | "ccos" -> (275,(0,Ar(Set,Prop)))
      | "ctan" -> (276,(0,Ar(Set,Prop)))
      | "cpi" -> (277,(0,Ar(Set,Prop)))
      | "cdvds" -> (278,(0,Ar(Set,Prop)))
      | "cbits" -> (279,(0,Ar(Set,Prop)))
      | "csad" -> (280,(0,Ar(Set,Prop)))
      | "csmu" -> (281,(0,Ar(Set,Prop)))
      | "cgcd" -> (282,(0,Ar(Set,Prop)))
      | "clcm" -> (283,(0,Ar(Set,Prop)))
      | "clcmf" -> (284,(0,Ar(Set,Prop)))
      | "cprime" -> (285,(0,Ar(Set,Prop)))
      | "cnumer" -> (286,(0,Ar(Set,Prop)))
      | "cdenom" -> (287,(0,Ar(Set,Prop)))
      | "codz" -> (288,(0,Ar(Set,Prop)))
      | "cphi" -> (289,(0,Ar(Set,Prop)))
      | "cpc" -> (290,(0,Ar(Set,Prop)))
      | "cgz" -> (291,(0,Ar(Set,Prop)))
      | "cvdwa" -> (292,(0,Ar(Set,Prop)))
      | "cvdwm" -> (293,(0,Ar(Set,Prop)))
      | "cvdwp" -> (294,(0,Ar(Set,Prop)))
      | "cram" -> (295,(0,Ar(Set,Prop)))
      | "cprmo" -> (296,(0,Ar(Set,Prop)))
      | "cstr" -> (297,(0,Ar(Set,Prop)))
      | "cnx" -> (298,(0,Ar(Set,Prop)))
      | "csts" -> (299,(0,Ar(Set,Prop)))
      | "cslot" -> (300,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "cbs" -> (301,(0,Ar(Set,Prop)))
      | "cress" -> (302,(0,Ar(Set,Prop)))
      | "cplusg" -> (303,(0,Ar(Set,Prop)))
      | "cmulr" -> (304,(0,Ar(Set,Prop)))
      | "cstv" -> (305,(0,Ar(Set,Prop)))
      | "csca" -> (306,(0,Ar(Set,Prop)))
      | "cvsca" -> (307,(0,Ar(Set,Prop)))
      | "cip" -> (308,(0,Ar(Set,Prop)))
      | "cts" -> (309,(0,Ar(Set,Prop)))
      | "cple" -> (310,(0,Ar(Set,Prop)))
      | "coc" -> (311,(0,Ar(Set,Prop)))
      | "cds" -> (312,(0,Ar(Set,Prop)))
      | "cunif" -> (313,(0,Ar(Set,Prop)))
      | "chom" -> (314,(0,Ar(Set,Prop)))
      | "cco" -> (315,(0,Ar(Set,Prop)))
      | "crest" -> (316,(0,Ar(Set,Prop)))
      | "ctopn" -> (317,(0,Ar(Set,Prop)))
      | "ctg" -> (318,(0,Ar(Set,Prop)))
      | "cpt" -> (319,(0,Ar(Set,Prop)))
      | "c0g" -> (320,(0,Ar(Set,Prop)))
      | "cgsu" -> (321,(0,Ar(Set,Prop)))
      | "cprds" -> (322,(0,Ar(Set,Prop)))
      | "cpws" -> (323,(0,Ar(Set,Prop)))
      | "cordt" -> (324,(0,Ar(Set,Prop)))
      | "cxrs" -> (325,(0,Ar(Set,Prop)))
      | "cqtop" -> (326,(0,Ar(Set,Prop)))
      | "cimas" -> (327,(0,Ar(Set,Prop)))
      | "cqus" -> (328,(0,Ar(Set,Prop)))
      | "cxps" -> (329,(0,Ar(Set,Prop)))
      | "cmre" -> (330,(0,Ar(Set,Prop)))
      | "cmrc" -> (331,(0,Ar(Set,Prop)))
      | "cmri" -> (332,(0,Ar(Set,Prop)))
      | "cacs" -> (333,(0,Ar(Set,Prop)))
      | "ccat" -> (334,(0,Ar(Set,Prop)))
      | "ccid" -> (335,(0,Ar(Set,Prop)))
      | "chomf" -> (336,(0,Ar(Set,Prop)))
      | "ccomf" -> (337,(0,Ar(Set,Prop)))
      | "coppc" -> (338,(0,Ar(Set,Prop)))
      | "cmon" -> (339,(0,Ar(Set,Prop)))
      | "cepi" -> (340,(0,Ar(Set,Prop)))
      | "csect" -> (341,(0,Ar(Set,Prop)))
      | "cinv" -> (342,(0,Ar(Set,Prop)))
      | "ciso" -> (343,(0,Ar(Set,Prop)))
      | "ccic" -> (344,(0,Ar(Set,Prop)))
      | "cssc" -> (345,(0,Ar(Set,Prop)))
      | "cresc" -> (346,(0,Ar(Set,Prop)))
      | "csubc" -> (347,(0,Ar(Set,Prop)))
      | "cfunc" -> (348,(0,Ar(Set,Prop)))
      | "cidfu" -> (349,(0,Ar(Set,Prop)))
      | "ccofu" -> (350,(0,Ar(Set,Prop)))
      | "cresf" -> (351,(0,Ar(Set,Prop)))
      | "cful" -> (352,(0,Ar(Set,Prop)))
      | "cfth" -> (353,(0,Ar(Set,Prop)))
      | "cnat" -> (354,(0,Ar(Set,Prop)))
      | "cfuc" -> (355,(0,Ar(Set,Prop)))
      | "cinito" -> (356,(0,Ar(Set,Prop)))
      | "ctermo" -> (357,(0,Ar(Set,Prop)))
      | "czeroo" -> (358,(0,Ar(Set,Prop)))
      | "cdoma" -> (359,(0,Ar(Set,Prop)))
      | "ccoda" -> (360,(0,Ar(Set,Prop)))
      | "carw" -> (361,(0,Ar(Set,Prop)))
      | "choma" -> (362,(0,Ar(Set,Prop)))
      | "cida" -> (363,(0,Ar(Set,Prop)))
      | "ccoa" -> (364,(0,Ar(Set,Prop)))
      | "csetc" -> (365,(0,Ar(Set,Prop)))
      | "ccatc" -> (366,(0,Ar(Set,Prop)))
      | "cestrc" -> (367,(0,Ar(Set,Prop)))
      | "cxpc" -> (368,(0,Ar(Set,Prop)))
      | "c1stf" -> (369,(0,Ar(Set,Prop)))
      | "c2ndf" -> (370,(0,Ar(Set,Prop)))
      | "cprf" -> (371,(0,Ar(Set,Prop)))
      | "cevlf" -> (372,(0,Ar(Set,Prop)))
      | "ccurf" -> (373,(0,Ar(Set,Prop)))
      | "cuncf" -> (374,(0,Ar(Set,Prop)))
      | "cdiag" -> (375,(0,Ar(Set,Prop)))
      | "chof" -> (376,(0,Ar(Set,Prop)))
      | "cyon" -> (377,(0,Ar(Set,Prop)))
      | "cpreset" -> (378,(0,Ar(Set,Prop)))
      | "cdrs" -> (379,(0,Ar(Set,Prop)))
      | "cpo" -> (380,(0,Ar(Set,Prop)))
      | "cplt" -> (381,(0,Ar(Set,Prop)))
      | "club" -> (382,(0,Ar(Set,Prop)))
      | "cglb" -> (383,(0,Ar(Set,Prop)))
      | "cjn" -> (384,(0,Ar(Set,Prop)))
      | "cmee" -> (385,(0,Ar(Set,Prop)))
      | "ctos" -> (386,(0,Ar(Set,Prop)))
      | "cp0" -> (387,(0,Ar(Set,Prop)))
      | "cp1" -> (388,(0,Ar(Set,Prop)))
      | "clat" -> (389,(0,Ar(Set,Prop)))
      | "ccla" -> (390,(0,Ar(Set,Prop)))
      | "codu" -> (391,(0,Ar(Set,Prop)))
      | "cipo" -> (392,(0,Ar(Set,Prop)))
      | "cdlat" -> (393,(0,Ar(Set,Prop)))
      | "cps" -> (394,(0,Ar(Set,Prop)))
      | "ctsr" -> (395,(0,Ar(Set,Prop)))
      | "cdir" -> (396,(0,Ar(Set,Prop)))
      | "ctail" -> (397,(0,Ar(Set,Prop)))
      | "cplusf" -> (398,(0,Ar(Set,Prop)))
      | "cmgm" -> (399,(0,Ar(Set,Prop)))
      | "csgrp" -> (400,(0,Ar(Set,Prop)))
      | "cmnd" -> (401,(0,Ar(Set,Prop)))
      | "cmhm" -> (402,(0,Ar(Set,Prop)))
      | "csubmnd" -> (403,(0,Ar(Set,Prop)))
      | "cfrmd" -> (404,(0,Ar(Set,Prop)))
      | "cvrmd" -> (405,(0,Ar(Set,Prop)))
      | "cgrp" -> (406,(0,Ar(Set,Prop)))
      | "cminusg" -> (407,(0,Ar(Set,Prop)))
      | "csg" -> (408,(0,Ar(Set,Prop)))
      | "cmg" -> (409,(0,Ar(Set,Prop)))
      | "csubg" -> (410,(0,Ar(Set,Prop)))
      | "cnsg" -> (411,(0,Ar(Set,Prop)))
      | "cqg" -> (412,(0,Ar(Set,Prop)))
      | "cghm" -> (413,(0,Ar(Set,Prop)))
      | "cgim" -> (414,(0,Ar(Set,Prop)))
      | "cgic" -> (415,(0,Ar(Set,Prop)))
      | "cga" -> (416,(0,Ar(Set,Prop)))
      | "ccntz" -> (417,(0,Ar(Set,Prop)))
      | "ccntr" -> (418,(0,Ar(Set,Prop)))
      | "coppg" -> (419,(0,Ar(Set,Prop)))
      | "csymg" -> (420,(0,Ar(Set,Prop)))
      | "cpmtr" -> (421,(0,Ar(Set,Prop)))
      | "cpsgn" -> (422,(0,Ar(Set,Prop)))
      | "cevpm" -> (423,(0,Ar(Set,Prop)))
      | "cod" -> (424,(0,Ar(Set,Prop)))
      | "cgex" -> (425,(0,Ar(Set,Prop)))
      | "cpgp" -> (426,(0,Ar(Set,Prop)))
      | "cslw" -> (427,(0,Ar(Set,Prop)))
      | "clsm" -> (428,(0,Ar(Set,Prop)))
      | "cpj1" -> (429,(0,Ar(Set,Prop)))
      | "cefg" -> (430,(0,Ar(Set,Prop)))
      | "cfrgp" -> (431,(0,Ar(Set,Prop)))
      | "cvrgp" -> (432,(0,Ar(Set,Prop)))
      | "ccmn" -> (433,(0,Ar(Set,Prop)))
      | "cabl" -> (434,(0,Ar(Set,Prop)))
      | "ccyg" -> (435,(0,Ar(Set,Prop)))
      | "cdprd" -> (436,(0,Ar(Set,Prop)))
      | "cdpj" -> (437,(0,Ar(Set,Prop)))
      | "cmgp" -> (438,(0,Ar(Set,Prop)))
      | "cur" -> (439,(0,Ar(Set,Prop)))
      | "csrg" -> (440,(0,Ar(Set,Prop)))
      | "crg" -> (441,(0,Ar(Set,Prop)))
      | "ccrg" -> (442,(0,Ar(Set,Prop)))
      | "coppr" -> (443,(0,Ar(Set,Prop)))
      | "cdsr" -> (444,(0,Ar(Set,Prop)))
      | "cui" -> (445,(0,Ar(Set,Prop)))
      | "cir" -> (446,(0,Ar(Set,Prop)))
      | "cinvr" -> (447,(0,Ar(Set,Prop)))
      | "cdvr" -> (448,(0,Ar(Set,Prop)))
      | "crpm" -> (449,(0,Ar(Set,Prop)))
      | "crh" -> (450,(0,Ar(Set,Prop)))
      | "crs" -> (451,(0,Ar(Set,Prop)))
      | "cric" -> (452,(0,Ar(Set,Prop)))
      | "cdr" -> (453,(0,Ar(Set,Prop)))
      | "cfield" -> (454,(0,Ar(Set,Prop)))
      | "csubrg" -> (455,(0,Ar(Set,Prop)))
      | "crgspn" -> (456,(0,Ar(Set,Prop)))
      | "cabv" -> (457,(0,Ar(Set,Prop)))
      | "cstf" -> (458,(0,Ar(Set,Prop)))
      | "csr" -> (459,(0,Ar(Set,Prop)))
      | "clmod" -> (460,(0,Ar(Set,Prop)))
      | "cscaf" -> (461,(0,Ar(Set,Prop)))
      | "clss" -> (462,(0,Ar(Set,Prop)))
      | "clspn" -> (463,(0,Ar(Set,Prop)))
      | "clmhm" -> (464,(0,Ar(Set,Prop)))
      | "clmim" -> (465,(0,Ar(Set,Prop)))
      | "clmic" -> (466,(0,Ar(Set,Prop)))
      | "clbs" -> (467,(0,Ar(Set,Prop)))
      | "clvec" -> (468,(0,Ar(Set,Prop)))
      | "csra" -> (469,(0,Ar(Set,Prop)))
      | "crglmod" -> (470,(0,Ar(Set,Prop)))
      | "clidl" -> (471,(0,Ar(Set,Prop)))
      | "crsp" -> (472,(0,Ar(Set,Prop)))
      | "c2idl" -> (473,(0,Ar(Set,Prop)))
      | "clpidl" -> (474,(0,Ar(Set,Prop)))
      | "clpir" -> (475,(0,Ar(Set,Prop)))
      | "cnzr" -> (476,(0,Ar(Set,Prop)))
      | "crlreg" -> (477,(0,Ar(Set,Prop)))
      | "cdomn" -> (478,(0,Ar(Set,Prop)))
      | "cidom" -> (479,(0,Ar(Set,Prop)))
      | "cpid" -> (480,(0,Ar(Set,Prop)))
      | "casa" -> (481,(0,Ar(Set,Prop)))
      | "casp" -> (482,(0,Ar(Set,Prop)))
      | "cascl" -> (483,(0,Ar(Set,Prop)))
      | "cmps" -> (484,(0,Ar(Set,Prop)))
      | "cmvr" -> (485,(0,Ar(Set,Prop)))
      | "cmpl" -> (486,(0,Ar(Set,Prop)))
      | "cltb" -> (487,(0,Ar(Set,Prop)))
      | "copws" -> (488,(0,Ar(Set,Prop)))
      | "ces" -> (489,(0,Ar(Set,Prop)))
      | "cevl" -> (490,(0,Ar(Set,Prop)))
      | "cmhp" -> (491,(0,Ar(Set,Prop)))
      | "cpsd" -> (492,(0,Ar(Set,Prop)))
      | "cslv" -> (493,(0,Ar(Set,Prop)))
      | "cai" -> (494,(0,Ar(Set,Prop)))
      | "cps1" -> (495,(0,Ar(Set,Prop)))
      | "cv1" -> (496,(0,Ar(Set,Prop)))
      | "cpl1" -> (497,(0,Ar(Set,Prop)))
      | "cco1" -> (498,(0,Ar(Set,Prop)))
      | "ctp1" -> (499,(0,Ar(Set,Prop)))
      | "ces1" -> (500,(0,Ar(Set,Prop)))
      | "ce1" -> (501,(0,Ar(Set,Prop)))
      | "cpsmet" -> (502,(0,Ar(Set,Prop)))
      | "cxmt" -> (503,(0,Ar(Set,Prop)))
      | "cme" -> (504,(0,Ar(Set,Prop)))
      | "cbl" -> (505,(0,Ar(Set,Prop)))
      | "cfbas" -> (506,(0,Ar(Set,Prop)))
      | "cfg" -> (507,(0,Ar(Set,Prop)))
      | "cmopn" -> (508,(0,Ar(Set,Prop)))
      | "cmetu" -> (509,(0,Ar(Set,Prop)))
      | "ccnfld" -> (510,(0,Ar(Set,Prop)))
      | "zring" -> (511,(0,Ar(Set,Prop)))
      | "czrh" -> (512,(0,Ar(Set,Prop)))
      | "czlm" -> (513,(0,Ar(Set,Prop)))
      | "cchr" -> (514,(0,Ar(Set,Prop)))
      | "czn" -> (515,(0,Ar(Set,Prop)))
      | "crefld" -> (516,(0,Ar(Set,Prop)))
      | "cphl" -> (517,(0,Ar(Set,Prop)))
      | "cipf" -> (518,(0,Ar(Set,Prop)))
      | "cocv" -> (519,(0,Ar(Set,Prop)))
      | "ccss" -> (520,(0,Ar(Set,Prop)))
      | "cthl" -> (521,(0,Ar(Set,Prop)))
      | "cpj" -> (522,(0,Ar(Set,Prop)))
      | "chs" -> (523,(0,Ar(Set,Prop)))
      | "cobs" -> (524,(0,Ar(Set,Prop)))
      | "cdsmm" -> (525,(0,Ar(Set,Prop)))
      | "cfrlm" -> (526,(0,Ar(Set,Prop)))
      | "cuvc" -> (527,(0,Ar(Set,Prop)))
      | "clindf" -> (528,(0,Ar(Set,Prop)))
      | "clinds" -> (529,(0,Ar(Set,Prop)))
      | "cmmul" -> (530,(0,Ar(Set,Prop)))
      | "cmat" -> (531,(0,Ar(Set,Prop)))
      | "cdmat" -> (532,(0,Ar(Set,Prop)))
      | "cscmat" -> (533,(0,Ar(Set,Prop)))
      | "cmvmul" -> (534,(0,Ar(Set,Prop)))
      | "cmarrep" -> (535,(0,Ar(Set,Prop)))
      | "cmatrepV" -> (536,(0,Ar(Set,Prop)))
      | "csubma" -> (537,(0,Ar(Set,Prop)))
      | "cmdat" -> (538,(0,Ar(Set,Prop)))
      | "cmadu" -> (539,(0,Ar(Set,Prop)))
      | "cminmar1" -> (540,(0,Ar(Set,Prop)))
      | "ccpmat" -> (541,(0,Ar(Set,Prop)))
      | "cmat2pmat" -> (542,(0,Ar(Set,Prop)))
      | "ccpmat2mat" -> (543,(0,Ar(Set,Prop)))
      | "cdecpmat" -> (544,(0,Ar(Set,Prop)))
      | "cpm2mp" -> (545,(0,Ar(Set,Prop)))
      | "cchpmat" -> (546,(0,Ar(Set,Prop)))
      | "ctop" -> (547,(0,Ar(Set,Prop)))
      | "ctopon" -> (548,(0,Ar(Set,Prop)))
      | "ctps" -> (549,(0,Ar(Set,Prop)))
      | "ctb" -> (550,(0,Ar(Set,Prop)))
      | "ccld" -> (551,(0,Ar(Set,Prop)))
      | "cnt" -> (552,(0,Ar(Set,Prop)))
      | "ccl" -> (553,(0,Ar(Set,Prop)))
      | "cnei" -> (554,(0,Ar(Set,Prop)))
      | "clp" -> (555,(0,Ar(Set,Prop)))
      | "cperf" -> (556,(0,Ar(Set,Prop)))
      | "ccn" -> (557,(0,Ar(Set,Prop)))
      | "ccnp" -> (558,(0,Ar(Set,Prop)))
      | "clm" -> (559,(0,Ar(Set,Prop)))
      | "ct0" -> (560,(0,Ar(Set,Prop)))
      | "ct1" -> (561,(0,Ar(Set,Prop)))
      | "cha" -> (562,(0,Ar(Set,Prop)))
      | "creg" -> (563,(0,Ar(Set,Prop)))
      | "cnrm" -> (564,(0,Ar(Set,Prop)))
      | "ccnrm" -> (565,(0,Ar(Set,Prop)))
      | "cpnrm" -> (566,(0,Ar(Set,Prop)))
      | "ccmp" -> (567,(0,Ar(Set,Prop)))
      | "cconn" -> (568,(0,Ar(Set,Prop)))
      | "c1stc" -> (569,(0,Ar(Set,Prop)))
      | "c2ndc" -> (570,(0,Ar(Set,Prop)))
      | "clly" -> (571,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "cnlly" -> (572,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "cref" -> (573,(0,Ar(Set,Prop)))
      | "cptfin" -> (574,(0,Ar(Set,Prop)))
      | "clocfin" -> (575,(0,Ar(Set,Prop)))
      | "ckgen" -> (576,(0,Ar(Set,Prop)))
      | "ctx" -> (577,(0,Ar(Set,Prop)))
      | "cxko" -> (578,(0,Ar(Set,Prop)))
      | "ckq" -> (579,(0,Ar(Set,Prop)))
      | "chmeo" -> (580,(0,Ar(Set,Prop)))
      | "chmph" -> (581,(0,Ar(Set,Prop)))
      | "cfil" -> (582,(0,Ar(Set,Prop)))
      | "cufil" -> (583,(0,Ar(Set,Prop)))
      | "cufl" -> (584,(0,Ar(Set,Prop)))
      | "cfm" -> (585,(0,Ar(Set,Prop)))
      | "cflim" -> (586,(0,Ar(Set,Prop)))
      | "cflf" -> (587,(0,Ar(Set,Prop)))
      | "cfcls" -> (588,(0,Ar(Set,Prop)))
      | "cfcf" -> (589,(0,Ar(Set,Prop)))
      | "ccnext" -> (590,(0,Ar(Set,Prop)))
      | "ctmd" -> (591,(0,Ar(Set,Prop)))
      | "ctgp" -> (592,(0,Ar(Set,Prop)))
      | "ctsu" -> (593,(0,Ar(Set,Prop)))
      | "ctrg" -> (594,(0,Ar(Set,Prop)))
      | "ctdrg" -> (595,(0,Ar(Set,Prop)))
      | "ctlm" -> (596,(0,Ar(Set,Prop)))
      | "ctvc" -> (597,(0,Ar(Set,Prop)))
      | "cust" -> (598,(0,Ar(Set,Prop)))
      | "cutop" -> (599,(0,Ar(Set,Prop)))
      | "cuss" -> (600,(0,Ar(Set,Prop)))
      | "cusp" -> (601,(0,Ar(Set,Prop)))
      | "ctus" -> (602,(0,Ar(Set,Prop)))
      | "cucn" -> (603,(0,Ar(Set,Prop)))
      | "ccfilu" -> (604,(0,Ar(Set,Prop)))
      | "ccusp" -> (605,(0,Ar(Set,Prop)))
      | "cxme" -> (606,(0,Ar(Set,Prop)))
      | "cmt" -> (607,(0,Ar(Set,Prop)))
      | "ctmt" -> (608,(0,Ar(Set,Prop)))
      | "cnm" -> (609,(0,Ar(Set,Prop)))
      | "cngp" -> (610,(0,Ar(Set,Prop)))
      | "ctng" -> (611,(0,Ar(Set,Prop)))
      | "cnrg" -> (612,(0,Ar(Set,Prop)))
      | "cnlm" -> (613,(0,Ar(Set,Prop)))
      | "cnvc" -> (614,(0,Ar(Set,Prop)))
      | "cnmo" -> (615,(0,Ar(Set,Prop)))
      | "cnghm" -> (616,(0,Ar(Set,Prop)))
      | "cnmhm" -> (617,(0,Ar(Set,Prop)))
      | "cii" -> (618,(0,Ar(Set,Prop)))
      | "ccncf" -> (619,(0,Ar(Set,Prop)))
      | "chtpy" -> (620,(0,Ar(Set,Prop)))
      | "cphtpy" -> (621,(0,Ar(Set,Prop)))
      | "cphtpc" -> (622,(0,Ar(Set,Prop)))
      | "cpco" -> (623,(0,Ar(Set,Prop)))
      | "comi" -> (624,(0,Ar(Set,Prop)))
      | "comn" -> (625,(0,Ar(Set,Prop)))
      | "cpi1" -> (626,(0,Ar(Set,Prop)))
      | "cpin" -> (627,(0,Ar(Set,Prop)))
      | "cclm" -> (628,(0,Ar(Set,Prop)))
      | "ccvs" -> (629,(0,Ar(Set,Prop)))
      | "ccph" -> (630,(0,Ar(Set,Prop)))
      | "ctch" -> (631,(0,Ar(Set,Prop)))
      | "ccfil" -> (632,(0,Ar(Set,Prop)))
      | "cca" -> (633,(0,Ar(Set,Prop)))
      | "cms" -> (634,(0,Ar(Set,Prop)))
      | "ccms" -> (635,(0,Ar(Set,Prop)))
      | "cbn" -> (636,(0,Ar(Set,Prop)))
      | "chl" -> (637,(0,Ar(Set,Prop)))
      | "crrx" -> (638,(0,Ar(Set,Prop)))
      | "cehl" -> (639,(0,Ar(Set,Prop)))
      | "covol" -> (640,(0,Ar(Set,Prop)))
      | "cvol" -> (641,(0,Ar(Set,Prop)))
      | "cmbf" -> (642,(0,Ar(Set,Prop)))
      | "citg1" -> (643,(0,Ar(Set,Prop)))
      | "citg2" -> (644,(0,Ar(Set,Prop)))
      | "cibl" -> (645,(0,Ar(Set,Prop)))
      | "citg" -> (646,(0,Ar(Ar(Set,Ar(Set,Prop)),Ar(Ar(Set,Ar(Set,Prop)),Ar(Set,Prop)))))
      | "c0p" -> (647,(0,Ar(Set,Prop)))
      | "cdit" -> (648,(0,Ar(Ar(Set,Ar(Set,Prop)),Ar(Ar(Set,Ar(Set,Prop)),Ar(Ar(Set,Ar(Set,Prop)),Ar(Set,Prop))))))
      | "climc" -> (649,(0,Ar(Set,Prop)))
      | "cdv" -> (650,(0,Ar(Set,Prop)))
      | "cdvn" -> (651,(0,Ar(Set,Prop)))
      | "ccpn" -> (652,(0,Ar(Set,Prop)))
      | "cmdg" -> (653,(0,Ar(Set,Prop)))
      | "cdg1" -> (654,(0,Ar(Set,Prop)))
      | "cmn1" -> (655,(0,Ar(Set,Prop)))
      | "cuc1p" -> (656,(0,Ar(Set,Prop)))
      | "cq1p" -> (657,(0,Ar(Set,Prop)))
      | "cr1p" -> (658,(0,Ar(Set,Prop)))
      | "cig1p" -> (659,(0,Ar(Set,Prop)))
      | "cply" -> (660,(0,Ar(Set,Prop)))
      | "cidp" -> (661,(0,Ar(Set,Prop)))
      | "ccoe" -> (662,(0,Ar(Set,Prop)))
      | "cdgr" -> (663,(0,Ar(Set,Prop)))
      | "cquot" -> (664,(0,Ar(Set,Prop)))
      | "caa" -> (665,(0,Ar(Set,Prop)))
      | "ctayl" -> (666,(0,Ar(Set,Prop)))
      | "cana" -> (667,(0,Ar(Set,Prop)))
      | "culm" -> (668,(0,Ar(Set,Prop)))
      | "clog" -> (669,(0,Ar(Set,Prop)))
      | "ccxp" -> (670,(0,Ar(Set,Prop)))
      | "clogb" -> (671,(0,Ar(Set,Prop)))
      | "casin" -> (672,(0,Ar(Set,Prop)))
      | "cacos" -> (673,(0,Ar(Set,Prop)))
      | "catan" -> (674,(0,Ar(Set,Prop)))
      | "carea" -> (675,(0,Ar(Set,Prop)))
      | "cem" -> (676,(0,Ar(Set,Prop)))
      | "czeta" -> (677,(0,Ar(Set,Prop)))
      | "clgam" -> (678,(0,Ar(Set,Prop)))
      | "cgam" -> (679,(0,Ar(Set,Prop)))
      | "cigam" -> (680,(0,Ar(Set,Prop)))
      | "ccht" -> (681,(0,Ar(Set,Prop)))
      | "cvma" -> (682,(0,Ar(Set,Prop)))
      | "cchp" -> (683,(0,Ar(Set,Prop)))
      | "cppi" -> (684,(0,Ar(Set,Prop)))
      | "cmu" -> (685,(0,Ar(Set,Prop)))
      | "csgm" -> (686,(0,Ar(Set,Prop)))
      | "cdchr" -> (687,(0,Ar(Set,Prop)))
      | "clgs" -> (688,(0,Ar(Set,Prop)))
      | "cstrkg" -> (689,(0,Ar(Set,Prop)))
      | "cstrkgc" -> (690,(0,Ar(Set,Prop)))
      | "cstrkgb" -> (691,(0,Ar(Set,Prop)))
      | "cstrkgcb" -> (692,(0,Ar(Set,Prop)))
      | "cstrkgld" -> (693,(0,Ar(Set,Prop)))
      | "cstrkge" -> (694,(0,Ar(Set,Prop)))
      | "citv" -> (695,(0,Ar(Set,Prop)))
      | "clng" -> (696,(0,Ar(Set,Prop)))
      | "ccgrg" -> (697,(0,Ar(Set,Prop)))
      | "cismt" -> (698,(0,Ar(Set,Prop)))
      | "cleg" -> (699,(0,Ar(Set,Prop)))
      | "chlg" -> (700,(0,Ar(Set,Prop)))
      | "cmir" -> (701,(0,Ar(Set,Prop)))
      | "crag" -> (702,(0,Ar(Set,Prop)))
      | "cperpg" -> (703,(0,Ar(Set,Prop)))
      | "chpg" -> (704,(0,Ar(Set,Prop)))
      | "cmid" -> (705,(0,Ar(Set,Prop)))
      | "clmi" -> (706,(0,Ar(Set,Prop)))
      | "ccgra" -> (707,(0,Ar(Set,Prop)))
      | "cinag" -> (708,(0,Ar(Set,Prop)))
      | "cleag" -> (709,(0,Ar(Set,Prop)))
      | "ceqlg" -> (710,(0,Ar(Set,Prop)))
      | "cttg" -> (711,(0,Ar(Set,Prop)))
      | "cee" -> (712,(0,Ar(Set,Prop)))
      | "cbtwn" -> (713,(0,Ar(Set,Prop)))
      | "ccgr" -> (714,(0,Ar(Set,Prop)))
      | "ceeng" -> (715,(0,Ar(Set,Prop)))
      | "cedgf" -> (716,(0,Ar(Set,Prop)))
      | "cvtx" -> (717,(0,Ar(Set,Prop)))
      | "ciedg" -> (718,(0,Ar(Set,Prop)))
      | "cedg" -> (719,(0,Ar(Set,Prop)))
      | "cuhgr" -> (720,(0,Ar(Set,Prop)))
      | "cushgr" -> (721,(0,Ar(Set,Prop)))
      | "cupgr" -> (722,(0,Ar(Set,Prop)))
      | "cumgr" -> (723,(0,Ar(Set,Prop)))
      | "cuspgr" -> (724,(0,Ar(Set,Prop)))
      | "cusgr" -> (725,(0,Ar(Set,Prop)))
      | "csubgr" -> (726,(0,Ar(Set,Prop)))
      | "cfusgr" -> (727,(0,Ar(Set,Prop)))
      | "cnbgr" -> (728,(0,Ar(Set,Prop)))
      | "cuvtx" -> (729,(0,Ar(Set,Prop)))
      | "ccplgr" -> (730,(0,Ar(Set,Prop)))
      | "ccusgr" -> (731,(0,Ar(Set,Prop)))
      | "cvtxdg" -> (732,(0,Ar(Set,Prop)))
      | "crgr" -> (733,(0,Ar(Set,Prop)))
      | "crusgr" -> (734,(0,Ar(Set,Prop)))
      | "cewlks" -> (735,(0,Ar(Set,Prop)))
      | "cwlks" -> (736,(0,Ar(Set,Prop)))
      | "cwlkson" -> (737,(0,Ar(Set,Prop)))
      | "ctrls" -> (738,(0,Ar(Set,Prop)))
      | "ctrlson" -> (739,(0,Ar(Set,Prop)))
      | "cpths" -> (740,(0,Ar(Set,Prop)))
      | "cspths" -> (741,(0,Ar(Set,Prop)))
      | "cpthson" -> (742,(0,Ar(Set,Prop)))
      | "cspthson" -> (743,(0,Ar(Set,Prop)))
      | "cclwlks" -> (744,(0,Ar(Set,Prop)))
      | "ccrcts" -> (745,(0,Ar(Set,Prop)))
      | "ccycls" -> (746,(0,Ar(Set,Prop)))
      | "cwwlks" -> (747,(0,Ar(Set,Prop)))
      | "cwwlksn" -> (748,(0,Ar(Set,Prop)))
      | "cwwlksnon" -> (749,(0,Ar(Set,Prop)))
      | "cwwspthsn" -> (750,(0,Ar(Set,Prop)))
      | "cwwspthsnon" -> (751,(0,Ar(Set,Prop)))
      | "cclwwlk" -> (752,(0,Ar(Set,Prop)))
      | "cclwwlkn" -> (753,(0,Ar(Set,Prop)))
      | "cclwwlknold" -> (754,(0,Ar(Set,Prop)))
      | "cclwwlknon" -> (755,(0,Ar(Set,Prop)))
      | "cconngr" -> (756,(0,Ar(Set,Prop)))
      | "ceupth" -> (757,(0,Ar(Set,Prop)))
      | "cfrgr" -> (758,(0,Ar(Set,Prop)))
      | "cplig" -> (759,(0,Ar(Set,Prop)))
      | "cgr" -> (760,(0,Ar(Set,Prop)))
      | "cgi" -> (761,(0,Ar(Set,Prop)))
      | "cgn" -> (762,(0,Ar(Set,Prop)))
      | "cgs" -> (763,(0,Ar(Set,Prop)))
      | "cablo" -> (764,(0,Ar(Set,Prop)))
      | "cvc" -> (765,(0,Ar(Set,Prop)))
      | "cnv" -> (766,(0,Ar(Set,Prop)))
      | "cpv" -> (767,(0,Ar(Set,Prop)))
      | "cba" -> (768,(0,Ar(Set,Prop)))
      | "cns" -> (769,(0,Ar(Set,Prop)))
      | "cn0v" -> (770,(0,Ar(Set,Prop)))
      | "cnsb" -> (771,(0,Ar(Set,Prop)))
      | "cnmcv" -> (772,(0,Ar(Set,Prop)))
      | "cims" -> (773,(0,Ar(Set,Prop)))
      | "cdip" -> (774,(0,Ar(Set,Prop)))
      | "css" -> (775,(0,Ar(Set,Prop)))
      | "clno" -> (776,(0,Ar(Set,Prop)))
      | "cnmoo" -> (777,(0,Ar(Set,Prop)))
      | "cblo" -> (778,(0,Ar(Set,Prop)))
      | "c0o" -> (779,(0,Ar(Set,Prop)))
      | "caj" -> (780,(0,Ar(Set,Prop)))
      | "chmo" -> (781,(0,Ar(Set,Prop)))
      | "ccphlo" -> (782,(0,Ar(Set,Prop)))
      | "ccbn" -> (783,(0,Ar(Set,Prop)))
      | "chlo" -> (784,(0,Ar(Set,Prop)))
      | "chil" -> (785,(0,Ar(Set,Prop)))
      | "cva" -> (786,(0,Ar(Set,Prop)))
      | "csm" -> (787,(0,Ar(Set,Prop)))
      | "csp" -> (788,(0,Ar(Set,Prop)))
      | "cno" -> (789,(0,Ar(Set,Prop)))
      | "c0v" -> (790,(0,Ar(Set,Prop)))
      | "cmv" -> (791,(0,Ar(Set,Prop)))
      | "ccau" -> (792,(0,Ar(Set,Prop)))
      | "chli" -> (793,(0,Ar(Set,Prop)))
      | "csh" -> (794,(0,Ar(Set,Prop)))
      | "cch" -> (795,(0,Ar(Set,Prop)))
      | "cort" -> (796,(0,Ar(Set,Prop)))
      | "cph" -> (797,(0,Ar(Set,Prop)))
      | "cspn" -> (798,(0,Ar(Set,Prop)))
      | "chj" -> (799,(0,Ar(Set,Prop)))
      | "chsup" -> (800,(0,Ar(Set,Prop)))
      | "c0h" -> (801,(0,Ar(Set,Prop)))
      | "ccm" -> (802,(0,Ar(Set,Prop)))
      | "cpjh" -> (803,(0,Ar(Set,Prop)))
      | "chos" -> (804,(0,Ar(Set,Prop)))
      | "chot" -> (805,(0,Ar(Set,Prop)))
      | "chod" -> (806,(0,Ar(Set,Prop)))
      | "chfs" -> (807,(0,Ar(Set,Prop)))
      | "chft" -> (808,(0,Ar(Set,Prop)))
      | "ch0o" -> (809,(0,Ar(Set,Prop)))
      | "chio" -> (810,(0,Ar(Set,Prop)))
      | "cnop" -> (811,(0,Ar(Set,Prop)))
      | "ccop" -> (812,(0,Ar(Set,Prop)))
      | "clo" -> (813,(0,Ar(Set,Prop)))
      | "cbo" -> (814,(0,Ar(Set,Prop)))
      | "cuo" -> (815,(0,Ar(Set,Prop)))
      | "cho" -> (816,(0,Ar(Set,Prop)))
      | "cnmf" -> (817,(0,Ar(Set,Prop)))
      | "cnl" -> (818,(0,Ar(Set,Prop)))
      | "ccnfn" -> (819,(0,Ar(Set,Prop)))
      | "clf" -> (820,(0,Ar(Set,Prop)))
      | "cado" -> (821,(0,Ar(Set,Prop)))
      | "cbr" -> (822,(0,Ar(Set,Prop)))
      | "ck" -> (823,(0,Ar(Set,Prop)))
      | "cleo" -> (824,(0,Ar(Set,Prop)))
      | "cei" -> (825,(0,Ar(Set,Prop)))
      | "cel" -> (826,(0,Ar(Set,Prop)))
      | "cspc" -> (827,(0,Ar(Set,Prop)))
      | "cst" -> (828,(0,Ar(Set,Prop)))
      | "chst" -> (829,(0,Ar(Set,Prop)))
      | "ccv" -> (830,(0,Ar(Set,Prop)))
      | "cat" -> (831,(0,Ar(Set,Prop)))
      | "cmd" -> (832,(0,Ar(Set,Prop)))
      | "cdmd" -> (833,(0,Ar(Set,Prop)))
      | "cdp2" -> (834,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "cdp" -> (835,(0,Ar(Set,Prop)))
      | "cxdiv" -> (836,(0,Ar(Set,Prop)))
      | "comnd" -> (837,(0,Ar(Set,Prop)))
      | "cogrp" -> (838,(0,Ar(Set,Prop)))
      | "csgns" -> (839,(0,Ar(Set,Prop)))
      | "cinftm" -> (840,(0,Ar(Set,Prop)))
      | "carchi" -> (841,(0,Ar(Set,Prop)))
      | "cslmd" -> (842,(0,Ar(Set,Prop)))
      | "corng" -> (843,(0,Ar(Set,Prop)))
      | "cofld" -> (844,(0,Ar(Set,Prop)))
      | "cresv" -> (845,(0,Ar(Set,Prop)))
      | "csmat" -> (846,(0,Ar(Set,Prop)))
      | "clmat" -> (847,(0,Ar(Set,Prop)))
      | "ccref" -> (848,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "cldlf" -> (849,(0,Ar(Set,Prop)))
      | "cpcmp" -> (850,(0,Ar(Set,Prop)))
      | "cmetid" -> (851,(0,Ar(Set,Prop)))
      | "cpstm" -> (852,(0,Ar(Set,Prop)))
      | "chcmp" -> (853,(0,Ar(Set,Prop)))
      | "cqqh" -> (854,(0,Ar(Set,Prop)))
      | "crrh" -> (855,(0,Ar(Set,Prop)))
      | "crrext" -> (856,(0,Ar(Set,Prop)))
      | "cxrh" -> (857,(0,Ar(Set,Prop)))
      | "cmntop" -> (858,(0,Ar(Set,Prop)))
      | "cind" -> (859,(0,Ar(Set,Prop)))
      | "cesum" -> (860,(0,Ar(Ar(Set,Ar(Set,Prop)),Ar(Ar(Set,Ar(Set,Prop)),Ar(Set,Prop)))))
      | "cofc" -> (861,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "csiga" -> (862,(0,Ar(Set,Prop)))
      | "csigagen" -> (863,(0,Ar(Set,Prop)))
      | "cbrsiga" -> (864,(0,Ar(Set,Prop)))
      | "csx" -> (865,(0,Ar(Set,Prop)))
      | "cmeas" -> (866,(0,Ar(Set,Prop)))
      | "cdde" -> (867,(0,Ar(Set,Prop)))
      | "cae" -> (868,(0,Ar(Set,Prop)))
      | "cfae" -> (869,(0,Ar(Set,Prop)))
      | "cmbfm" -> (870,(0,Ar(Set,Prop)))
      | "coms" -> (871,(0,Ar(Set,Prop)))
      | "ccarsg" -> (872,(0,Ar(Set,Prop)))
      | "citgm" -> (873,(0,Ar(Set,Prop)))
      | "csitm" -> (874,(0,Ar(Set,Prop)))
      | "csitg" -> (875,(0,Ar(Set,Prop)))
      | "csseq" -> (876,(0,Ar(Set,Prop)))
      | "cfib" -> (877,(0,Ar(Set,Prop)))
      | "cprb" -> (878,(0,Ar(Set,Prop)))
      | "ccprob" -> (879,(0,Ar(Set,Prop)))
      | "crrv" -> (880,(0,Ar(Set,Prop)))
      | "corvc" -> (881,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "crepr" -> (882,(0,Ar(Set,Prop)))
      | "cvts" -> (883,(0,Ar(Set,Prop)))
      | "cstrkg2d" -> (884,(0,Ar(Set,Prop)))
      | "cafs" -> (885,(0,Ar(Set,Prop)))
      | "w_bnj17" -> (886,(0,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Prop))))))
      | "c_bnj14" -> (887,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop))))))
      | "w_bnj13" -> (888,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Prop))))
      | "w_bnj15" -> (889,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Prop))))
      | "c_bnj18" -> (890,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop))))))
      | "w_bnj19" -> (891,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Prop)))))
      | "cretr" -> (892,(0,Ar(Set,Prop)))
      | "cpconn" -> (893,(0,Ar(Set,Prop)))
      | "csconn" -> (894,(0,Ar(Set,Prop)))
      | "ccvm" -> (895,(0,Ar(Set,Prop)))
      | "cgoe" -> (896,(0,Ar(Set,Prop)))
      | "cgna" -> (897,(0,Ar(Set,Prop)))
      | "cgol" -> (898,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "csat" -> (899,(0,Ar(Set,Prop)))
      | "cfmla" -> (900,(0,Ar(Set,Prop)))
      | "csate" -> (901,(0,Ar(Set,Prop)))
      | "cprv" -> (902,(0,Ar(Set,Prop)))
      | "cgon" -> (903,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "cgoa" -> (904,(0,Ar(Set,Prop)))
      | "cgoi" -> (905,(0,Ar(Set,Prop)))
      | "cgoo" -> (906,(0,Ar(Set,Prop)))
      | "cgob" -> (907,(0,Ar(Set,Prop)))
      | "cgoq" -> (908,(0,Ar(Set,Prop)))
      | "cgox" -> (909,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "cgze" -> (910,(0,Ar(Set,Prop)))
      | "cgzr" -> (911,(0,Ar(Set,Prop)))
      | "cgzp" -> (912,(0,Ar(Set,Prop)))
      | "cgzu" -> (913,(0,Ar(Set,Prop)))
      | "cgzg" -> (914,(0,Ar(Set,Prop)))
      | "cgzi" -> (915,(0,Ar(Set,Prop)))
      | "cgzf" -> (916,(0,Ar(Set,Prop)))
      | "cmcn" -> (917,(0,Ar(Set,Prop)))
      | "cmvar" -> (918,(0,Ar(Set,Prop)))
      | "cmty" -> (919,(0,Ar(Set,Prop)))
      | "cmvt" -> (920,(0,Ar(Set,Prop)))
      | "cmtc" -> (921,(0,Ar(Set,Prop)))
      | "cmax" -> (922,(0,Ar(Set,Prop)))
      | "cmrex" -> (923,(0,Ar(Set,Prop)))
      | "cmex" -> (924,(0,Ar(Set,Prop)))
      | "cmdv" -> (925,(0,Ar(Set,Prop)))
      | "cmvrs" -> (926,(0,Ar(Set,Prop)))
      | "cmrsub" -> (927,(0,Ar(Set,Prop)))
      | "cmsub" -> (928,(0,Ar(Set,Prop)))
      | "cmvh" -> (929,(0,Ar(Set,Prop)))
      | "cmpst" -> (930,(0,Ar(Set,Prop)))
      | "cmsr" -> (931,(0,Ar(Set,Prop)))
      | "cmsta" -> (932,(0,Ar(Set,Prop)))
      | "cmfs" -> (933,(0,Ar(Set,Prop)))
      | "cmcls" -> (934,(0,Ar(Set,Prop)))
      | "cmpps" -> (935,(0,Ar(Set,Prop)))
      | "cmthm" -> (936,(0,Ar(Set,Prop)))
      | "cm0s" -> (937,(0,Ar(Set,Prop)))
      | "cmsa" -> (938,(0,Ar(Set,Prop)))
      | "cmwgfs" -> (939,(0,Ar(Set,Prop)))
      | "cmsy" -> (940,(0,Ar(Set,Prop)))
      | "cmesy" -> (941,(0,Ar(Set,Prop)))
      | "cmgfs" -> (942,(0,Ar(Set,Prop)))
      | "cmtree" -> (943,(0,Ar(Set,Prop)))
      | "cmst" -> (944,(0,Ar(Set,Prop)))
      | "cmsax" -> (945,(0,Ar(Set,Prop)))
      | "cmufs" -> (946,(0,Ar(Set,Prop)))
      | "cmuv" -> (947,(0,Ar(Set,Prop)))
      | "cmvl" -> (948,(0,Ar(Set,Prop)))
      | "cmvsb" -> (949,(0,Ar(Set,Prop)))
      | "cmfsh" -> (950,(0,Ar(Set,Prop)))
      | "cmfr" -> (951,(0,Ar(Set,Prop)))
      | "cmevl" -> (952,(0,Ar(Set,Prop)))
      | "cmdl" -> (953,(0,Ar(Set,Prop)))
      | "cusyn" -> (954,(0,Ar(Set,Prop)))
      | "cgmdl" -> (955,(0,Ar(Set,Prop)))
      | "cmitp" -> (956,(0,Ar(Set,Prop)))
      | "cmfitp" -> (957,(0,Ar(Set,Prop)))
      | "citr" -> (958,(0,Ar(Set,Prop)))
      | "ccpms" -> (959,(0,Ar(Set,Prop)))
      | "chlb" -> (960,(0,Ar(Set,Prop)))
      | "chlim" -> (961,(0,Ar(Set,Prop)))
      | "cpfl" -> (962,(0,Ar(Set,Prop)))
      | "csf1" -> (963,(0,Ar(Set,Prop)))
      | "csf" -> (964,(0,Ar(Set,Prop)))
      | "cpsl" -> (965,(0,Ar(Set,Prop)))
      | "czr" -> (966,(0,Ar(Set,Prop)))
      | "cgf" -> (967,(0,Ar(Set,Prop)))
      | "cgfo" -> (968,(0,Ar(Set,Prop)))
      | "ceqp" -> (969,(0,Ar(Set,Prop)))
      | "crqp" -> (970,(0,Ar(Set,Prop)))
      | "cqp" -> (971,(0,Ar(Set,Prop)))
      | "cqpOLD" -> (972,(0,Ar(Set,Prop)))
      | "czp" -> (973,(0,Ar(Set,Prop)))
      | "cqpa" -> (974,(0,Ar(Set,Prop)))
      | "ccp" -> (975,(0,Ar(Set,Prop)))
      | "ctrpred" -> (976,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop))))))
      | "cwsuc" -> (977,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop))))))
      | "cwlim" -> (978,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "cfrecs" -> (979,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop))))))
      | "csur" -> (980,(0,Ar(Set,Prop)))
      | "cslt" -> (981,(0,Ar(Set,Prop)))
      | "cbday" -> (982,(0,Ar(Set,Prop)))
      | "csle" -> (983,(0,Ar(Set,Prop)))
      | "csslt" -> (984,(0,Ar(Set,Prop)))
      | "cscut" -> (985,(0,Ar(Set,Prop)))
      | "cmade" -> (986,(0,Ar(Set,Prop)))
      | "cold" -> (987,(0,Ar(Set,Prop)))
      | "cnew" -> (988,(0,Ar(Set,Prop)))
      | "cleft" -> (989,(0,Ar(Set,Prop)))
      | "cright" -> (990,(0,Ar(Set,Prop)))
      | "ctxp" -> (991,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "cpprod" -> (992,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "csset" -> (993,(0,Ar(Set,Prop)))
      | "ctrans" -> (994,(0,Ar(Set,Prop)))
      | "cbigcup" -> (995,(0,Ar(Set,Prop)))
      | "cfix" -> (996,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "climits" -> (997,(0,Ar(Set,Prop)))
      | "cfuns" -> (998,(0,Ar(Set,Prop)))
      | "csingle" -> (999,(0,Ar(Set,Prop)))
      | "csingles" -> (1000,(0,Ar(Set,Prop)))
      | "cimage" -> (1001,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "ccart" -> (1002,(0,Ar(Set,Prop)))
      | "cimg" -> (1003,(0,Ar(Set,Prop)))
      | "cdomain" -> (1004,(0,Ar(Set,Prop)))
      | "crange" -> (1005,(0,Ar(Set,Prop)))
      | "capply" -> (1006,(0,Ar(Set,Prop)))
      | "ccup" -> (1007,(0,Ar(Set,Prop)))
      | "ccap" -> (1008,(0,Ar(Set,Prop)))
      | "csuccf" -> (1009,(0,Ar(Set,Prop)))
      | "cfunpart" -> (1010,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "cfullfn" -> (1011,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "crestrict" -> (1012,(0,Ar(Set,Prop)))
      | "cub" -> (1013,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "clb" -> (1014,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "caltop" -> (1015,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "caltxp" -> (1016,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "cofs" -> (1017,(0,Ar(Set,Prop)))
      | "ctransport" -> (1018,(0,Ar(Set,Prop)))
      | "cifs" -> (1019,(0,Ar(Set,Prop)))
      | "ccgr3" -> (1020,(0,Ar(Set,Prop)))
      | "ccolin" -> (1021,(0,Ar(Set,Prop)))
      | "cfs" -> (1022,(0,Ar(Set,Prop)))
      | "csegle" -> (1023,(0,Ar(Set,Prop)))
      | "coutsideof" -> (1024,(0,Ar(Set,Prop)))
      | "cline2" -> (1025,(0,Ar(Set,Prop)))
      | "cray" -> (1026,(0,Ar(Set,Prop)))
      | "clines2" -> (1027,(0,Ar(Set,Prop)))
      | "cfwddif" -> (1028,(0,Ar(Set,Prop)))
      | "cfwddifn" -> (1029,(0,Ar(Set,Prop)))
      | "chf" -> (1030,(0,Ar(Set,Prop)))
      | "cfne" -> (1031,(0,Ar(Set,Prop)))
      | "w3nand" -> (1032,(0,Ar(Prop,Ar(Prop,Ar(Prop,Prop)))))
      | "cgcdOLD" -> (1033,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "cprvb" -> (1034,(0,Ar(Prop,Prop)))
      | "wssb" -> (1035,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "wrnf" -> (1036,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Ar(Set,Prop)),Prop))))
      | "bj_csngl" -> (1037,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "bj_ctag" -> (1038,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "bj_cproj" -> (1039,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "bj_c1upl" -> (1040,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "bj_cpr1" -> (1041,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "bj_c2uple" -> (1042,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "bj_cpr2" -> (1043,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "celwise" -> (1044,(0,Ar(Set,Prop)))
      | "cmoore" -> (1045,(0,Ar(Set,Prop)))
      | "cmpt3" -> (1046,(0,Ar(Ar(Set,Ar(Set,Ar(Set,Ar(Set,Prop)))),Ar(Ar(Set,Ar(Set,Ar(Set,Ar(Set,Prop)))),Ar(Ar(Set,Ar(Set,Ar(Set,Ar(Set,Prop)))),Ar(Ar(Set,Ar(Set,Ar(Set,Ar(Set,Prop)))),Ar(Set,Prop)))))))
      | "csethom" -> (1047,(0,Ar(Set,Prop)))
      | "ctophom" -> (1048,(0,Ar(Set,Prop)))
      | "cmgmhom" -> (1049,(0,Ar(Set,Prop)))
      | "ctopmgmhom" -> (1050,(0,Ar(Set,Prop)))
      | "ccur_" -> (1051,(0,Ar(Set,Prop)))
      | "cunc_" -> (1052,(0,Ar(Set,Prop)))
      | "cstrset" -> (1053,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop))))))
      | "cdiag2" -> (1054,(0,Ar(Set,Prop)))
      | "cinftyexpi" -> (1055,(0,Ar(Set,Prop)))
      | "cccinfty" -> (1056,(0,Ar(Set,Prop)))
      | "cccbar" -> (1057,(0,Ar(Set,Prop)))
      | "cpinfty" -> (1058,(0,Ar(Set,Prop)))
      | "cminfty" -> (1059,(0,Ar(Set,Prop)))
      | "crrbar" -> (1060,(0,Ar(Set,Prop)))
      | "cinfty" -> (1061,(0,Ar(Set,Prop)))
      | "ccchat" -> (1062,(0,Ar(Set,Prop)))
      | "crrhat" -> (1063,(0,Ar(Set,Prop)))
      | "caddcc" -> (1064,(0,Ar(Set,Prop)))
      | "coppcc" -> (1065,(0,Ar(Set,Prop)))
      | "cprcpal" -> (1066,(0,Ar(Set,Prop)))
      | "carg" -> (1067,(0,Ar(Set,Prop)))
      | "cmulc" -> (1068,(0,Ar(Set,Prop)))
      | "cinvc" -> (1069,(0,Ar(Set,Prop)))
      | "cfinsum" -> (1070,(0,Ar(Set,Prop)))
      | "crrvec" -> (1071,(0,Ar(Set,Prop)))
      | "ctau" -> (1072,(0,Ar(Set,Prop)))
      | "cfinxp" -> (1073,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "wcel_wl" -> (1074,(0,Ar(Ar(Set,Ar(Set,Prop)),Prop)))
      | "wcel2_wl" -> (1075,(0,Ar(Ar(Set,Ar(Set,Prop)),Prop)))
      | "ctotbnd" -> (1076,(0,Ar(Set,Prop)))
      | "cbnd" -> (1077,(0,Ar(Set,Prop)))
      | "cismty" -> (1078,(0,Ar(Set,Prop)))
      | "crrn" -> (1079,(0,Ar(Set,Prop)))
      | "cass" -> (1080,(0,Ar(Set,Prop)))
      | "cexid" -> (1081,(0,Ar(Set,Prop)))
      | "cmagm" -> (1082,(0,Ar(Set,Prop)))
      | "csem" -> (1083,(0,Ar(Set,Prop)))
      | "cmndo" -> (1084,(0,Ar(Set,Prop)))
      | "cghomOLD" -> (1085,(0,Ar(Set,Prop)))
      | "crngo" -> (1086,(0,Ar(Set,Prop)))
      | "cdrng" -> (1087,(0,Ar(Set,Prop)))
      | "crnghom" -> (1088,(0,Ar(Set,Prop)))
      | "crngiso" -> (1089,(0,Ar(Set,Prop)))
      | "crisc" -> (1090,(0,Ar(Set,Prop)))
      | "ccm2" -> (1091,(0,Ar(Set,Prop)))
      | "cfld" -> (1092,(0,Ar(Set,Prop)))
      | "ccring" -> (1093,(0,Ar(Set,Prop)))
      | "cidl" -> (1094,(0,Ar(Set,Prop)))
      | "cpridl" -> (1095,(0,Ar(Set,Prop)))
      | "cmaxidl" -> (1096,(0,Ar(Set,Prop)))
      | "cprrng" -> (1097,(0,Ar(Set,Prop)))
      | "cdmn" -> (1098,(0,Ar(Set,Prop)))
      | "cigen" -> (1099,(0,Ar(Set,Prop)))
      | "cxrn" -> (1100,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "ccoss" -> (1101,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "ccoels" -> (1102,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "crels" -> (1103,(0,Ar(Set,Prop)))
      | "cssr" -> (1104,(0,Ar(Set,Prop)))
      | "crefs" -> (1105,(0,Ar(Set,Prop)))
      | "crefrels" -> (1106,(0,Ar(Set,Prop)))
      | "wrefrel" -> (1107,(0,Ar(Ar(Set,Prop),Prop)))
      | "ccnvrefs" -> (1108,(0,Ar(Set,Prop)))
      | "ccnvrefrels" -> (1109,(0,Ar(Set,Prop)))
      | "wcnvrefrel" -> (1110,(0,Ar(Ar(Set,Prop),Prop)))
      | "csyms" -> (1111,(0,Ar(Set,Prop)))
      | "csymrels" -> (1112,(0,Ar(Set,Prop)))
      | "wsymrel" -> (1113,(0,Ar(Ar(Set,Prop),Prop)))
      | "wprt" -> (1114,(0,Ar(Ar(Set,Prop),Prop)))
      | "clsa" -> (1115,(0,Ar(Set,Prop)))
      | "clsh" -> (1116,(0,Ar(Set,Prop)))
      | "clcv" -> (1117,(0,Ar(Set,Prop)))
      | "clfn" -> (1118,(0,Ar(Set,Prop)))
      | "clk" -> (1119,(0,Ar(Set,Prop)))
      | "cld" -> (1120,(0,Ar(Set,Prop)))
      | "cops" -> (1121,(0,Ar(Set,Prop)))
      | "ccmtN" -> (1122,(0,Ar(Set,Prop)))
      | "col" -> (1123,(0,Ar(Set,Prop)))
      | "coml" -> (1124,(0,Ar(Set,Prop)))
      | "ccvr" -> (1125,(0,Ar(Set,Prop)))
      | "catm" -> (1126,(0,Ar(Set,Prop)))
      | "cal" -> (1127,(0,Ar(Set,Prop)))
      | "clc" -> (1128,(0,Ar(Set,Prop)))
      | "chlt" -> (1129,(0,Ar(Set,Prop)))
      | "clln" -> (1130,(0,Ar(Set,Prop)))
      | "clpl" -> (1131,(0,Ar(Set,Prop)))
      | "clvol" -> (1132,(0,Ar(Set,Prop)))
      | "clines" -> (1133,(0,Ar(Set,Prop)))
      | "cpointsN" -> (1134,(0,Ar(Set,Prop)))
      | "cpsubsp" -> (1135,(0,Ar(Set,Prop)))
      | "cpmap" -> (1136,(0,Ar(Set,Prop)))
      | "cpadd" -> (1137,(0,Ar(Set,Prop)))
      | "cpclN" -> (1138,(0,Ar(Set,Prop)))
      | "cpolN" -> (1139,(0,Ar(Set,Prop)))
      | "cpscN" -> (1140,(0,Ar(Set,Prop)))
      | "clh" -> (1141,(0,Ar(Set,Prop)))
      | "claut" -> (1142,(0,Ar(Set,Prop)))
      | "cwpointsN" -> (1143,(0,Ar(Set,Prop)))
      | "cpautN" -> (1144,(0,Ar(Set,Prop)))
      | "cldil" -> (1145,(0,Ar(Set,Prop)))
      | "cltrn" -> (1146,(0,Ar(Set,Prop)))
      | "cdilN" -> (1147,(0,Ar(Set,Prop)))
      | "ctrnN" -> (1148,(0,Ar(Set,Prop)))
      | "ctrl" -> (1149,(0,Ar(Set,Prop)))
      | "ctgrp" -> (1150,(0,Ar(Set,Prop)))
      | "ctendo" -> (1151,(0,Ar(Set,Prop)))
      | "cedring" -> (1152,(0,Ar(Set,Prop)))
      | "cedring_rN" -> (1153,(0,Ar(Set,Prop)))
      | "cdveca" -> (1154,(0,Ar(Set,Prop)))
      | "cdia" -> (1155,(0,Ar(Set,Prop)))
      | "cdvh" -> (1156,(0,Ar(Set,Prop)))
      | "cocaN" -> (1157,(0,Ar(Set,Prop)))
      | "cdjaN" -> (1158,(0,Ar(Set,Prop)))
      | "cdib" -> (1159,(0,Ar(Set,Prop)))
      | "cdic" -> (1160,(0,Ar(Set,Prop)))
      | "cdih" -> (1161,(0,Ar(Set,Prop)))
      | "coch" -> (1162,(0,Ar(Set,Prop)))
      | "cdjh" -> (1163,(0,Ar(Set,Prop)))
      | "clpoN" -> (1164,(0,Ar(Set,Prop)))
      | "clcd" -> (1165,(0,Ar(Set,Prop)))
      | "cmpd" -> (1166,(0,Ar(Set,Prop)))
      | "chvm" -> (1167,(0,Ar(Set,Prop)))
      | "chdma1" -> (1168,(0,Ar(Set,Prop)))
      | "chdma" -> (1169,(0,Ar(Set,Prop)))
      | "chg" -> (1170,(0,Ar(Set,Prop)))
      | "chlh" -> (1171,(0,Ar(Set,Prop)))
      | "cnacs" -> (1172,(0,Ar(Set,Prop)))
      | "cmzpcl" -> (1173,(0,Ar(Set,Prop)))
      | "cmzp" -> (1174,(0,Ar(Set,Prop)))
      | "cdioph" -> (1175,(0,Ar(Set,Prop)))
      | "csquarenn" -> (1176,(0,Ar(Set,Prop)))
      | "cpell1qr" -> (1177,(0,Ar(Set,Prop)))
      | "cpell1234qr" -> (1178,(0,Ar(Set,Prop)))
      | "cpell14qr" -> (1179,(0,Ar(Set,Prop)))
      | "cpellfund" -> (1180,(0,Ar(Set,Prop)))
      | "crmx" -> (1181,(0,Ar(Set,Prop)))
      | "crmy" -> (1182,(0,Ar(Set,Prop)))
      | "clfig" -> (1183,(0,Ar(Set,Prop)))
      | "clnm" -> (1184,(0,Ar(Set,Prop)))
      | "clnr" -> (1185,(0,Ar(Set,Prop)))
      | "cldgis" -> (1186,(0,Ar(Set,Prop)))
      | "cmnc" -> (1187,(0,Ar(Set,Prop)))
      | "cplylt" -> (1188,(0,Ar(Set,Prop)))
      | "cdgraa" -> (1189,(0,Ar(Set,Prop)))
      | "cmpaa" -> (1190,(0,Ar(Set,Prop)))
      | "citgo" -> (1191,(0,Ar(Set,Prop)))
      | "cza" -> (1192,(0,Ar(Set,Prop)))
      | "cmend" -> (1193,(0,Ar(Set,Prop)))
      | "csdrg" -> (1194,(0,Ar(Set,Prop)))
      | "ccytp" -> (1195,(0,Ar(Set,Prop)))
      | "ctopsep" -> (1196,(0,Ar(Set,Prop)))
      | "ctoplnd" -> (1197,(0,Ar(Set,Prop)))
      | "crcl" -> (1198,(0,Ar(Set,Prop)))
      | "whe" -> (1199,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Prop))))
      | "cbcc" -> (1200,(0,Ar(Set,Prop)))
      | "cplusr" -> (1201,(0,Ar(Set,Prop)))
      | "cminusr" -> (1202,(0,Ar(Set,Prop)))
      | "ctimesr" -> (1203,(0,Ar(Set,Prop)))
      | "cptdfc" -> (1204,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "crr3c" -> (1205,(0,Ar(Set,Prop)))
      | "cline3" -> (1206,(0,Ar(Set,Prop)))
      | "wvd1" -> (1207,(0,Ar(Prop,Ar(Prop,Prop))))
      | "wvd2" -> (1208,(0,Ar(Prop,Ar(Prop,Ar(Prop,Prop)))))
      | "wvhc2" -> (1209,(0,Ar(Prop,Ar(Prop,Prop))))
      | "wvd3" -> (1210,(0,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Prop))))))
      | "wvhc3" -> (1211,(0,Ar(Prop,Ar(Prop,Ar(Prop,Prop)))))
      | "wvhc4" -> (1212,(0,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Prop))))))
      | "wvhc5" -> (1213,(0,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Prop)))))))
      | "wvhc6" -> (1214,(0,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Prop))))))))
      | "wvhc7" -> (1215,(0,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Prop)))))))))
      | "wvhc8" -> (1216,(0,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Prop))))))))))
      | "wvhc9" -> (1217,(0,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Prop)))))))))))
      | "wvhc10" -> (1218,(0,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Prop))))))))))))
      | "wvhc11" -> (1219,(0,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Prop)))))))))))))
      | "wvhc12" -> (1220,(0,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Ar(Prop,Prop))))))))))))))
      | "clsi" -> (1221,(0,Ar(Set,Prop)))
      | "clsxlim" -> (1222,(0,Ar(Set,Prop)))
      | "csalg" -> (1223,(0,Ar(Set,Prop)))
      | "csalon" -> (1224,(0,Ar(Set,Prop)))
      | "csalgen" -> (1225,(0,Ar(Set,Prop)))
      | "csumge0" -> (1226,(0,Ar(Set,Prop)))
      | "cmea" -> (1227,(0,Ar(Set,Prop)))
      | "come" -> (1228,(0,Ar(Set,Prop)))
      | "ccaragen" -> (1229,(0,Ar(Set,Prop)))
      | "covoln" -> (1230,(0,Ar(Set,Prop)))
      | "cvoln" -> (1231,(0,Ar(Set,Prop)))
      | "csmblfn" -> (1232,(0,Ar(Set,Prop)))
      | "wdfat" -> (1233,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Prop))))
      | "cafv" -> (1234,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop)))))
      | "caov" -> (1235,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Ar(Set,Prop))))))
      | "cnelbr" -> (1236,(0,Ar(Set,Prop)))
      | "ciccp" -> (1237,(0,Ar(Set,Prop)))
      | "cpfx" -> (1238,(0,Ar(Set,Prop)))
      | "cfmtno" -> (1239,(0,Ar(Set,Prop)))
      | "ceven" -> (1240,(0,Ar(Set,Prop)))
      | "codd" -> (1241,(0,Ar(Set,Prop)))
      | "cgbe" -> (1242,(0,Ar(Set,Prop)))
      | "cgbow" -> (1243,(0,Ar(Set,Prop)))
      | "cgbo" -> (1244,(0,Ar(Set,Prop)))
      | "cupwlks" -> (1245,(0,Ar(Set,Prop)))
      | "cspr" -> (1246,(0,Ar(Set,Prop)))
      | "cmgmhm" -> (1247,(0,Ar(Set,Prop)))
      | "csubmgm" -> (1248,(0,Ar(Set,Prop)))
      | "ccllaw" -> (1249,(0,Ar(Set,Prop)))
      | "casslaw" -> (1250,(0,Ar(Set,Prop)))
      | "ccomlaw" -> (1251,(0,Ar(Set,Prop)))
      | "cintop" -> (1252,(0,Ar(Set,Prop)))
      | "cclintop" -> (1253,(0,Ar(Set,Prop)))
      | "cassintop" -> (1254,(0,Ar(Set,Prop)))
      | "cmgm2" -> (1255,(0,Ar(Set,Prop)))
      | "ccmgm2" -> (1256,(0,Ar(Set,Prop)))
      | "csgrp2" -> (1257,(0,Ar(Set,Prop)))
      | "ccsgrp2" -> (1258,(0,Ar(Set,Prop)))
      | "crng" -> (1259,(0,Ar(Set,Prop)))
      | "crngh" -> (1260,(0,Ar(Set,Prop)))
      | "crngs" -> (1261,(0,Ar(Set,Prop)))
      | "crngc" -> (1262,(0,Ar(Set,Prop)))
      | "crngcALTV" -> (1263,(0,Ar(Set,Prop)))
      | "cringc" -> (1264,(0,Ar(Set,Prop)))
      | "cringcALTV" -> (1265,(0,Ar(Set,Prop)))
      | "cdmatalt" -> (1266,(0,Ar(Set,Prop)))
      | "cscmatalt" -> (1267,(0,Ar(Set,Prop)))
      | "clinc" -> (1268,(0,Ar(Set,Prop)))
      | "clinco" -> (1269,(0,Ar(Set,Prop)))
      | "clininds" -> (1270,(0,Ar(Set,Prop)))
      | "clindeps" -> (1271,(0,Ar(Set,Prop)))
      | "cfdiv" -> (1272,(0,Ar(Set,Prop)))
      | "cbigo" -> (1273,(0,Ar(Set,Prop)))
      | "cblen" -> (1274,(0,Ar(Set,Prop)))
      | "cdig" -> (1275,(0,Ar(Set,Prop)))
      | "csetrecs" -> (1276,(0,Ar(Ar(Set,Prop),Ar(Set,Prop))))
      | "cpg" -> (1277,(0,Ar(Set,Prop)))
      | "cge_real" -> (1278,(0,Ar(Set,Prop)))
      | "cgt" -> (1279,(0,Ar(Set,Prop)))
      | "csinh" -> (1280,(0,Ar(Set,Prop)))
      | "ccosh" -> (1281,(0,Ar(Set,Prop)))
      | "ctanh" -> (1282,(0,Ar(Set,Prop)))
      | "csec" -> (1283,(0,Ar(Set,Prop)))
      | "ccsc" -> (1284,(0,Ar(Set,Prop)))
      | "ccot" -> (1285,(0,Ar(Set,Prop)))
      | "clog_" -> (1286,(0,Ar(Set,Prop)))
      | "wreflexive" -> (1287,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Prop))))
      | "wirreflexive" -> (1288,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Prop))))
      | "walsi" -> (1289,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Prop))))
      | "walsc" -> (1290,(0,Ar(Ar(Set,Prop),Ar(Ar(Set,Ar(Set,Prop)),Prop))))
      | _ -> raise Not_found
    end
  else
    match x with
(*  | "Eps" -> (0,(1,Ar(Ar(TpVar 0,Prop),TpVar 0))) *)
    | "In" -> if !pfgtheory = HOAS then raise Not_found else (1,(0,Ar(Set,Ar(Set,Prop))))
    | "Empty" -> if !pfgtheory = HF || !pfgtheory = Egal then (2,(0,Set)) else raise Not_found
    | "Union" -> if !pfgtheory = HOAS then raise Not_found else (3,(0,Ar(Set,Set)))
    | "Power" -> if !pfgtheory = HF || !pfgtheory = Egal then (4,(0,Ar(Set,Set))) else raise Not_found
    | "Repl" -> if !pfgtheory = HF || !pfgtheory = Egal then (5,(0,Ar(Set,Ar(Ar(Set,Set),Set)))) else raise Not_found
    | "UnivOf" -> if !pfgtheory = Egal then (6,(0,Ar(Set,Set))) else raise Not_found
    | _ -> raise Not_found

type tm =
  | DB of int
  | TmH of string
  | Prim of int
  | TpAp of tm * tp
  | Ap of tm * tm
  | Lam of tp * tm
  | Imp of tm * tm
  | All of tp * tm

type ptm = int * tm

type pf =
  | Hyp of int
  | Known of string
  | PTpAp of pf * tp
  | PTmAp of pf * tm
  | PPfAp of pf * pf
  | PLam of tm * pf
  | TLam of tp * pf

type ppf = int * pf

type setinfixop = InfMem | InfSubq

type infixop =
  | InfSet of setinfixop
  | InfNam of string

type asckind = AscTp | AscSet | AscSubeq

type atree =
  | Byte of int
  | String of string
  | QString of string
  | Na of string
  | Nu of bool * string * string option * string option
  | Le of string * (asckind * atree) option * atree * atree
  | LeM of string * string list * atree * atree
  | Bi of string * (string list * (asckind * atree) option) list * atree
  | Preo of string * atree
  | Posto of string * atree
  | Info of infixop * atree * atree
  | Implop of atree * atree
  | Sep of string * setinfixop * atree * atree
  | Rep of string * setinfixop * atree * atree
  | SepRep of string * setinfixop * atree * atree * atree
  | SetEnum of atree list
  | MTuple of atree * atree list
  | Tuple of atree * atree * atree list
  | IfThenElse of atree * atree * atree

type ltree =
  | ByteL of int
  | StringL of string
  | QStringL of string
  | NaL of string
  | NuL of bool * string * string option * string option
  | LeL of string * (asckind * ltree) option * ltree * ltree
  | LeML of string * string list * ltree * ltree
  | BiL of string * string * (string list * (asckind * ltree) option) list * ltree
  | PreoL of string * ltree
  | PostoL of string * ltree
  | InfoL of infixop * ltree * ltree
  | ImplopL of ltree * ltree
  | SepL of string * setinfixop * ltree * ltree
  | RepL of string * setinfixop * ltree * ltree
  | SepRepL of string * setinfixop * ltree * ltree * ltree
  | SetEnumL of ltree list
  | MTupleL of ltree * ltree list
  | ParenL of ltree * ltree list
  | IfThenElseL of ltree * ltree * ltree

let rec binderishp (a:ltree) : bool =
  match a with
  | BiL(_) -> true
  | LeL(_) -> true
  | LeML(_) -> true
  | IfThenElseL(_) -> true
  | PreoL(x,a) -> binderishp a
  | InfoL(i,a,b) -> binderishp b
  | _ -> false

let setinfixop_string i =
  match i with
  | InfMem -> ":e"
  | InfSubq -> "c="

let asckind_string i =
  match i with
  | AscTp -> ":"
  | AscSet -> ":e"
  | AscSubeq -> "c="

let rec output_ltree ch a =
  match a with
  | ByteL(x) -> Printf.fprintf ch "\\x%02x" x
  | StringL(x) -> output_char ch '"'; output_string ch x; output_char ch '"'
  | QStringL(x) -> output_char ch '?'; output_string ch x; output_char ch '?'
  | NaL(x) -> output_string ch x
  | NuL(b,x,None,None) ->
      begin
	if b then output_char ch '-';
	output_string ch x;
      end
  | NuL(b,x,Some y,None) ->
      begin
	if b then output_char ch '-';
	output_string ch x;
	output_char ch '.';
	output_string ch y;
      end
  | NuL(b,x,None,Some z) ->
      begin
	if b then output_char ch '-';
	output_string ch x;
	output_char ch 'E';
	output_string ch z;
      end
  | NuL(b,x,Some y,Some z) ->
      begin
	if b then output_char ch '-';
	output_string ch x;
	output_char ch '.';
	output_string ch y;
	output_char ch 'E';
	output_string ch z;
      end
  | LeL(x,None,a,c) ->
      output_string ch "let ";
      output_string ch x;
      output_string ch " := ";
      output_ltree ch a;
      output_string ch " in ";
      output_ltree ch c
  | LeL(x,Some (i,b),a,c) ->
      output_string ch "let ";
      output_string ch x;
      output_char ch ' ';
      output_string ch (asckind_string i);
      output_char ch ' ';
      output_ltree ch b;
      output_string ch " := ";
      output_ltree ch a;
      output_string ch " in ";
      output_ltree ch c
  | LeML(x,xl,a,c) ->
      output_string ch "let [";
      output_string ch x;
      List.iter (fun y -> output_char ch ','; output_string ch y) xl;
      output_string ch "] := ";
      output_ltree ch a;
      output_string ch " in ";
      output_ltree ch c
  | BiL(x,m,[(xl,None)],c) ->
      output_string ch x;
      List.iter (fun y -> output_char ch ' '; output_string ch y) xl;
      output_char ch ' ';
      output_string ch m;
      output_char ch ' ';
      output_ltree ch c
  | BiL(x,m,[(xl,Some(i,b))],c) ->
      output_string ch x;
      List.iter (fun y -> output_char ch ' '; output_string ch y) xl;
      output_char ch ' ';
      output_string ch (asckind_string i);
      output_char ch ' ';
      output_ltree ch b;
      output_char ch ' ';
      output_string ch m;
      output_char ch ' ';
      output_ltree ch c
  | BiL(x,m,vll,c) ->
      output_string ch x;
      List.iter
	(fun vl ->
	  output_string ch " (";
	  let nfst = ref false in
	  begin
	    match vl with
	    | (xl,None) ->
		List.iter (fun y -> if !nfst then output_char ch ' '; nfst := true; output_string ch y) xl;
	    | (xl,Some(AscTp,b)) ->
		List.iter (fun y -> if !nfst then output_char ch ' '; nfst := true; output_string ch y) xl;
		output_string ch " : ";
		output_ltree ch b
	    | (xl,Some(AscSet,b)) ->
		List.iter (fun y -> if !nfst then output_char ch ' '; nfst := true; output_string ch y) xl;
		output_string ch " :e ";
		output_ltree ch b
	    | (xl,Some(AscSubeq,b)) ->
		List.iter (fun y -> if !nfst then output_char ch ' '; nfst := true; output_string ch y) xl;
		output_string ch " c= ";
		output_ltree ch b
	  end;
	  output_char ch ')';
	  )
	vll;
      output_char ch ' ';
      output_string ch m;
      output_char ch ' ';
      output_ltree ch c
  | PreoL(x,a) ->
      output_string ch x;
      output_char ch ' ';
      output_ltree ch a
  | PostoL(x,a) ->
      output_ltree ch a;
      output_char ch ' ';
      output_string ch x
  | InfoL(InfSet i,a,b) ->
      output_ltree ch a;
      output_char ch ' ';
      output_string ch (setinfixop_string i);
      output_char ch ' ';
      output_ltree ch b
  | InfoL(InfNam x,a,b) ->
      output_ltree ch a;
      output_char ch ' ';
      output_string ch x;
      output_char ch ' ';
      output_ltree ch b
  | ImplopL(a,b) ->
      output_ltree ch a;
      output_char ch ' ';
      output_ltree ch b
  | SepL(x,i,a,b) ->
      output_char ch '{';
      output_string ch x;
      output_char ch ' ';
      output_string ch (setinfixop_string i);
      output_char ch ' ';
      output_ltree ch a;
      output_char ch '|';
      output_ltree ch b;
      output_char ch '}';
  | RepL(x,i,a,b) ->
      output_char ch '{';
      output_ltree ch a;
      output_char ch '|';
      output_string ch x;
      output_char ch ' ';
      output_string ch (setinfixop_string i);
      output_char ch ' ';
      output_ltree ch b;
      output_char ch '}';
  | SepRepL(x,i,a,b,c) ->
      output_char ch '{';
      output_ltree ch a;
      output_char ch '|';
      output_string ch x;
      output_char ch ' ';
      output_string ch (setinfixop_string i);
      output_char ch ' ';
      output_ltree ch b;
      output_char ch ',';
      output_ltree ch c;
      output_char ch '}';
  | SetEnumL(al) ->
      begin
	output_char ch '{';
	match al with
	| [] -> output_char ch '}';
	| (a::bl) ->
	    output_ltree ch a;
	    List.iter (fun b -> output_char ch ','; output_ltree ch b) bl;
	    output_char ch '}';
      end
  | MTupleL(a,bl) ->
      output_char ch '[';
      output_ltree ch a;
      List.iter (fun b -> output_char ch ','; output_ltree ch b) bl;
      output_char ch ']';
  | ParenL(a,bl) ->
      output_char ch '(';
      output_ltree ch a;
      List.iter (fun b -> output_char ch ','; output_ltree ch b) bl;
      output_char ch ')';
  | IfThenElseL(a,b,c) ->
      output_string ch "if ";
      output_ltree ch a;
      output_string ch " then ";
      output_ltree ch b;
      output_string ch " else ";
      output_ltree ch c

let rec ltree_to_atree a =
  match a with
  | ByteL(x) -> Byte(x)
  | StringL(x) -> String(x)
  | QStringL(x) -> QString(x)
  | NaL(x) -> Na(x)
  | NuL(b,x,y,z) -> Nu(b,x,y,z)
  | LeL(x,None,a,c) -> Le(x,None,ltree_to_atree a,ltree_to_atree c)
  | LeL(x,Some(i,b),a,c) -> Le(x,Some(i,ltree_to_atree b),ltree_to_atree a,ltree_to_atree c)
  | LeML(x,xl,a,c) -> LeM(x,xl,ltree_to_atree a,ltree_to_atree c)
  | BiL(x,m,vll,c) ->
      let vlla = List.map
	  (fun (xl,o) ->
	    match o with
	    | None -> (xl,None)
	    | Some(i,b) -> (xl,Some(i,ltree_to_atree b)))
	  vll
      in
      Bi(x,vlla,ltree_to_atree c)
  | PreoL(x,a) -> Preo(x,ltree_to_atree a)
  | PostoL(x,a) -> Posto(x,ltree_to_atree a)
  | InfoL(x,a,b) -> Info(x,ltree_to_atree a,ltree_to_atree b)
  | ImplopL(a,b) -> Implop(ltree_to_atree a,ltree_to_atree b)
  | SepL(x,i,a,b) -> Sep(x,i,ltree_to_atree a,ltree_to_atree b)
  | RepL(x,i,a,b) -> Rep(x,i,ltree_to_atree a,ltree_to_atree b)
  | SepRepL(x,i,a,b,c) -> SepRep(x,i,ltree_to_atree a,ltree_to_atree b,ltree_to_atree c)
  | SetEnumL(al) -> SetEnum(List.map ltree_to_atree al)
  | MTupleL(a,bl) -> MTuple(ltree_to_atree a,List.map ltree_to_atree bl)
  | ParenL(a,[]) -> ltree_to_atree a
  | ParenL(a,b::cl) -> Tuple(ltree_to_atree a,ltree_to_atree b,List.map ltree_to_atree cl)
  | IfThenElseL(a,b,c) -> IfThenElse(ltree_to_atree a,ltree_to_atree b,ltree_to_atree c)

type picase = Postfix | InfixNone | InfixLeft | InfixRight

type docitem =
  | Author of string * string list
  | Title of string
  | Salt of string
  | Opaque of string list
  | Transparent of string list
  | Treasure of string
  | ShowProofTerms of bool
  | Section of string
  | End of string
  | VarDecl of string list * asckind * ltree
  | LetDecl of string * (asckind * ltree) option * ltree
  | HypDecl of string * ltree
  | PostInfixDecl of string * ltree * int * picase
  | PrefixDecl of string * ltree * int
  | BinderDecl of bool * bool * string * ltree * ltree option
  | NotationDecl of string * string list
  | UnicodeDecl of string * string list
  | SubscriptDecl of string
  | SuperscriptDecl of string
  | ParamDecl of string * ltree
  | DefDecl of string * ltree option * ltree
  | ParamHash of string * string * string option
  | AxDecl of string * ltree
  | ThmDecl of string * string * ltree

type pftacitem =
  | PfStruct of int
  | Exact of ltree
  | LetTac of string list * ltree option
  | AssumeTac of string list * ltree option
  | SetTac of string * ltree option * ltree
  | ApplyTac of ltree
  | ClaimTac of string * ltree
  | ProveTac of ltree * ltree list
  | CasesTac of ltree * (string * ltree) list list
  | WitnessTac of ltree
  | RewriteTac of bool * ltree * int list
  | SpecialTac of string * ltree list
  | Qed
  | Admitted
  | Admit
  | Aby of string list

type docorpftacitem =
  | DocItem : docitem -> docorpftacitem
  | PfTacItem : pftacitem -> docorpftacitem

type doc = (string * string) list * docorpftacitem list

(*** DocPromise(hashofdocyettobepublished,[...listofhashesofpropositionsprovenindocyettobepublished...]) ***)
type formalmetablockitem =
  | Doc of doc
  | DocPromise of string * string list

type formalmetablock = formalmetablockitem list

let rec tp_to_str m =
  match m with
  | TpVar(i) -> "?" ^ string_of_int i
  | Prop -> "prop"
  | Set -> "set"
  | Ar(m1,m2) -> "(" ^ tp_to_str m1 ^ " -> " ^ tp_to_str m2 ^ ")"

let rec tm_to_str m =
  match m with
  | DB(i) -> "_" ^ string_of_int i
  | TmH(h) ->
     begin
       try
         Hashtbl.find tmh_legend h
       with Not_found -> "#" ^ h
     end
  | Prim(i) ->
     begin
       try
         Hashtbl.find prim_legend i
       with Not_found -> "\"" ^ string_of_int i ^ "\""
     end
  | TpAp(m1,m2) -> "(" ^ tm_to_str m1 ^ " " ^ tp_to_str m2 ^ ")"
  | Ap(m1,m2) -> "(" ^ tm_to_str m1 ^ " " ^ tm_to_str m2 ^ ")"
  | Lam(m1,m2) -> "(fun _:" ^ tp_to_str m1 ^ " => " ^ tm_to_str m2 ^ ")"
  | Imp(m1,m2) -> "(" ^ tm_to_str m1 ^ " -> " ^ tm_to_str m2 ^ ")"
  | All(m1,m2) -> "(forall _:" ^ tp_to_str m1 ^ ", " ^ tm_to_str m2 ^ ")"

let rec pf_to_str m =
  match m with
  | Hyp(i) -> "__" ^ string_of_int i
  | Known(h) ->
     begin
       try
         Hashtbl.find knownh_legend h
       with Not_found -> "##" ^ h
     end
  | PTpAp(m1,m2) -> "(" ^ pf_to_str m1 ^ " " ^ tp_to_str m2 ^ ")"
  | PTmAp(m1,m2) -> "(" ^ pf_to_str m1 ^ " " ^ tm_to_str m2 ^ ")"
  | PPfAp(m1,m2) -> "(" ^ pf_to_str m1 ^ " " ^ pf_to_str m2 ^ ")"
  | PLam(m1,m2) -> "(fun _:" ^ tm_to_str m1 ^ " => " ^ pf_to_str m2 ^ ")"
  | TLam(m1,m2) -> "(fun _:" ^ tp_to_str m1 ^ " => " ^ pf_to_str m2 ^ ")"

let rec tp_to_sexpr m =
  match m with
  | TpVar(i) -> "(TPVAR " ^ string_of_int i ^ ")"
  | Prop -> "(PROP)"
  | Set -> "(SET)"
  | Ar(m1,m2) -> "(AR " ^ tp_to_sexpr m1 ^ " " ^ tp_to_sexpr m2 ^ ")"

let rec tm_to_sexpr m =
  match m with
  | DB(i) -> "(DB " ^ string_of_int i ^ ")"
  | TmH(h) -> "(TMH \"" ^ h ^ "\")"
  | Prim(i) -> Printf.sprintf "(PRIM %d)" i
  | TpAp(m1,m2) -> "(TPAP " ^ tm_to_sexpr m1 ^ " " ^ tp_to_sexpr m2 ^ ")"
  | Ap(m1,m2) -> "(AP " ^ tm_to_sexpr m1 ^ " " ^ tm_to_sexpr m2 ^ ")"
  | Lam(m1,m2) -> "(LAM " ^ tp_to_sexpr m1 ^ " " ^ tm_to_sexpr m2 ^ ")"
  | Imp(m1,m2) -> "(IMP " ^ tm_to_sexpr m1 ^ " " ^ tm_to_sexpr m2 ^ ")"
  | All(m1,m2) -> "(ALL " ^ tp_to_sexpr m1 ^ " " ^ tm_to_sexpr m2 ^ ")"

let rec pf_to_sexpr m =
  match m with
  | Hyp(i) -> "(HYP " ^ string_of_int i ^ ")"
  | Known(h) -> "(KNOWN \"" ^ h ^ "\")"
  | PTpAp(m1,m2) -> "(PTPAP " ^ pf_to_sexpr m1 ^ " " ^ tp_to_sexpr m2 ^ ")"
  | PTmAp(m1,m2) -> "(PTMAP " ^ pf_to_sexpr m1 ^ " " ^ tm_to_sexpr m2 ^ ")"
  | PPfAp(m1,m2) -> "(PPFAP " ^ pf_to_sexpr m1 ^ " " ^ pf_to_sexpr m2 ^ ")"
  | PLam(m1,m2) -> "(PLAM " ^ tm_to_sexpr m1 ^ " " ^ pf_to_sexpr m2 ^ ")"
  | TLam(m1,m2) -> "(TLAM " ^ tp_to_sexpr m1 ^ " " ^ pf_to_sexpr m2 ^ ")"

(*** serialization code ***)
let hex_char h =
  List.nth ['0';'1';'2';'3';'4';'5';'6';'7';'8';'9';'A';'B';'C';'D';'E';'F'] h

(*** position function ***)
let rec position_rec l x i =
match l with
| (y::r) when x = y -> i
| (y::r) -> position_rec r x (i+1)
| [] -> raise Not_found

let position l x = position_rec l x 0

let tplookup ctxtp x =
  TpVar (position ctxtp x)

exception NegDB

let rec tmshift i j m =
  match m with
  | DB(k) when k < i -> DB(k)
  | DB(k) ->
      let l = k + j in
      if l >= i then DB(l) else raise NegDB
  | TpAp(m1,a) -> TpAp(tmshift i j m1,a)
  | Ap(m1,m2) -> Ap(tmshift i j m1,tmshift i j m2)
  | Lam(a1,m1) -> Lam(a1,tmshift (i+1) j m1)
  | Imp(m1,m2) -> Imp(tmshift i j m1,tmshift i j m2)
  | All(a1,m1) -> All(a1,tmshift (i+1) j m1)
  | _ -> m

let rec tmtplookup_rec ctxtm x i =
  match ctxtm with
  | ((y,(a,None))::_) when y = x -> (DB i,a)
  | ((y,(a,Some(m)))::_) when y = x && i = 0 -> (m,a)
  | ((y,(a,Some(m)))::_) when y = x -> (tmshift 0 i m,a)
  | ((_,(_,None))::r) -> tmtplookup_rec r x (i+1) (*** Shift for variables ***)
  | ((_,(_,Some(_)))::r) -> tmtplookup_rec r x i (*** Do not shift for lets ***)
  | [] -> raise Not_found

let tmtplookup ctxtm x =
  tmtplookup_rec ctxtm x 0

let tmlookup ctxtm x =
  let (n,_) = tmtplookup_rec ctxtm x 0 in n

let rec pfshift i j d =
  match d with
  | Hyp(k) when k < i -> Hyp(k)
  | Hyp(k) -> let l = k+j in if l >= i then Hyp(k+j) else raise NegDB
  | PTpAp(d1,a) -> PTpAp(pfshift i j d1,a)
  | PTmAp(d1,m2) -> PTmAp(pfshift i j d1,m2)
  | PPfAp(d1,d2) -> PPfAp(pfshift i j d1,pfshift i j d2)
  | PLam(m1,d1) -> PLam(m1,pfshift (i+1) j d1)
  | TLam(a1,d1) -> TLam(a1,pfshift i j d1)
  | _ -> d

let rec pftmshift i j d =
  match d with
  | Hyp(k) -> Hyp(k)
  | PTpAp(d1,a) -> PTpAp(pftmshift i j d1,a)
  | PTmAp(d1,m2) -> PTmAp(pftmshift i j d1,tmshift i j m2)
  | PPfAp(d1,d2) -> PPfAp(pftmshift i j d1,pftmshift i j d2)
  | PLam(m1,d1) -> PLam(tmshift i j m1,pftmshift i j d1)
  | TLam(a1,d1) -> TLam(a1,pftmshift (i+1) j d1)
  | _ -> d

let rec pflookup_rec ctxpf x i =
  match ctxpf with
  | ((y,m)::_) when y = x -> Hyp i
  | (_::r) -> pflookup_rec r x (i+1)
  | [] -> raise Not_found

let pflookup ctxpf x = pflookup_rec ctxpf x 0

let rec pfproplookup_rec ctxpf x i =
  match ctxpf with
  | ((y,m)::_) when y = x -> (Hyp i,m)
  | (_::r) -> pfproplookup_rec r x (i+1)
  | [] -> raise Not_found

let pfproplookup ctxpf x = pfproplookup_rec ctxpf x 0

let rec tp_closed_p a =
  match a with
  | Ar(a1,a2) -> tp_closed_p a1 && tp_closed_p a2
  | TpVar _ -> false
  | _ -> true

let rec tpsubst a cl =
  match a with
  | TpVar i -> List.nth cl i
  | Set -> Set
  | Prop -> Prop
  | Ar(a,b) -> Ar(tpsubst a cl,tpsubst b cl)

let rec tmtpsubst m cl =
  match m with
  | TpAp(m1,a1) -> TpAp(tmtpsubst m1 cl,tpsubst a1 cl)
  | Ap(m1,m2) -> Ap(tmtpsubst m1 cl,tmtpsubst m2 cl)
  | Lam(a1,m1) -> Lam(tpsubst a1 cl,tmtpsubst m1 cl)
  | Imp(m1,m2) -> Imp(tmtpsubst m1 cl,tmtpsubst m2 cl)
  | All(a1,m1) -> All(tpsubst a1 cl,tmtpsubst m1 cl)
  | _ -> m

let rec pftpsubst d cl =
  match d with
  | PTpAp(d1,a1) -> PTpAp(pftpsubst d1 cl,tpsubst a1 cl)
  | PTmAp(d1,m1) -> PTmAp(pftpsubst d1 cl,tmtpsubst m1 cl)
  | PPfAp(d1,d2) -> PPfAp(pftpsubst d1 cl,pftpsubst d2 cl)
  | PLam(m1,d1) -> PLam(tmtpsubst m1 cl,pftpsubst d1 cl)
  | TLam(a1,d1) -> TLam(tpsubst a1 cl,pftpsubst d1 cl)
  | _ -> d

let rec tmsubst m j n =
  match m with
  | DB(i) when i = j && j = 0 -> n
  | DB(i) when i = j -> tmshift 0 j n
  | DB(i) when i > j -> DB(i-1)
  | TpAp(m1,a) -> TpAp(tmsubst m1 j n,a) (*** This could be omitted since it should always be TmH applied to <= 3 type variables, and so will contain no de Bruijns. ***)
  | Ap(m1,m2) -> Ap(tmsubst m1 j n,tmsubst m2 j n)
  | Lam(a,m1) -> Lam(a,tmsubst m1 (j+1) n)
  | Imp(m1,m2) -> Imp(tmsubst m1 j n,tmsubst m2 j n)
  | All(a,m1) -> All(a,tmsubst m1 (j+1) n)
  | _ -> m

let rec free_in_tm_p m j =
  match m with
  | DB(i) when i = j -> true
  | Ap(m1,m2) -> free_in_tm_p m1 j || free_in_tm_p m2 j
  | Lam(a,m1) -> free_in_tm_p m1 (j+1)
  | Imp(m1,m2) -> free_in_tm_p m1 j || free_in_tm_p m2 j
  | All(a,m1) -> free_in_tm_p m1 (j+1)
  | TpAp(m1,a) -> false (*** invariant: m1 is closed ***)
  | _ -> false

let rec free_in_pf_p d j =
  match d with
  | PTpAp(d1,_) -> free_in_pf_p d1 j
  | PTmAp(d1,m2) -> free_in_pf_p d1 j || free_in_tm_p m2 j
  | PPfAp(d1,d2) -> free_in_pf_p d1 j || free_in_pf_p d2 j
  | PLam(m1,d2) -> free_in_tm_p m1 j || free_in_pf_p d2 j
  | TLam(a1,d2) -> free_in_pf_p d2 (j+1)
  | _ -> false

let rec hyp_in_pf_p d j =
  match d with
  | Hyp(i) -> i = j
  | PTpAp(d1,_) -> hyp_in_pf_p d1 j
  | PTmAp(d1,m2) -> hyp_in_pf_p d1 j
  | PPfAp(d1,d2) -> hyp_in_pf_p d1 j || hyp_in_pf_p d2 j
  | PLam(m1,d2) -> hyp_in_pf_p d2 (j+1)
  | TLam(a1,d2) -> hyp_in_pf_p d2 j
  | _ -> false

let beta_count = ref None

let beta_count_check () =
  match !beta_count with
  | None -> ()
  | Some b when b > 0 ->
      beta_count := Some (b-1)
  | _ ->
     raise (Failure("Resource Bound Reached -- Too many beta reductions"))

let beta_report () =
  match !beta_count with
  | Some(b) ->
     Printf.printf "beta_count remaining: %d\n" b;
     Printf.printf "betas used: %d\n" (150000000 - b)
  | None -> ()

let rec tm_beta_eta_norm_1 m =
  match m with
  | Ap(m1,m2) ->
      let (m1r,m1b) = tm_beta_eta_norm_1 m1 in
      let (m2r,m2b) = tm_beta_eta_norm_1 m2 in
      begin
	match m1r with
	| Lam(a,m) ->
	    beta_count_check ();
	    (tmsubst m 0 m2r,false) (*** beta ***)
	| _ -> (Ap(m1r,m2r),m1b && m2b)
      end
  | Lam(a,m1) ->
      let (m1r,m1b) = tm_beta_eta_norm_1 m1 in
      begin
	match m1r with
	| Ap(m1f,DB(0)) when not (free_in_tm_p m1f 0) -> (tmshift 0 (-1) m1f,false) (*** eta ***)
	| _ -> (Lam(a,m1r),m1b)
      end
  | Imp(m1,m2) ->
      let (m1r,m1b) = tm_beta_eta_norm_1 m1 in
      let (m2r,m2b) = tm_beta_eta_norm_1 m2 in
      (Imp(m1r,m2r),m1b && m2b)
  | All(a,m1) ->
      let (m1r,m1b) = tm_beta_eta_norm_1 m1 in
      (All(a,m1r),m1b)
  | TpAp(m1,a1) -> (m,true) (*** invariant: polydefs are gone, so m1 is either Prim(0) or TmH(h) where h is the id of Prim(0). No reduction here. ***)
  | _ -> (m,true)

let rec tm_beta_eta_norm m =
  let (mr,mb) = tm_beta_eta_norm_1 m in
  if mb then
    mr
  else
    tm_beta_eta_norm mr

let rec tm_beta_eta_exeq_norm_1 m =
  match m with
  | Ap(m1,m2) ->
      let (m1r,m1b) = tm_beta_eta_exeq_norm_1 m1 in
      let (m2r,m2b) = tm_beta_eta_exeq_norm_1 m2 in
      begin
	match m1r with
	| Lam(a,m) ->
	    beta_count_check ();
	    (tmsubst m 0 m2r,false) (*** beta ***)
	| _ -> (Ap(m1r,m2r),m1b && m2b)
      end
  | Lam(a,m1) ->
      let (m1r,m1b) = tm_beta_eta_exeq_norm_1 m1 in
      begin
	match m1r with
	| Ap(m1f,DB(0)) when not (free_in_tm_p m1f 0) -> (tmshift 0 (-1) m1f,false) (*** eta ***)
	| _ -> (Lam(a,m1r),m1b)
      end
  | Imp(m1,m2) ->
      let (m1r,m1b) = tm_beta_eta_exeq_norm_1 m1 in
      let (m2r,m2b) = tm_beta_eta_exeq_norm_1 m2 in
      (Imp(m1r,m2r),m1b && m2b)
  | All(a,m1) ->
      let (m1r,m1b) = tm_beta_eta_exeq_norm_1 m1 in
      (All(a,m1r),m1b)
  | TpAp(TmH(h),a) when h = "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099" -> (** ex **)
     (Lam(Ar(a,Prop),All(Prop,Imp(All(a,Imp(Ap(DB(2),DB(0)),DB(1))),DB(0)))),false)
  | TpAp(TmH(h),a) when h = "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a" -> (** eq **)
     (Lam(a,Lam(a,All(Ar(a,Ar(a,Prop)),Imp(Ap(Ap(DB(0),DB(2)),DB(1)),Ap(Ap(DB(0),DB(1)),DB(2)))))),false)
  | TpAp(TmH(h),a) when h = "7966a66a9bb198103c2a540ccd5ebebdff33c10843cc10eebfc98715e142989c" -> (** neq **)
     if !pfgtheory = HF then
       (Lam(a,Lam(a,Ap(TmH("058f630dd89cad5a22daa56e097e3bdf85ce16ebd3dbf7994e404e2a98800f7f"),All(Ar(a,Ar(a,Prop)),Imp(Ap(Ap(DB(0),DB(2)),DB(1)),Ap(Ap(DB(0),DB(1)),DB(2))))))),false)
     else
       (Lam(a,Lam(a,Imp(All(Ar(a,Ar(a,Prop)),Imp(Ap(Ap(DB(0),DB(2)),DB(1)),Ap(Ap(DB(0),DB(1)),DB(2)))),All(Prop,DB(0))))),false)
  | TpAp(m1,a1) -> (m,true) (*** invariant: polydefs are gone, so m1 is either Prim(0) or TmH(h) where h is the id of Prim(0). No reduction here. ***)
  | _ -> (m,true)

let rec tm_beta_eta_exeq_norm m =
  let (mr,mb) = tm_beta_eta_exeq_norm_1 m in
  if mb then
    mr
  else
    tm_beta_eta_exeq_norm mr

let tpofprim i =
  match i with
  | 0 -> Ar(Ar(TpVar 0,Prop),TpVar 0)
  | 1 -> Ar(Set,Ar(Set,Prop))
  | 2 -> Set
  | 3 -> Ar(Set,Set)
  | 4 -> Ar(Set,Set)
  | 5 -> Ar(Set,Ar(Ar(Set,Set),Set))
  | 6 -> Ar(Set,Set)
  | _ -> raise Not_found

let rec extr_tpoftm sgtmof cxtm m =
  match m with
  | DB i -> List.nth cxtm i
  | TpAp(Prim 0,a) -> Ar(Ar(a,Prop),a)
  | TpAp(TpAp(TpAp(TpAp(TpAp(TpAp(TmH h,a1),a2),a3),a4),a5),a6) ->
      begin
	match Hashtbl.find sgtmof h with
	| (6,d) -> tpsubst d [a1;a2;a3;a4;a5;a6]
	| (i,_) -> raise (Failure(h ^ " applied to 6 types, but expected to be applied to " ^ (string_of_int i)))
      end
  | TpAp(TpAp(TpAp(TpAp(TpAp(TmH h,a1),a2),a3),a4),a5) ->
      begin
	match Hashtbl.find sgtmof h with
	| (5,d) -> tpsubst d [a1;a2;a3;a4;a5]
	| (i,_) -> raise (Failure(h ^ " applied to 5 types, but expected to be applied to " ^ (string_of_int i)))
      end
  | TpAp(TpAp(TpAp(TpAp(TmH h,a1),a2),a3),a4) ->
      begin
	match Hashtbl.find sgtmof h with
	| (4,d) -> tpsubst d [a1;a2;a3;a4]
	| (i,_) -> raise (Failure(h ^ " applied to 4 types, but expected to be applied to " ^ (string_of_int i)))
      end
  | TpAp(TpAp(TpAp(TmH h,a),b),c) ->
      begin
	match Hashtbl.find sgtmof h with
	| (3,d) -> tpsubst d [a;b;c]
	| (i,_) -> raise (Failure(h ^ " applied to 3 types, but expected to be applied to " ^ (string_of_int i)))
      end
  | TpAp(TpAp(TmH h,a),b) ->
      begin
	match Hashtbl.find sgtmof h with
	| (2,d) -> tpsubst d [a;b]
	| (i,_) -> raise (Failure(h ^ " applied to 2 types, but expected to be applied to " ^ (string_of_int i)))
      end
  | TpAp(TmH h,a) ->
      begin
	match Hashtbl.find sgtmof h with
	| (1,d) -> tpsubst d [a]
	| (i,_) -> raise (Failure(h ^ " applied to 1 type, but expected to be applied to " ^ (string_of_int i)))
      end
  | TmH h ->
      begin
	match Hashtbl.find sgtmof h with
	| (0,d) -> d
	| (i,_) -> raise (Failure(h ^ " applied to no types, but expected to be applied to " ^ (string_of_int i)))
      end
  | Prim 0 -> raise (Failure("The polymorphic primitive Eps applied to no types, but expected to be applied to 1"))
  | Prim i -> tpofprim i
  | TpAp(_,_) -> raise (Failure("Nonprefix polymorphism in term"))
  | Ap(m1,m2) ->
      begin
	match extr_tpoftm sgtmof cxtm m1 with
	| Ar(a,b) -> (check_tpoftm sgtmof cxtm m2 a; b)
	| _ -> raise (Failure("Type Error: Nonfunction applied to an argument."))
      end
  | Lam(a,m) -> Ar(a,extr_tpoftm sgtmof (a::cxtm) m)
  | Imp(m1,m2) -> (check_tpoftm sgtmof cxtm m1 Prop; check_tpoftm sgtmof cxtm m2 Prop; Prop)
  | All(a,m) -> (check_tpoftm sgtmof (a::cxtm) m Prop; Prop)
and check_tpoftm sgtmof cxtm m a =
  let b = extr_tpoftm sgtmof cxtm m in
  if a = b then
    ()
  else
    raise (Failure("Type Error: Found " ^ tp_to_str b ^ "\nbut expected " ^ tp_to_str a))

let rec tm_head_args_r m args =
  match m with
  | Ap(m1,m2) -> tm_head_args_r m1 (m2::args)
  | _ -> (m,args)

let tm_head_args m =
  tm_head_args_r m []

(*** assume m is beta eta normal and not a Lam, and args are all beta eta normal ***)
let rec tm_app_beta_eta_norm2 m args =
  match args with
  | (n::argr) -> tm_app_beta_eta_norm2 (Ap(m,n)) argr
  | _ -> m

(*** assume m is beta eta normal already and args are all beta eta normal ***)
let rec tm_app_beta_eta_norm m args =
  match (m,args) with
  | (Lam(_,m1),n::argr) ->
      tm_app_beta_eta_norm (tm_beta_eta_norm (tmsubst m1 0 n)) argr
  | _ ->
      tm_app_beta_eta_norm2 m args

let defp sdel h =
  match h with
  | TmH(c) -> Hashtbl.mem sdel c
  | TpAp(TmH(c),_) -> Hashtbl.mem sdel c
  | TpAp(TpAp(TmH(c),_),_) -> Hashtbl.mem sdel c
  | TpAp(TpAp(TpAp(TmH(c),_),_),_) -> Hashtbl.mem sdel c
  | TpAp(TpAp(TpAp(TpAp(TmH(c),_),_),_),_) -> Hashtbl.mem sdel c
  | TpAp(TpAp(TpAp(TpAp(TpAp(TmH(c),_),_),_),_),_) -> Hashtbl.mem sdel c
  | TpAp(TpAp(TpAp(TpAp(TpAp(TpAp(TmH(c),_),_),_),_),_),_) -> Hashtbl.mem sdel c
  | _ -> false

let deltap dl h =
  match h with
  | TmH(c) -> List.mem c dl
  | TpAp(TmH(c),_) -> true
  | TpAp(TpAp(TmH(c),_),_) -> true
  | TpAp(TpAp(TpAp(TmH(c),_),_),_) -> true
  | TpAp(TpAp(TpAp(TpAp(TmH(c),_),_),_),_) -> true
  | TpAp(TpAp(TpAp(TpAp(TpAp(TmH(c),_),_),_),_),_) -> true
  | TpAp(TpAp(TpAp(TpAp(TpAp(TpAp(TmH(c),_),_),_),_),_),_) -> true
  | _ -> false

(*** assume all defs are beta eta normal ***)
let delta_exp sdel h args =
  try
    match h with
    | TmH(c) ->
	begin
	  let (i,m) = Hashtbl.find sdel c in
	  if i = 0 then
	    tm_app_beta_eta_norm m args
	  else if i = 1 then
	    raise (Failure(c ^ " should be applied to 1 type, but is applied to none."))
	  else
	    raise (Failure(c ^ " should be applied to " ^ (string_of_int i) ^ " types, but is applied to none."))
	end
    | TpAp(TmH(c),a1) ->
	begin
	  let (i,m) = Hashtbl.find sdel c in
	  if i = 1 then
	    tm_app_beta_eta_norm (tmtpsubst m [a1]) args
	  else
	    raise (Failure(c ^ " should be applied to " ^ (string_of_int i) ^ " types, but is applied to 1."))
	end
    | TpAp(TpAp(TmH(c),a1),a2) ->
	begin
	  let (i,m) = Hashtbl.find sdel c in
	  if i = 2 then
	    tm_app_beta_eta_norm (tmtpsubst m [a1;a2]) args
	  else if i = 1 then
	    raise (Failure(c ^ " should be applied to 1 type, but is applied to 2."))
	  else
	    raise (Failure(c ^ " should be applied to " ^ (string_of_int i) ^ " types, but is applied to 2."))
	end
    | TpAp(TpAp(TpAp(TmH(c),a1),a2),a3) ->
	begin
	  let (i,m) = Hashtbl.find sdel c in
	  if i = 3 then
	    tm_app_beta_eta_norm (tmtpsubst m [a1;a2;a3]) args
	  else if i = 1 then
	    raise (Failure(c ^ " should be applied to 1 type, but is applied to 3."))
	  else
	    raise (Failure(c ^ " should be applied to " ^ (string_of_int i) ^ " types, but is applied to 3."))
	end
    | TpAp(TpAp(TpAp(TpAp(TmH(c),a1),a2),a3),a4) ->
	begin
	  let (i,m) = Hashtbl.find sdel c in
	  if i = 4 then
	    tm_app_beta_eta_norm (tmtpsubst m [a1;a2;a3;a4]) args
	  else if i = 1 then
	    raise (Failure(c ^ " should be applied to 1 type, but is applied to 4."))
	  else
	    raise (Failure(c ^ " should be applied to " ^ (string_of_int i) ^ " types, but is applied to 4."))
	end
    | TpAp(TpAp(TpAp(TpAp(TpAp(TmH(c),a1),a2),a3),a4),a5) ->
	begin
	  let (i,m) = Hashtbl.find sdel c in
	  if i = 5 then
	    tm_app_beta_eta_norm (tmtpsubst m [a1;a2;a3;a4;a5]) args
	  else if i = 1 then
	    raise (Failure(c ^ " should be applied to 1 type, but is applied to 5."))
	  else
	    raise (Failure(c ^ " should be applied to " ^ (string_of_int i) ^ " types, but is applied to 5."))
	end
    | TpAp(TpAp(TpAp(TpAp(TpAp(TpAp(TmH(c),a1),a2),a3),a4),a5),a6) ->
	begin
	  let (i,m) = Hashtbl.find sdel c in
	  if i = 5 then
	    tm_app_beta_eta_norm (tmtpsubst m [a1;a2;a3;a4;a5;a6]) args
	  else if i = 1 then
	    raise (Failure(c ^ " should be applied to 1 type, but is applied to 6."))
	  else
	    raise (Failure(c ^ " should be applied to " ^ (string_of_int i) ^ " types, but is applied to 6."))
	end
    | _ -> raise Not_found
  with Not_found ->
    (*** By checking with defp above before delta_exp is called, I should know that this doesn't happen. **)
    raise (Failure("delta_exp called with an inappropriate head. Bug"))

let delta_cons h dl =
  match h with
  | TmH(c) -> if List.mem c dl then dl else (c::dl)
  | _ -> dl

let rec headnorm1 m sdel dl =
  match m with
  | Lam(_,_) -> (m,dl)
  | Imp(_,_) -> (m,dl)
  | All(_,_) -> (m,dl)
  | _ ->
      let (mh,margs) = tm_head_args m in
      if defp sdel mh then
	headnorm1 (delta_exp sdel mh margs) sdel (delta_cons mh dl)
      else
	(m,dl)

let headnorm m sdel dl = headnorm1 (tm_beta_eta_norm m) sdel dl

let gen_lam_body m =
  match m with
  | Lam(_,mb) -> mb
  | _ -> Ap(tmshift 0 1 m,DB(0))

(*** conv2 assumes m and n are beta-eta normal ***)
let rec conv2 m n sdel dl =
  match (m,n) with
  | (Lam(a1,m1),Lam(b1,n1)) ->
      if a1 = b1 then
	conv2 m1 n1 sdel dl
      else
	None
  | (All(a1,m1),All(b1,n1)) ->
      if a1 = b1 then
	conv2 m1 n1 sdel dl
      else
	None
  | (Imp(m1,m2),Imp(n1,n2)) ->
      convl [m1;m2] [n1;n2] sdel dl
  | (Lam(_,_),All(_,_)) -> None
  | (Lam(_,_),Imp(_,_)) -> None
  | (All(_,_),Lam(_,_)) -> None
  | (All(_,_),Imp(_,_)) -> None
  | (Imp(_,_),All(_,_)) -> None
  | (Imp(_,_),Lam(_,_)) -> None
  | (_,Lam(_,n1)) -> conv2 (gen_lam_body m) n1 sdel dl
  | (Lam(_,m1),_) -> conv2 m1 (gen_lam_body n) sdel dl
  | (_,All(_,_)) ->
      let (mh,margs) = tm_head_args m in
      if defp sdel mh then
	conv2 (delta_exp sdel mh margs) n sdel (delta_cons mh dl)
      else
	None
  | (_,Imp(_,_)) ->
      let (mh,margs) = tm_head_args m in
      if defp sdel mh then
	conv2 (delta_exp sdel mh margs) n sdel (delta_cons mh dl)
      else
	None
  | (All(_,_),_) ->
      let (nh,nargs) = tm_head_args n in
      if defp sdel nh then
	conv2 m (delta_exp sdel nh nargs) sdel (delta_cons nh dl)
      else
	None
  | (Imp(_,_),_) ->
      let (nh,nargs) = tm_head_args n in
      if defp sdel nh then
	conv2 m (delta_exp sdel nh nargs) sdel (delta_cons nh dl)
      else
	None
  | _ ->
      let (mh,margs) = tm_head_args m in
      if defp sdel mh then
        if deltap dl mh then
	  conv2 (delta_exp sdel mh margs) n sdel dl
	else if !eagerdeltas then
          conv2 (delta_exp sdel mh margs) n sdel (delta_cons mh dl)
        else
	  begin
	    match convrigid1 mh margs n sdel dl with
	    | Some(dl) -> Some(dl)
	    | None -> (*** try delta expanding mh ***)
		conv2 (delta_exp sdel mh margs) n sdel (delta_cons mh dl)
	  end
      else
	convrigid1 mh margs n sdel dl
and convrigid1 mh margs n sdel dl =
  let (nh,nargs) = tm_head_args n in
  if defp sdel nh then
    if deltap dl nh then
      convrigid1 mh margs (delta_exp sdel nh nargs) sdel dl
    else if !eagerdeltas then
      convrigid1 mh margs (delta_exp sdel nh nargs) sdel (delta_cons nh dl)
    else
      begin
	match convrigid2 mh margs nh nargs sdel dl with
	| Some(dl) -> Some(dl)
	| None -> (*** try delta expanding nh ***)
	    convrigid1 mh margs (delta_exp sdel nh nargs) sdel (delta_cons nh dl)
      end
  else
    convrigid2 mh margs nh nargs sdel dl
and convrigid2 mh margs nh nargs sdel dl =
  if mh = nh then
    convl margs nargs sdel dl
  else
    None
and convl ml nl sdel dl =
  match (ml,nl) with
  | ([],[]) -> Some(dl)
  | (m::mr,n::nr) ->
      begin
	match conv2 m n sdel dl with
	| Some(dl) -> convl mr nr sdel dl
	| None -> None
      end
  | _ -> None

let conv m n sdel dl =
  conv2 (tm_beta_eta_norm m) (tm_beta_eta_norm n) sdel dl

let rec extr_propofpf sgdelta sgtmof cxtm cxpf d dl =
  match d with
  | Hyp j ->
     begin
       match !reportbushydeps with
       | Some(ch) -> Printf.fprintf ch "H %d\n" (List.length cxpf - j)
       | None -> ()
     end;
     (List.nth cxpf j,dl)
  | PTpAp(PTpAp(PTpAp(PTpAp(PTpAp(PTpAp(Known(h),a1),a2),a3),a4),a5),a6) ->
      begin
        if !sexprinfo then Printf.printf "(USESKNOWN \"%s\")\n" h;
	try
	  match Hashtbl.find sgdelta h with
	  | (i,p) ->
	      if i = 6 then
		(tmtpsubst p [a1;a2;a3;a4;a5;a6],dl)
	      else if i = 1 then
		raise (Failure(h ^ " requires 1 type but 6 were given"))
	      else
		raise (Failure(h ^ " requires " ^ (string_of_int i) ^ " types but was given 6"))
	with Not_found -> raise (Failure(h ^ " should be known, but is not known")) 
      end
  | PTpAp(PTpAp(PTpAp(PTpAp(PTpAp(Known(h),a1),a2),a3),a4),a5) ->
      begin
        if !sexprinfo then Printf.printf "(USESKNOWN \"%s\")\n" h;
	try
	  match Hashtbl.find sgdelta h with
	  | (i,p) ->
	      if i = 5 then
		(tmtpsubst p [a1;a2;a3;a4;a5],dl)
	      else if i = 1 then
		raise (Failure(h ^ " requires 1 type but 5 were given"))
	      else
		raise (Failure(h ^ " requires " ^ (string_of_int i) ^ " types but was given 5"))
	with Not_found -> raise (Failure(h ^ " should be known, but is not known")) 
      end
  | PTpAp(PTpAp(PTpAp(PTpAp(Known(h),a1),a2),a3),a4) ->
      begin
        if !sexprinfo then Printf.printf "(USESKNOWN \"%s\")\n" h;
	try
	  match Hashtbl.find sgdelta h with
	  | (i,p) ->
	      if i = 4 then
		(tmtpsubst p [a1;a2;a3;a4],dl)
	      else if i = 1 then
		raise (Failure(h ^ " requires 1 type but 4 were given"))
	      else
		raise (Failure(h ^ " requires " ^ (string_of_int i) ^ " types but was given 4"))
	with Not_found -> raise (Failure(h ^ " should be known, but is not known")) 
      end
  | PTpAp(PTpAp(PTpAp(Known(h),a1),a2),a3) ->
      begin
        if !sexprinfo then Printf.printf "(USESKNOWN \"%s\")\n" h;
	try
	  match Hashtbl.find sgdelta h with
	  | (i,p) ->
	      if i = 3 then
		(tmtpsubst p [a1;a2;a3],dl)
	      else if i = 1 then
		raise (Failure(h ^ " requires 1 type but 3 were given"))
	      else
		raise (Failure(h ^ " requires " ^ (string_of_int i) ^ " types but was given 3"))
	with Not_found -> raise (Failure(h ^ " should be known, but is not known")) 
      end
  | PTpAp(PTpAp(Known(h),a1),a2) ->
      begin
        if !sexprinfo then Printf.printf "(USESKNOWN \"%s\")\n" h;
	try
	  match Hashtbl.find sgdelta h with
	  | (i,p) ->
	      if i = 2 then
		(tmtpsubst p [a1;a2],dl)
	      else if i = 1 then
		raise (Failure(h ^ " requires 1 type but 2 were given"))
	      else
		raise (Failure(h ^ " requires " ^ (string_of_int i) ^ " types but was given 2"))
	with Not_found -> raise (Failure(h ^ " should be known, but is not known")) 
      end
  | PTpAp(Known(h),a1) ->
      begin
        if !sexprinfo then Printf.printf "(USESKNOWN \"%s\")\n" h;
	try
	  match Hashtbl.find sgdelta h with
	  | (i,p) ->
	      if i = 1 then
		(tmtpsubst p [a1],dl)
	      else
		raise (Failure(h ^ " requires " ^ (string_of_int i) ^ " types but was given 1"))
	with Not_found -> raise (Failure(h ^ " should be known, but is not known")) 
      end
  | Known(h) ->
      begin
        if !sexprinfo then Printf.printf "(USESKNOWN \"%s\")\n" h;
        begin
          match !reportbushydeps with
          | Some(ch) -> Printf.fprintf ch "K %s\n" h
          | None -> ()
        end;
	try
	  match Hashtbl.find sgdelta h with
	  | (i,p) ->
	      if i = 0 then
		(p,dl)
	      else if i = 1 then
		raise (Failure(h ^ " requires 1 type but was given none"))
	      else
		raise (Failure(h ^ " requires " ^ (string_of_int i) ^ " types but was given none"))
	with Not_found -> (TmH(h),dl) (* raise (Failure(h ^ " should be known, but is not known"))  *)
      end
  | PTmAp(d1,m) ->
      begin
	let (q,dl) = extr_propofpf sgdelta sgtmof cxtm cxpf d1 dl in
	match headnorm q sgdelta dl with
	| (All(a,p),dl) ->
            let b = extr_tpoftm sgtmof cxtm m in
	    if b = a then
	      (tmsubst p 0 m,dl)
	    else
              raise (Failure(Printf.sprintf "Proof term for a universally quantified proposition applied to a term of the wrong type\npf %s\nof %s\napplied to %s\nof type %s\n" (pf_to_str d1) (tm_to_str (All(a,p))) (tm_to_str m) (tp_to_str b)))
	| (p,_) ->
	    raise (Failure("Proof term does not prove a universally quantified proposition but is applied to a term"))
      end
  | PPfAp(d1,d2) ->
      begin
	let (q,dl) = extr_propofpf sgdelta sgtmof cxtm cxpf d1 dl in
	match headnorm q sgdelta dl with
	| (Imp(p1,p2),dl) ->
	    begin
	      match check_propofpf sgdelta sgtmof cxtm cxpf d2 p1 dl with
	      | Some(dl) -> (p2,dl)
	      | None ->
		  raise (Failure("Proof term for an implication applied to a proof term for the wrong proposition"))
	    end
	| (p,_) ->
	    raise (Failure("Proof term does not prove an implication but is applied to a proof term"))
      end
  | TLam(a,d1) ->
      let (q,dl) = extr_propofpf sgdelta sgtmof (a::cxtm) (List.map (fun q -> tmshift 0 1 q) cxpf) d1 dl in
      (All(a,q),dl)
  | PLam(p,d1) ->
      let (q,dl) = extr_propofpf sgdelta sgtmof cxtm (p::cxpf) d1 dl in
      (Imp(p,q),dl)
  | _ -> raise (Failure("Ill-formed Proof Term"))
and check_propofpf sgdelta sgtmof cxtm cxpf d p dl =
  let (q,dl) = extr_propofpf sgdelta sgtmof cxtm cxpf d dl in
  conv q p sgdelta dl

exception MatchFail

type mtm =
  | MVar of int * mtm list
  | MDB of int
  | MTmH of string
  | MPrim of int
  | MTpAp of mtm * tp
  | MAp of mtm * mtm
  | MLam of tp * mtm
  | MImp of mtm * mtm
  | MAll of tp * mtm

let rec mtm_to_str m =
  match m with
  | MVar(x,[]) -> "?" ^ string_of_int x
  | MVar(x,(n::sigma)) -> "?" ^ string_of_int x ^ "[" ^ (mtm_to_str n) ^ (List.fold_right (fun n r -> "," ^ (mtm_to_str n) ^ r) sigma "]")
  | MDB(i) -> "_" ^ string_of_int i
  | MTmH(h) -> "#" ^ h
  | MPrim(i) -> "\"" ^ string_of_int i ^ "\""
  | MTpAp(m1,m2) -> "(" ^ mtm_to_str m1 ^ " " ^ tp_to_str m2 ^ ")"
  | MAp(m1,m2) -> "(" ^ mtm_to_str m1 ^ " " ^ mtm_to_str m2 ^ ")"
  | MLam(m1,m2) -> "(fun _:" ^ tp_to_str m1 ^ " => " ^ mtm_to_str m2 ^ ")"
  | MImp(m1,m2) -> "(" ^ mtm_to_str m1 ^ " -> " ^ mtm_to_str m2 ^ ")"
  | MAll(m1,m2) -> "(forall _:" ^ tp_to_str m1 ^ ", " ^ mtm_to_str m2 ^ ")"

let rec tm_to_mtm q =
  match q with
  | DB i -> MDB i
  | TmH h -> MTmH h
  | Prim i -> MPrim i
  | TpAp(q1,a) -> MTpAp(tm_to_mtm q1,a)
  | Ap(q1,q2) -> MAp(tm_to_mtm q1,tm_to_mtm q2)
  | Imp(q1,q2) -> MImp(tm_to_mtm q1,tm_to_mtm q2)
  | Lam(a,q1) -> MLam(a,tm_to_mtm q1)
  | All(a,q1) -> MAll(a,tm_to_mtm q1)

let rec mtm_to_tm q =
  match q with
  | MVar(_,_) -> raise Not_found
  | MDB i -> DB i
  | MTmH h -> TmH h
  | MPrim i -> Prim i
  | MTpAp(q1,a) -> TpAp(mtm_to_tm q1,a)
  | MAp(q1,q2) -> Ap(mtm_to_tm q1,mtm_to_tm q2)
  | MImp(q1,q2) -> Imp(mtm_to_tm q1,mtm_to_tm q2)
  | MLam(a,q1) -> Lam(a,mtm_to_tm q1)
  | MAll(a,q1) -> All(a,mtm_to_tm q1)

let rec mtm_shift i j m =
  match m with
  | MVar(x,sigma) -> MVar(x,List.map (mtm_shift i j) sigma)
  | MDB(k) when k < i -> MDB(k)
  | MDB(k) ->
      let l = k + j in
      if l >= i then MDB(l) else raise NegDB
  | MTpAp(m1,a) -> MTpAp(mtm_shift i j m1,a)
  | MAp(m1,m2) -> MAp(mtm_shift i j m1,mtm_shift i j m2)
  | MLam(a1,m1) -> MLam(a1,mtm_shift (i+1) j m1)
  | MImp(m1,m2) -> MImp(mtm_shift i j m1,mtm_shift i j m2)
  | MAll(a1,m1) -> MAll(a1,mtm_shift (i+1) j m1)
  | _ -> m

let rec mtm_subst m j n =
  match m with
  | MVar(x,sigma) -> MVar(x,List.map (fun m -> mtm_subst m j n) sigma)
  | MDB(i) when i = j && j = 0 -> n
  | MDB(i) when i = j -> mtm_shift 0 j n
  | MDB(i) when i > j -> MDB(i-1)
  | MTpAp(m1,a) -> MTpAp(mtm_subst m1 j n,a) (*** This could be omitted since it should always be TmH applied to <= 3 type variables, and so will contain no de Bruijns. ***)
  | MAp(m1,m2) -> MAp(mtm_subst m1 j n,mtm_subst m2 j n)
  | MLam(a1,m1) -> MLam(a1,mtm_subst m1 (j+1) n)
  | MImp(m1,m2) -> MImp(mtm_subst m1 j n,mtm_subst m2 j n)
  | MAll(a1,m1) -> MAll(a1,mtm_subst m1 (j+1) n)
  | _ -> m

let rec mtm_ssub tau q =
  match q with
  | MVar(x,sigma) -> MVar(x,List.map (mtm_ssub tau) sigma)
  | MDB i -> List.nth tau i
  | MTmH h -> MTmH h
  | MPrim i -> MPrim i
  | MTpAp(q1,a) -> MTpAp(mtm_ssub tau q1,a)
  | MAp(q1,q2) -> MAp(mtm_ssub tau q1,mtm_ssub tau q2)
  | MImp(q1,q2) -> MImp(mtm_ssub tau q1,mtm_ssub tau q2)
  | MLam(a,q1) -> MLam(a,mtm_ssub (MDB 0::List.map (mtm_shift 0 1) tau) q1)
  | MAll(a,q1) -> MAll(a,mtm_ssub (MDB 0::List.map (mtm_shift 0 1) tau) q1)

let rec mtm_msub theta q =
  match q with
  | MVar(x,sigma) ->
      begin
	let thetasigma = List.map (mtm_msub theta) sigma in
	try
	  let m = theta x in
	  mtm_ssub thetasigma m
	with Not_found -> MVar(x,thetasigma)
      end
  | MTpAp(q1,a) -> MTpAp(mtm_msub theta q1,a)
  | MAp(q1,q2) -> MAp(mtm_msub theta q1,mtm_msub theta q2)
  | MImp(q1,q2) -> MImp(mtm_msub theta q1,mtm_msub theta q2)
  | MLam(a,q1) -> MLam(a,mtm_msub theta q1)
  | MAll(a,q1) -> MAll(a,mtm_msub theta q1)
  | _ -> q

let op_min r z =
  match r with
  | Some(y) -> min y z
  | None -> z

let rec mtm_minap_db_r q j z r =
  match q with
  | MVar(x,sigma) ->
      mtms_minap_db_r sigma j r
  | MDB i when i = j -> Some(op_min r z)
  | MTpAp(q1,a) -> r (*** assume no DBs in q1 ***)
  | MAp(q1,q2) -> mtm_minap_db_r q1 j (z+1) (mtm_minap_db_r q2 j 0 r)
  | MImp(q1,q2) -> mtm_minap_db_r q1 j 0 (mtm_minap_db_r q2 j 0 r)
  | MLam(a,q1) -> mtm_minap_db_r q1 (j+1) 0 r
  | MAll(a,q1) -> mtm_minap_db_r q1 (j+1) 0 r
  | _ -> r
and mtms_minap_db_r sigma j r =
  match sigma with
  | [] -> r
  | (q::sigmar) -> mtms_minap_db_r sigmar j (mtm_minap_db_r q j 0 r)

let mtm_minap_db q j = mtm_minap_db_r q j 0 None

let rec mtm_lammvar_p q =
  match q with
  | MVar(_,_) -> true
  | MLam(_,q1) -> mtm_lammvar_p q1
  | _ -> false

let rec mtm_betared_if_1 q p =
  match q with
  | MVar(x,sigma) ->
      let (sigmar,sigmab) = mtms_betared_if_1 sigma p in
      (MVar(x,sigmar),sigmab)
  | MAp(q1,q2) ->
      let (q1r,q1b) = mtm_betared_if_1 q1 p in
      let (q2r,q2b) = mtm_betared_if_1 q2 p in
      begin
	match q1r with
	| MLam(a,qb) ->
	    if p qb q2r then
	      begin
		beta_count_check ();
		(mtm_subst qb 0 q2r,false) (*** beta, satisfying p ***)
	      end
	    else
	      (MAp(q1r,q2r),q1b && q2b)
	| _ -> (MAp(q1r,q2r),q1b && q2b)
      end
  | MLam(a,q1) ->
      let (q1r,q1b) = mtm_betared_if_1 q1 p in
      (MLam(a,q1r),q1b)
  | MImp(q1,q2) ->
      let (q1r,q1b) = mtm_betared_if_1 q1 p in
      let (q2r,q2b) = mtm_betared_if_1 q2 p in
      (MImp(q1r,q2r),q1b && q2b)
  | MAll(a,q1) ->
      let (q1r,q1b) = mtm_betared_if_1 q1 p in
      (MAll(a,q1r),q1b)
  | MTpAp(_,_) -> (q,true) (*** invariant should imply no betas are in here ***)
  | _ -> (q,true)
and mtms_betared_if_1 sigma p =
  match sigma with
  | [] -> ([],true)
  | (q::sigmar) ->
      let (qr,qb) = mtm_betared_if_1 q p in
      let (sigmarr,sigmarb) = mtms_betared_if_1 sigmar p in
      (qr::sigmarr,qb && sigmarb)

let rec mtm_betared_if q p =
  let (qr,qb) = mtm_betared_if_1 q p in
  if qb then
    qr
  else
    mtm_betared_if qr p

let rec pattern_invert k sigma q =
  match q with
  | DB i when i < k -> MDB i
  | DB i ->
      let j = position sigma (MDB (i-k)) in
      MDB (j+k)
  | TmH h -> MTmH h
  | Prim i -> MPrim i
  | TpAp(q1,a) -> MTpAp(pattern_invert k sigma q1,a)
  | Ap(q1,q2) -> MAp(pattern_invert k sigma q1,pattern_invert k sigma q2)
  | Imp(q1,q2) -> MImp(pattern_invert k sigma q1,pattern_invert k sigma q2)
  | Lam(a,q1) -> MLam(a,pattern_invert (k+1) sigma q1)
  | All(a,q1) -> MAll(a,pattern_invert (k+1) sigma q1)

let rec pattern_match sdel p q theta =
  match (p,q) with
  | (MVar(x,sigma),_) ->
      begin
	try
	  let m = mtm_ssub sigma (theta x) in
	  pattern_match sdel m q theta
	with Not_found ->
	  try
	    let m = pattern_invert 0 sigma q in
	    (fun y -> if x = y then m else theta y)
	  with Not_found -> raise MatchFail
      end
  | (MDB i,DB j) when i = j -> theta
  | (MPrim i,Prim j) when i = j -> theta
  | (MTmH h,TmH k) when h = k -> theta
  | (MTpAp(MTmH h,a1),TpAp(TmH k,b1)) when h = k && a1 = b1 -> theta
  | (MTpAp(MTpAp(MTmH h,a1),a2),TpAp(TpAp(TmH k,b1),b2)) when h = k && a1 = b1 && a2 = b2 -> theta
  | (MTpAp(MTpAp(MTpAp(MTmH h,a1),a2),a3),TpAp(TpAp(TpAp(TmH k,b1),b2),b3)) when h = k && a1 = b1 && a2 = b2 && a3 = b3 -> theta
  | (MAp(p1,p2),Ap(q1,q2)) ->
      let theta = pattern_match sdel p1 q1 theta in
      pattern_match sdel p2 q2 theta
  | (MImp(p1,p2),Imp(q1,q2)) ->
      let theta = pattern_match sdel p1 q1 theta in
      pattern_match sdel p2 q2 theta
  | (MLam(a1,p1),Lam(b1,q1)) when a1 = b1 ->
      pattern_match sdel p1 q1 theta
  | (MAll(a1,p1),All(b1,q1)) when a1 = b1 ->
      pattern_match sdel p1 q1 theta
  | (_,_) ->
      begin
	try
	  let p1 = mtm_to_tm p in
	  match conv p1 q sdel [] with
	  | Some(_) -> theta
	  | None -> raise MatchFail
	with Not_found -> raise MatchFail
      end

let rec mtm_app_red2 m args =
  match args with
  | (n::argr) -> mtm_app_red2 (MAp(m,n)) argr
  | _ -> m

let rec mtm_app_red m args =
  match (m,args) with
  | (MLam(_,m1),n::argr) ->
      mtm_app_red (mtm_subst m1 0 n) argr
  | _ ->
      mtm_app_red2 m args

let mdefp sdel h =
  match h with
  | MTmH(c) -> Hashtbl.mem sdel c
  | MTpAp(MTmH(c),_) -> Hashtbl.mem sdel c
  | MTpAp(MTpAp(MTmH(c),_),_) -> Hashtbl.mem sdel c
  | MTpAp(MTpAp(MTpAp(MTmH(c),_),_),_) -> Hashtbl.mem sdel c
  | _ -> false

(*** assume all defs are beta eta normal ***)
let mdelta_exp sdel h args =
  try
    match h with
    | MTmH(c) ->
	begin
	  let (i,m) = Hashtbl.find sdel c in
	  if i = 0 then
	    mtm_app_red (tm_to_mtm m) args
	  else if i = 1 then
	    raise (Failure(c ^ " should be applied to 1 type, but is applied to none."))
	  else
	    raise (Failure(c ^ " should be applied to " ^ (string_of_int i) ^ " types, but is applied to none."))
	end
    | MTpAp(MTmH(c),a1) ->
	begin
	  let (i,m) = Hashtbl.find sdel c in
	  if i = 1 then
	    mtm_app_red (tm_to_mtm (tmtpsubst m [a1])) args
	  else
	    raise (Failure(c ^ " should be applied to " ^ (string_of_int i) ^ " types, but is applied to 1."))
	end
    | MTpAp(MTpAp(MTmH(c),a1),a2) ->
	begin
	  let (i,m) = Hashtbl.find sdel c in
	  if i = 2 then
	    mtm_app_red (tm_to_mtm (tmtpsubst m [a1;a2])) args
	  else if i = 1 then
	    raise (Failure(c ^ " should be applied to 1 type, but is applied to 2."))
	  else
	    raise (Failure(c ^ " should be applied to " ^ (string_of_int i) ^ " types, but is applied to 2."))
	end
    | MTpAp(MTpAp(MTpAp(MTmH(c),a1),a2),a3) ->
	begin
	  let (i,m) = Hashtbl.find sdel c in
	  if i = 3 then
	    mtm_app_red (tm_to_mtm (tmtpsubst m [a1;a2;a3])) args
	  else if i = 1 then
	    raise (Failure(c ^ " should be applied to 1 type, but is applied to 3."))
	  else
	    raise (Failure(c ^ " should be applied to " ^ (string_of_int i) ^ " types, but is applied to 3."))
	end
    | _ -> raise Not_found
  with Not_found ->
    raise (Failure("mdelta_exp called with an inappropriate head. Bug"))

let rec mtm_head_args_r m args =
  match m with
  | MAp(m1,m2) -> mtm_head_args_r m1 (m2::args)
  | _ -> (m,args)

let mtm_head_args m =
  mtm_head_args_r m []

let mdelta_cons h dl =
  match h with
  | MTmH(c) -> (c::dl)
  | _ -> dl

let rec mheadnorm1 m sdel dl =
  match m with
  | MLam(_,_) -> (m,dl)
  | MImp(_,_) -> (m,dl)
  | MAll(_,_) -> (m,dl)
  | _ ->
      let (mh,margs) = mtm_head_args m in
      if mdefp sdel mh then
	mheadnorm1 (mdelta_exp sdel mh margs) sdel (mdelta_cons mh dl)
      else
	(m,dl)

let mheadnorm m sdel dl = mheadnorm1 m sdel dl

let valid_id_p h = String.length h = 64

let rec to_mathdata_tp l a =
  match a with
  | TpVar(i) -> Mathdata.TpVar(l-i-1)
  | Prop -> Mathdata.Prop
  | Set -> Mathdata.Base(0)
  | Ar(a1,a2) -> Mathdata.Ar(to_mathdata_tp l a1,to_mathdata_tp l a2)

let rec to_mathdatapfghf_tp a =
  match a with
  | TpVar(i) -> raise (Failure "no poly in pfg")
  | Prop -> Mathdatapfg.Prop
  | Set -> Mathdatapfg.Base(0)
  | Ar(a1,a2) -> Mathdatapfg.TpArr(to_mathdatapfghf_tp a1,to_mathdatapfghf_tp a2)

let rec to_mathdatapfgegal_tp a =
  match a with
  | TpVar(i) -> raise (Failure "no poly in pfg")
  | Prop -> Mathdatapfg.Prop
  | Set -> Mathdatapfg.Base(0)
  | Ar(a1,a2) -> Mathdatapfg.TpArr(to_mathdatapfgegal_tp a1,to_mathdatapfgegal_tp a2)

let rec to_mathdatapfgmiz_tp a =
  match a with
  | TpVar(i) -> raise (Failure "no poly in pfg")
  | Prop -> Mathdatapfg.Prop
  | Set -> Mathdatapfg.Base(0)
  | Ar(a1,a2) -> Mathdatapfg.TpArr(to_mathdatapfgmiz_tp a1,to_mathdatapfgmiz_tp a2)

let rec to_mathdatapfgsetmm_tp a =
  match a with
  | TpVar(i) -> raise (Failure "no poly in pfg")
  | Prop -> Mathdatapfg.Prop
  | Set -> Mathdatapfg.Base(0)
  | Ar(a1,a2) -> Mathdatapfg.TpArr(to_mathdatapfgsetmm_tp a1,to_mathdatapfgsetmm_tp a2)

let rec to_mathdatapfghoas_tp a =
  match a with
  | TpVar(i) -> raise (Failure "no poly in pfg")
  | Prop -> Mathdatapfg.Prop
  | Set -> Mathdatapfg.Base(0)
  | Ar(a1,a2) -> Mathdatapfg.TpArr(to_mathdatapfghoas_tp a1,to_mathdatapfghoas_tp a2)

let to_mathdatapfg_tp a =
  match !pfgtheory with
  | HF -> to_mathdatapfghf_tp a
  | Egal -> to_mathdatapfgegal_tp a
  | Mizar -> to_mathdatapfgmiz_tp a
  | HOAS -> to_mathdatapfghoas_tp a
  | SetMM -> to_mathdatapfgsetmm_tp a

let rec to_mathdata_ptp i l a =
  if i > 0 then
     Mathdata.TpAll(to_mathdata_ptp (i-1) (l+1) a)
  else
     to_mathdata_tp l a

let rec to_mathdata_tm l m =
  match m with
  | DB(i) -> Mathdata.DB(i)
  | TmH(h) -> Mathdata.TmH(Hash.hexstring_hashval h)
  | Prim(i) -> Mathdata.Prim(i)
  | TpAp(m,a) -> Mathdata.TTpAp(to_mathdata_tm l m,to_mathdata_tp l a)
  | Ap(m,n) -> Mathdata.Ap(to_mathdata_tm l m,to_mathdata_tm l n)
  | Lam(a,m) -> Mathdata.Lam(to_mathdata_tp l a,to_mathdata_tm l m)
  | Imp(m,n) -> Mathdata.Imp(to_mathdata_tm l m,to_mathdata_tm l n)
  | All(a,m) -> Mathdata.All(to_mathdata_tp l a,to_mathdata_tm l m)

let rec to_mathdata_ptm_lam i l m =
  if i > 0 then
     Mathdata.TTpLam(to_mathdata_ptm_lam (i-1) (l+1) m)
  else
     to_mathdata_tm l m

let rec to_mathdata_ptm_all i l m =
  if i > 0 then
     Mathdata.TTpAll(to_mathdata_ptm_all (i-1) (l+1) m)
  else
     to_mathdata_tm l m

let rec to_mathdata_pf l d =
  match d with
  | Hyp(i) -> Mathdata.Hyp(i)
  | Known(h) -> Mathdata.Known(Hash.hexstring_hashval h)
  | PTpAp(d,a) -> Mathdata.PTpAp(to_mathdata_pf l d,to_mathdata_tp l a)
  | PTmAp(d,m) -> Mathdata.PTmAp(to_mathdata_pf l d,to_mathdata_tm l m)
  | PPfAp(d,e) -> Mathdata.PPfAp(to_mathdata_pf l d,to_mathdata_pf l e)
  | PLam(m,d) -> Mathdata.PLam(to_mathdata_tm l m,to_mathdata_pf l d)
  | TLam(a,d) -> Mathdata.TLam(to_mathdata_tp l a,to_mathdata_pf l d)

let rec to_mathdata_ppf i l d =
  if i > 0 then
     Mathdata.PTpLam(to_mathdata_ppf (i-1) (l+1) d)
  else
     to_mathdata_pf l d

let tp_id a = Hash.hashval_hexstring (Mathdata.hashtp (to_mathdata_tp 0 a))

let ptp_id (i,a) = Hash.hashval_hexstring (Mathdata.hashtp (to_mathdata_ptp i 0 a))

let tm_id m sof sdel = Hash.hashval_hexstring (Mathdata.tm_hashroot (to_mathdata_tm 0 (tm_beta_eta_exeq_norm m)))

let ptm_lam_id (i,m) sof sdel = Hash.hashval_hexstring (Mathdata.tm_hashroot (to_mathdata_ptm_lam i 0 (tm_beta_eta_exeq_norm m)))
let ptm_all_id (i,m) sof sdel = Hash.hashval_hexstring (Mathdata.tm_hashroot (to_mathdata_ptm_all i 0 (tm_beta_eta_exeq_norm m)))

let hfthyid = Hash.hexstring_hashval "6ffc9680fbe00a58d70cdeb319f11205ed998131ce51bb96f16c7904faf74a3d"
let egalthyid = Hash.hexstring_hashval "29c988c5e6c620410ef4e61bcfcbe4213c77013974af40759d8b732c07d61967"
let mizarthyid = Hash.hexstring_hashval "5ab3df7b0b4ef20889de0517a318df8746940971ad9b2021e54c820eb9e74dce"
let hoasthyid = Hash.hexstring_hashval "513140056e2032628f48d11e221efe29892e9a03a661d3b691793524a5176ede"
let setmmthyid = Hash.hexstring_hashval "85ecfdcf26657b94532af5af2393c6945cee05c4aabccb8a819f793a7dbc4acf"

let pf_id d sof sdel = Hash.hashval_hexstring (Mathdata.pf_hashroot (to_mathdata_pf 0 d))

let ppf_id (i,d) sof sdel = "0000000000000000000000000000000000000000000000000000000000000000" (** This is fake, bviously. ppf_id isn't really needed anymore and is expensive to compute. **)

let rec tp_args_rtp a =
  match a with
  | Ar(a1,a2) ->
      let (argtpl,rtp) = tp_args_rtp a2 in
      (a1::argtpl,rtp)
  | _ -> ([],a)

let rec mk_forall_tm argtpl f m n =
  match argtpl with
  | (a::argtpr) ->
      let mb = gen_lam_body m in
      let nb = gen_lam_body n in
      All(a,mk_forall_tm argtpr f mb nb)
  | [] -> f m n

let rec mk_gen_ap m nl =
  match nl with
  | (n::nr) -> mk_gen_ap (Ap(m,n)) nr
  | [] -> m

let unicode : (string,string list) Hashtbl.t = Hashtbl.create 100;;
let subscript : (string,unit) Hashtbl.t = Hashtbl.create 100;;
let superscript : (string,unit) Hashtbl.t = Hashtbl.create 100;;

begin
  Hashtbl.add unicode "->" ["2192"];
  Hashtbl.add unicode "fun" ["3bb"];
  Hashtbl.add unicode "forall" ["2200"];
end

let authors : string list ref = ref []
let title : string option ref = ref None
let signature : string option ref = ref None
let showproofterms : bool ref = ref false
let salt : string option ref = ref None
let treasure : string option ref = ref None

(*** code for measuring complexity of tms and pfs -- not necessary ***)
let rec rem_dups_r ml rl =
  match ml with
  | [] -> rl
  | (m::mr) ->
      if List.mem m rl then
	rem_dups_r mr rl
      else
	rem_dups_r mr (m::rl)

let rem_dups ml = rem_dups_r ml []

let rec tm_info m =
  match m with
  | Lam(a,m) ->
      let (hs,ltps,atps,aps,imps) = tm_info m in
      (hs,a::ltps,atps,aps,imps)
  | All(a,m) -> 
      let (hs,ltps,atps,aps,imps) = tm_info m in
      (hs,ltps,a::atps,aps,imps)
  | Ap(m1,m2) ->
      let (hs1,ltps1,atps1,aps1,imps1) = tm_info m1 in
      let (hs2,ltps2,atps2,aps2,imps2) = tm_info m2 in
      (hs1 @ hs2,ltps1 @ ltps2,atps1 @ atps2,1+aps1+aps2,imps1+imps2)
  | Imp(m1,m2) ->
      let (hs1,ltps1,atps1,aps1,imps1) = tm_info m1 in
      let (hs2,ltps2,atps2,aps2,imps2) = tm_info m2 in
      (hs1 @ hs2,ltps1 @ ltps2,atps1 @ atps2,aps1+aps2,1+imps1+imps2)
  | TmH(h) -> ([h],[],[],0,0)
  | TpAp(TmH(h),_) -> ([h],[],[],0,0)
  | TpAp(TpAp(TmH(h),_),_) -> ([h],[],[],0,0)
  | TpAp(TpAp(TpAp(TmH(h),_),_),_) -> ([h],[],[],0,0)
  | TpAp(TpAp(TpAp(TpAp(TmH(h),_),_),_),_) -> ([h],[],[],0,0)
  | TpAp(TpAp(TpAp(TpAp(TpAp(TmH(h),_),_),_),_),_) -> ([h],[],[],0,0)
  | TpAp(TpAp(TpAp(TpAp(TpAp(TpAp(TmH(h),_),_),_),_),_),_) -> ([h],[],[],0,0)
  | _ -> ([],[],[],0,0)

let rec pf_info d =
  match d with
  | Known(h) -> ([h],[],[],0,[],[])
  | PTpAp(Known(h),_) -> ([h],[],[],0,[],[])
  | PTpAp(PTpAp(Known(h),_),_) -> ([h],[],[],0,[],[])
  | PTpAp(PTpAp(PTpAp(Known(h),_),_),_) -> ([h],[],[],0,[],[])
  | PTpAp(PTpAp(PTpAp(PTpAp(Known(h),_),_),_),_) -> ([h],[],[],0,[],[])
  | PTpAp(PTpAp(PTpAp(PTpAp(PTpAp(Known(h),_),_),_),_),_) -> ([h],[],[],0,[],[])
  | PTpAp(PTpAp(PTpAp(PTpAp(PTpAp(PTpAp(Known(h),_),_),_),_),_),_) -> ([h],[],[],0,[],[])
  | TLam(a,d) ->
      let (kl,tlams,insts,mps,plams,pbetas) = pf_info d in
      (kl,a::tlams,insts,mps,plams,pbetas)
  | PTmAp(d,m) ->
      let (kl,tlams,insts,mps,plams,pbetas) = pf_info d in
      (kl,tlams,m::insts,mps,plams,pbetas)
  | PPfAp(d1,d2) ->
      let (kl1,tlams1,insts1,mps1,plams1,pbetas1) = pf_info d1 in
      let (kl2,tlams2,insts2,mps2,plams2,pbetas2) = pf_info d2 in
      begin
	match d1 with
	| PLam(m,d) ->
	    (kl1 @ kl2,tlams1 @ tlams2,insts1 @ insts2,1+mps1+mps2,plams1 @ plams2,m::(pbetas1 @ pbetas2))
	| _ ->
	    (kl1 @ kl2,tlams1 @ tlams2,insts1 @ insts2,1+mps1+mps2,plams1 @ plams2,pbetas1 @ pbetas2)
      end
  | PLam(m,d) ->
      let (kl,tlams,insts,mps,plams,pbetas) = pf_info d in
      (kl,tlams,insts,mps,m::plams,pbetas)
  | _ -> ([],[],[],0,[],[])

let pf_complexity d =
  let (kl,tlams,insts,mps,plams,pbetas) = pf_info d in
  let kl2 = rem_dups kl in
  let tlams2 = rem_dups tlams in
  let insts2 = rem_dups insts in
  let plams2 = rem_dups plams in
  let pbetas2 = rem_dups pbetas in
  let complexity = ref (5 * mps) in
  complexity := !complexity + 10 * (List.length kl2) + List.length kl;
  complexity := !complexity + 10 * (List.length tlams2) + List.length tlams;
  List.iter
    (fun m ->
      let (hs,ltps,atps,aps,imps) = tm_info m in
      complexity := !complexity + List.length hs + List.length ltps + List.length atps + aps + imps
      )
    plams2;
  complexity := !complexity + List.length plams;
  List.iter
    (fun m ->
      let (hs,ltps,atps,aps,imps) = tm_info m in
      let hs2 = rem_dups hs in
      let ltps2 = rem_dups ltps in
      let atps2 = rem_dups atps in
      complexity := !complexity + 100 * (List.length ltps2); (** number of lambdas in the instantiations **)
      complexity := !complexity + 5 * (List.length hs2 + List.length atps2) + 10 * (List.length ltps) + List.length hs + List.length atps)
    insts2;
  complexity := !complexity + 10 * List.length insts;
  List.iter
    (fun m ->
      let (hs,ltps,atps,aps,imps) = tm_info m in
      let hs2 = rem_dups hs in
      let ltps2 = rem_dups ltps in
      let atps2 = rem_dups atps in
      complexity := !complexity + 70 * (List.length ltps2);
      complexity := !complexity + 3 * (List.length hs2 + List.length atps2) + 7 * (List.length ltps) + List.length hs + List.length atps)
    pbetas2;
  !complexity

let globalhrefs = ref false
let localhrefh : (string,unit) Hashtbl.t = Hashtbl.create 100

let output_unicode_html ch u =
  output_string ch "&#x";
  output_string ch u;
  output_char ch ';'

let output_name_html ch x =
  try
    let ul = Hashtbl.find unicode x in
    List.iter (fun u -> output_unicode_html ch u) ul
  with Not_found ->
    output_string ch x

let output_asckind_html ch k =
  match k with
  | AscTp -> output_string ch " : "
  | AscSet -> output_string ch " &#x2208; "
  | AscSubeq -> output_string ch " &#x2286; "

let output_plain_setinfixop_html ch k =
  match k with
  | InfMem -> output_string ch " &#x2208; "
  | InfSubq -> output_string ch " &#x2286; "

let output_setinfixop_html ch k =
  match k with
  | InfMem -> output_string ch " <a href='#In_notation'>&#x2208;</a> "
  | InfSubq -> output_string ch " <a href='#Subq_notation'>&#x2286;</a> "

let output_infixop_html ch i =
  match i with
  | InfNam(x) -> output_name_html ch x
  | InfSet(k) -> output_setinfixop_html ch k

let output_midtok_html ch m =
  if m = "," then
    output_string ch ", "
  else if m = "=>" then
    output_string ch " &#x21d2; "
  else
    output_string ch m

let output_names_html ch xl =
  match xl with
  | [] -> ()
  | (x::yl) ->
      output_name_html ch x;
      List.iter
	(fun y ->
	  output_char ch ' ';
	  output_string ch y;
	)
	yl

let rec output_comma_names_html ch xl =
  match xl with
  | [] -> ()
  | [x] ->
      output_name_html ch x;
  | [x;y] ->
      output_name_html ch x;
      output_string ch " and ";
      output_name_html ch y;
  | (x::yl) ->
      output_name_html ch x;
      output_string ch ", ";
      output_comma_names_html ch yl

let url_friendly_name x = x
(**
  let y = Buffer.create 100 in
  for i = 0 to (String.length x) - 1 do
    let c = x.[i] in
    let co = Char.code c in
    if (co >= 48 && co <= 57 || co >= 65 && co <= 90 || co >= 97 && co <= 122) then
      Buffer.add_char y c
    else
      begin
	Buffer.add_char y '_';
	Buffer.add_char y (hex_char ((co lsr 4) mod 16));
	Buffer.add_char y (hex_char (co mod 16));
      end
  done;
  Buffer.contents y
 **)

(*** <a> causes css problems in combination with <span> for some reason, so only call this if it's declaring the name (not inside an lterm).
    Eh, it also insists on screwing up the font. I've just changed all anchors to have the math friendly font. How annoying. ***)
let output_name_whrefa_html cx ch x stmh sknh =
  if List.mem x cx then
    output_name_html ch x
  else
    begin
      try
        if not (!pfgtheory = HF) then raise Not_found;
        let p = Hashtbl.find pfghfanchor x in
        Printf.fprintf ch "<a classname='anamelink' href='https://mgwiki.github.io/mgw_test/th/HOHF.html#%s'>%s</a>" p x
      with Not_found ->
        try
          if not !globalhrefs then raise Not_found;
          let hid = Hashtbl.find stmh x in
          output_string ch "<a classname='anamelink' href='term.php?h=";
          output_string ch hid;
          output_string ch "'>";
          output_name_html ch x;
          output_string ch "</a>";
        with Not_found ->
          try
            if not !globalhrefs then raise Not_found;
	    let hid = Hashtbl.find sknh x in
	    output_string ch "<a classname='anamelink' href='term.php?h="; 
	    output_string ch hid;
	    output_name_html ch x;
	    output_string ch "</a>";
          with Not_found ->
            if Hashtbl.mem localhrefh x then
              begin
	        output_string ch "<a classname='anamelink' href='#"; 
	        output_string ch (url_friendly_name x);
	        output_string ch "'>";
	        output_name_html ch x;
	        output_string ch "</a>";
              end
            else
	      output_name_html ch x;
    end

(*** <a> causes css problems in combination with <span> for some reason, so I usually call this and use a span for links ***)
let output_name_whref_html ch x stmh sknh =
  begin
    try
      if not !globalhrefs then raise Not_found;
      let hid = Hashtbl.find stmh x in
      output_string ch "<span class='namelink' onclick=\"location.href='term.php?h="; 
      output_string ch hid;
      output_string ch "';\">";
      output_name_html ch x;
      output_string ch "</span>";
    with Not_found ->
      try
        if not !globalhrefs then raise Not_found;
	let hid = Hashtbl.find sknh x in
	output_string ch "<span class='namelink' onclick=\"location.href='term.php?h=";
        output_string ch hid;
	output_string ch "';\">";
	output_name_html ch x;
	output_string ch "</span>";
      with Not_found ->
        if Hashtbl.mem localhrefh x then
          begin
	    output_string ch "<span class='namelink' onclick=\"location.href='#";
	    output_string ch (url_friendly_name x);
	    output_string ch "'\">";
	    output_name_html ch x;
	    output_string ch "</span>";
          end
        else
	  output_name_html ch x;
  end

let rec output_ltree_html cx ch a stmh sknh =
  output_string ch "<span class='ltree'>";
  output_ltree_html_c cx ch a stmh sknh;
  output_string ch "</span>"
and output_ltree_html_c cx ch a stmh sknh =
  match a with
  | ByteL(x) -> Printf.fprintf ch "\\x%02x" x
  | StringL(x) -> output_char ch '"'; output_string ch x; output_char ch '"'
  | QStringL(x) -> output_char ch '?'; output_string ch x; output_char ch '?'
  | NaL(x) ->
      output_name_whrefa_html cx ch x stmh sknh
  | NuL(b,x,None,None) ->
      begin
	if b then output_char ch '-';
        wrap_href_special ch !natnotationhrefstack
          (fun () ->
	    output_string ch x);
      end
  | NuL(b,x,Some y,None) ->
      begin
	if b then output_char ch '-';
	output_string ch x;
	output_char ch '.';
	output_string ch y;
      end
  | NuL(b,x,None,Some z) ->
      begin
	if b then output_char ch '-';
	output_string ch x;
	output_char ch 'E';
	output_string ch z;
      end
  | NuL(b,x,Some y,Some z) ->
      begin
	if b then output_char ch '-';
	output_string ch x;
	output_char ch '.';
	output_string ch y;
	output_char ch 'E';
	output_string ch z;
      end
  | LeL(x,None,a,c) ->
      begin
	output_string ch "<span class='keyword'>let</span> ";
	output_string ch x;
	output_string ch  " &#x2254; ";
	output_ltree_html cx ch a stmh sknh;
	output_string ch " <span class='keyword'>in</span> ";
	output_ltree_html cx ch c stmh sknh;
      end
  | LeL(x,Some(i,b),a,c) ->
      begin
	output_string ch "<span class='keyword'>let</span> ";
	output_string ch x;
	output_asckind_html ch i;
	output_ltree_html cx ch b stmh sknh;
	output_string ch  " &#x2254; ";
	output_ltree_html cx ch a stmh sknh;
	output_string ch " <span class='keyword'>in</span> ";
	output_ltree_html cx ch c stmh sknh;
      end
  | LeML(x,yl,a,c) ->
      begin
	output_string ch "<span class='keyword'>let</span> [";
	output_string ch x;
	List.iter
	  (fun y ->
	    output_char ch ',';
	    output_string ch y;
	    )
	  yl;
	output_string ch  "] := ";
	output_ltree_html cx ch a stmh sknh;
	output_string ch  " in ";
	output_ltree_html cx ch c stmh sknh;
      end
  | BiL(x,m,[(xl,o)],c) ->
      let subp = Hashtbl.mem subscript x in
      let supp = Hashtbl.mem superscript x in
      let setinbd = match o with None -> false | Some(i,_) -> i = AscSet in
      let setsubqbd = match o with None -> false | Some(i,_) -> i = AscSubeq in
      let wrap1 = wrap_href_special ch
                   (if x = "fun" then
                      (if setinbd || setsubqbd then !setlamnotationhrefstack else [])
                    else if x = "forall" || x = "exists" then
                      []
                    else
                      hashtbl_find_or_nil bindernotationhrefstack x)
      in
      let wrap2 = wrap_href_special ch
                    (if x = "fun" then
                       (if setinbd || setsubqbd then !setlamnotationhrefstack else [])
                     else if x = "forall" then
                       (if setinbd then ["In_notation"] else if setsubqbd then ["Subq_notation"] else [])
                     else
                       hashtbl_find_or_nil bindernotationhrefstack x)
      in
      wrap1
        (fun () ->
          output_name_html ch x);
      if subp then output_string ch "<sub>" else if supp then output_string ch "<sup>" else if not (Hashtbl.mem unicode x) then output_string ch " ";
      output_names_html ch xl;
      begin
	match o with
	| None -> ()
	| Some(i,b) ->
           wrap2
             (fun () ->
	       output_asckind_html ch i);
	   output_ltree_html cx ch b stmh sknh
      end;
      if subp then
	output_string ch "</sub>"
      else if supp then
	output_string ch "</sup>"
      else
	begin
	  output_midtok_html ch m;
	  output_string ch " "
	end;
      output_ltree_html cx ch c stmh sknh
  | BiL(x,m,vll,c) ->
      let subp = Hashtbl.mem subscript x in
      let supp = Hashtbl.mem superscript x in
      let setinbd = List.exists (fun (xl,o) -> match o with None -> false | Some(i,_) -> i = AscSet) vll in
      let setsubqbd = List.exists (fun (xl,o) -> match o with None -> false | Some(i,_) -> i = AscSubeq) vll in
      let wrap1 = wrap_href_special ch
                   (if x = "fun" then
                      (if setinbd || setsubqbd then !setlamnotationhrefstack else [])
                    else if x = "forall" || x = "exists" then
                      []
                    else
                      hashtbl_find_or_nil bindernotationhrefstack x)
      in
      let wrap2 = wrap_href_special ch
                    (if x = "fun" then
                       (if setinbd || setsubqbd then !setlamnotationhrefstack else [])
                     else if x = "forall" then
                       (if setinbd then ["In_notation"] else if setsubqbd then ["Subq_notation"] else [])
                     else
                       hashtbl_find_or_nil bindernotationhrefstack x)
      in
      wrap1
        (fun () ->
          output_name_html ch x);
      if subp then output_string ch "<sub>" else if supp then output_string ch "<sup>";
      List.iter
	(fun (xl,o) ->
	  output_char ch '(';
	  output_names_html ch xl;
	  begin
	    match o with
	    | None -> ()
	    | Some(i,b) ->
               wrap2
                 (fun () ->
		   output_asckind_html ch i);
	       output_ltree_html cx ch b stmh sknh
	  end;
	  output_char ch ')';
	)
	vll;
      if subp then
	output_string ch "</sub>"
      else if supp then
	output_string ch "</sup>"
      else
	output_midtok_html ch m;
      output_ltree_html cx ch c stmh sknh
  | PreoL(x,a) ->
      wrap_href_special ch (hashtbl_find_or_nil prefixnotationhrefstack x)
        (fun () ->
          output_name_html ch x);
      output_char ch ' ';
      output_ltree_html cx ch a stmh sknh
  | PostoL(x,a) ->
      output_ltree_html cx ch a stmh sknh;
      output_char ch ' ';
      wrap_href_special ch (hashtbl_find_or_nil postinfixnotationhrefstack x)
        (fun () ->
          output_name_html ch x)
  | InfoL(x,a,b) ->
      begin
	if match x with InfNam(y) -> Hashtbl.mem subscript y | _ -> false then
	  begin
	    output_ltree_html cx ch a stmh sknh;
	    output_string ch "<sub>";
	    output_ltree_html cx ch b stmh sknh;
	    output_string ch "</sub>";
	  end
	else if match x with InfNam(y) -> Hashtbl.mem superscript y | _ -> false then
	  begin
	    output_ltree_html cx ch a stmh sknh;
	    output_string ch "<sup>";
	    output_ltree_html cx ch b stmh sknh;
	    output_string ch "</sup>";
	  end
	else
	  begin
	    output_ltree_html cx ch a stmh sknh;
	    output_char ch ' ';
            begin
              match x with
              | InfNam(xn) ->
                 wrap_href_special ch (hashtbl_find_or_nil postinfixnotationhrefstack xn)
                   (fun () ->
	             output_infixop_html ch x);
              | InfSet(_) -> output_infixop_html ch x
            end;
	    output_char ch ' ';
	    output_ltree_html cx ch b stmh sknh
	  end
      end
  | ImplopL(a,b) ->
      output_ltree_html cx ch a stmh sknh;
      output_char ch ' ';
      output_ltree_html cx ch b stmh sknh
  | SepL(x,i,a,b) ->
      wrap_href_special ch !sepnotationhrefstack
        (fun () ->
          output_char ch '{');
      output_name_html ch x;
      wrap_href_special ch !sepnotationhrefstack
        (fun () ->
          output_plain_setinfixop_html ch i);
      output_ltree_html cx ch a stmh sknh;
      wrap_href_special ch !sepnotationhrefstack
        (fun () ->
          output_char ch '|');
      output_ltree_html cx ch b stmh sknh;
      wrap_href_special ch !sepnotationhrefstack
        (fun () ->
          output_char ch '}');
  | RepL(x,i,a,b) ->
      wrap_href_special ch !replnotationhrefstack
        (fun () ->
          output_char ch '{');
      output_ltree_html cx ch a stmh sknh;
      wrap_href_special ch !replnotationhrefstack
        (fun () ->
          output_char ch '|');
      output_name_html ch x;
      wrap_href_special ch !replnotationhrefstack
        (fun () ->
          output_plain_setinfixop_html ch i);
      output_ltree_html cx ch b stmh sknh;
      wrap_href_special ch !replnotationhrefstack
        (fun () ->
          output_char ch '}');
  | SepRepL(x,i,a,b,c) ->
      wrap_href_special ch !replsepnotationhrefstack
        (fun () ->
          output_char ch '{');
      output_ltree_html cx ch a stmh sknh;
      wrap_href_special ch !replsepnotationhrefstack
        (fun () ->
          output_char ch '|');
      output_name_html ch x;
      wrap_href_special ch !replsepnotationhrefstack
        (fun () ->
          output_plain_setinfixop_html ch i);
      output_ltree_html cx ch b stmh sknh;
      wrap_href_special ch !replsepnotationhrefstack
        (fun () ->
          output_string ch ", ");
      output_ltree_html cx ch c stmh sknh;
      wrap_href_special ch !replsepnotationhrefstack
        (fun () ->
          output_char ch '}');
  | SetEnumL([]) ->
      wrap_href_special2 ch !setenumnotationhrefstack !setenum0notationhrefstack
        (fun () ->
          output_char ch '{';
          output_char ch '}');
  | SetEnumL(a::bl) ->
      let wrap =
        match List.length bl with
        | 0 -> wrap_href_special2 ch !setenumnotationhrefstack !setenum1notationhrefstack
        | 1 -> wrap_href_special2 ch !setenumnotationhrefstack !setenum2notationhrefstack
        | _ -> wrap_href_special ch !setenumnotationhrefstack
      in
      wrap (fun () -> output_char ch '{');
      output_ltree_html cx ch a stmh sknh;
	List.iter
	  (fun b ->
            wrap (fun () -> output_char ch ',');
	    output_ltree_html cx ch b stmh sknh)
	  bl;
      wrap (fun () -> output_char ch '}');
  | MTupleL(a,bl) ->
      output_char ch '[';
      output_ltree_html cx ch a stmh sknh;
      List.iter
	(fun b ->
	  output_char ch ',';
	  output_ltree_html cx ch b stmh sknh;
	)
	bl;
      output_char ch ']';
  | ParenL(a,[]) ->
      output_char ch '(';
      output_ltree_html cx ch a stmh sknh;
      output_char ch ')';
  | ParenL(a,b::cl) ->
      wrap_href_special ch !tuplenotationhrefstack
        (fun () ->
          output_char ch '(');
      output_ltree_html cx ch a stmh sknh;
      List.iter
	(fun c ->
	  output_char ch ',';
	  output_ltree_html cx ch c stmh sknh;
	)
	(b::cl);
      wrap_href_special ch !tuplenotationhrefstack
        (fun () ->
          output_char ch ')');
  | IfThenElseL(a,b,c) ->
      wrap_href_special ch !ifnotationhrefstack
        (fun () ->
          output_string ch "<span class='keyword'>if</span> ");
      output_ltree_html cx ch a stmh sknh;
      wrap_href_special ch !ifnotationhrefstack
        (fun () ->
          output_string ch " <span class='keyword'>then</span> ");
      output_ltree_html cx ch b stmh sknh;
      wrap_href_special ch !ifnotationhrefstack
        (fun () ->
          output_string ch " <span class='keyword'>else</span> ");
      output_ltree_html cx ch c stmh sknh

let output_docitem_html cx ch ditem stmh sknh =
  match ditem with
  | Author(x,yl) -> ()
  | Title(x) -> ()
  | Salt(x) -> ()
  | Opaque(_) -> ()
  | Transparent(_) -> ()
  | Treasure(x) ->
      Printf.fprintf ch "\n$%s\n" x;
  | ShowProofTerms(_) -> ()
  | Section(x) ->
     copy_head_notationhashtbl postinfixnotationhrefstack;
     copy_head_notationhashtbl prefixnotationhrefstack;
     copy_head_notationhashtbl bindernotationhrefstack;
     copy_head_notationstack tuplenotationhrefstack;
     copy_head_notationstack ifnotationhrefstack;
     copy_head_notationstack setlamnotationhrefstack;
     copy_head_notationstack replnotationhrefstack;
     copy_head_notationstack sepnotationhrefstack;
     copy_head_notationstack replsepnotationhrefstack;
     copy_head_notationstack setenumnotationhrefstack;
     copy_head_notationstack setenum0notationhrefstack;
     copy_head_notationstack setenum1notationhrefstack;
     copy_head_notationstack setenum2notationhrefstack;
     copy_head_notationstack natnotationhrefstack;
     Printf.fprintf ch "<div class='section'>\n";
     Printf.fprintf ch "<div class='sectionbegin'>Beginning of Section <b>%s</b></div>\n" x 
  | End(x) ->
     pop_notationhashtbl postinfixnotationhrefstack;
     pop_notationhashtbl prefixnotationhrefstack;
     pop_notationhashtbl bindernotationhrefstack;
     pop_notationstack tuplenotationhrefstack;
     pop_notationstack ifnotationhrefstack;
     pop_notationstack setlamnotationhrefstack;
     pop_notationstack replnotationhrefstack;
     pop_notationstack sepnotationhrefstack;
     pop_notationstack replsepnotationhrefstack;
     pop_notationstack setenumnotationhrefstack;
     pop_notationstack setenum0notationhrefstack;
     pop_notationstack setenum1notationhrefstack;
     pop_notationstack setenum2notationhrefstack;
     pop_notationstack natnotationhrefstack;
     Printf.fprintf ch "<div class='sectionend'>End of Section <b>%s</b></div>\n" x;
     Printf.fprintf ch "</div>\n"
  | VarDecl(xl,i,a) ->
      output_string ch "<div class='vardecl'><span class='docitemkeyword'>Variable</span> <span class='ltree'>";
      List.iter
	(fun x ->
	  output_char ch ' ';
	  output_string ch x;
	)
	xl;
      output_asckind_html ch i;
      output_ltree_html cx ch a stmh sknh;
      output_string ch "</span></div>\n";
  | LetDecl(x,None,b) ->
      output_string ch "<div class='letdecl'><span class='docitemkeyword'>Let</span> <span class='ltree'>";
      output_string ch x;
      output_string ch " &#x225d; ";
      output_ltree_html cx ch b stmh sknh;
      output_string ch "</span></div>\n";
  | LetDecl(x,Some(i,a),b) ->
      output_string ch "<div class='letdecl'><span class='docitemkeyword'>Let</span> <span class='ltree'>";
      output_string ch x;
      output_string ch " ";
      output_asckind_html ch i;
      output_ltree_html cx ch a stmh sknh;
      output_string ch " &#x225d; ";
      output_ltree_html cx ch b stmh sknh;
      output_string ch "</span></div>\n";
  | HypDecl(x,b) ->
      output_string ch "<div class='hypdecl'><span class='docitemkeyword'>Hypothesis</span> <span class='ltree'>";
      output_string ch x;
      output_string ch " : ";
      output_ltree_html cx ch b stmh sknh;
      output_string ch "</span></div>\n";
  | PostInfixDecl(x,b,p,InfixNone) ->
      incr notationhrefcntr;
      Printf.fprintf ch "<div class='infixdecl'><a name='notation_%d'/><b>Notation</b>. We use <span class='ltree'>" !notationhrefcntr;
      output_name_html ch x;
      output_string ch "</span> as an infix operator with priority ";
      output_string ch (string_of_int p);
      output_string ch " and no associativity";
      output_string ch " corresponding to applying term <span class='ltree'>";
      output_ltree_html cx ch b stmh sknh;
      output_string ch "</span>.</div>\n";
      Hashtbl.replace postinfixnotationhrefstack x (Printf.sprintf "notation_%d" !notationhrefcntr::hashtbl_find_or_nil postinfixnotationhrefstack x);
  | PostInfixDecl(x,b,p,InfixLeft) ->
      incr notationhrefcntr;
      Printf.fprintf ch "<div class='infixdecl'><a name='notation_%d'/><b>Notation</b>. We use <span class='ltree'>" !notationhrefcntr;
      output_name_html ch x;
      output_string ch "</span> as an infix operator with priority ";
      output_string ch (string_of_int p);
      output_string ch " and which associates to the left";
      output_string ch " corresponding to applying term <span class='ltree'>";
      output_ltree_html cx ch b stmh sknh;
      output_string ch "</span>.</div>\n";
      Hashtbl.replace postinfixnotationhrefstack x (Printf.sprintf "notation_%d" !notationhrefcntr::hashtbl_find_or_nil postinfixnotationhrefstack x);
  | PostInfixDecl(x,b,p,InfixRight) ->
      incr notationhrefcntr;
      Printf.fprintf ch "<div class='infixdecl'><a name='notation_%d'/><b>Notation</b>. We use <span class='ltree'>" !notationhrefcntr;
      output_name_html ch x;
      output_string ch "</span> as an infix operator with priority ";
      output_string ch (string_of_int p);
      output_string ch " and which associates to the right";
      output_string ch " corresponding to applying term <span class='ltree'>";
      output_ltree_html cx ch b stmh sknh;
      output_string ch "</span>.</div>\n";
      Hashtbl.replace postinfixnotationhrefstack x (Printf.sprintf "notation_%d" !notationhrefcntr::hashtbl_find_or_nil postinfixnotationhrefstack x);
  | PostInfixDecl(x,b,p,Postfix) ->
      incr notationhrefcntr;
      Printf.fprintf ch "<div class='postfixdecl'><a name='notation_%d'/><b>Notation</b>. We use <span class='ltree'>" !notationhrefcntr;
      output_name_html ch x;
      output_string ch "</span> as a postfix operator with priority ";
      output_string ch (string_of_int p);
      output_string ch " corresponding to applying term <span class='ltree'>";
      output_ltree_html cx ch b stmh sknh;
      output_string ch "</span>.";
      output_string ch "</div>\n";
      Hashtbl.replace postinfixnotationhrefstack x (Printf.sprintf "notation_%d" !notationhrefcntr::hashtbl_find_or_nil postinfixnotationhrefstack x);
  | PrefixDecl(x,b,p) ->
      incr notationhrefcntr;
      Printf.fprintf ch "<div class='prefixdecl'><a name='notation_%d'/><b>Notation</b>. We use <span class='ltree'>" !notationhrefcntr;
      output_name_html ch x;
      output_string ch "</span> as a prefix operator with priority ";
      output_string ch (string_of_int p);
      output_string ch " corresponding to applying term <span class='ltree'>";
      output_ltree_html cx ch b stmh sknh;
      output_string ch "</span>.";
      output_string ch "</div>\n";
      Hashtbl.replace prefixnotationhrefstack x (Printf.sprintf "notation_%d" !notationhrefcntr::hashtbl_find_or_nil postinfixnotationhrefstack x);
  | BinderDecl(plus,comma,x,a,None) ->
      incr notationhrefcntr;
      Printf.fprintf ch "<div class='binderdecl'><a name='notation_%d'/><b>Notation</b>. We use <span class='ltree'>" !notationhrefcntr;
      output_name_html ch x;
      if plus then
	output_string ch " <i>x</i>...<i>y</i> [possibly with ascriptions] "
      else
	output_string ch " <i>x</i> [possibly with ascriptions] ";
      if comma then
	output_string ch " , <i>B</i> "
      else
	output_string ch " &#x21d2; <i>B</i>";
      output_string ch "</span> as a binder notation corresponding to a term constructed using <span class='ltree'>";
      output_ltree_html cx ch a stmh sknh;
      output_string ch "</span>.</div>\n";
      Hashtbl.replace bindernotationhrefstack x (Printf.sprintf "notation_%d" !notationhrefcntr::hashtbl_find_or_nil bindernotationhrefstack x);
  | BinderDecl(plus,comma,x,a,Some(b)) ->
      incr notationhrefcntr;
      Printf.fprintf ch "<div class='binderdecl'><a name='notation_%d'/><b>Notation</b>. We use <span class='ltree'>" !notationhrefcntr;
      output_name_html ch x;
      if plus then
	output_string ch " <i>x</i>...<i>y</i> [possibly with ascriptions] "
      else
	output_string ch " <i>x</i> [possibly with ascriptions] ";
      if comma then
	output_string ch " , <i>B</i> "
      else
	output_string ch " &#x21d2; <i>B</i> ";
      output_string ch "</span> as a binder notation corresponding to a term constructed using <span class='ltree'>";
      output_ltree_html cx ch a stmh sknh;
      output_string ch "</span> and handling  &#x2208; or &#x2286; ascriptions using <span class='ltree'>";
      output_ltree_html cx ch b stmh sknh;
      output_string ch "</span>.</div>\n";
      Hashtbl.replace bindernotationhrefstack x (Printf.sprintf "notation_%d" !notationhrefcntr::hashtbl_find_or_nil bindernotationhrefstack x);
  | NotationDecl(x,yl) ->
      let declare_tuple_notation = ref false in
      incr notationhrefcntr;
      Printf.fprintf ch "<div class='notationdecl'><a name='notation_%d'/><b>Notation</b>. " !notationhrefcntr;
      begin
	match x with
	| "IfThenElse" ->
	    begin
              ifnotationhrefstack := Printf.sprintf "notation_%d" !notationhrefcntr::!ifnotationhrefstack;
              if not (!setlamnotationhrefstack = []) then declare_tuple_notation := true;
	      match yl with
	      | [y] ->
		  output_string ch "<span class='ltree'><span class='keyword'>if</span> <i>cond</i> <span class='keyword'>then</span> <i>T</i> <span class='keyword'>else</span> <i>E</i></span> is notation corresponding to <span class='ltree'>";
		  output_string ch y;
		  output_string ch " <i>type</i> <i>cond</i> <i>T</i> <i>E</i></span> where <span class='ltree'><i>type</i></span> is the inferred type of <span class='ltree'><i>T</i></span>."
	      | _ ->
		  raise (Failure("Bad IfThenElse notation"))
	    end
	| "Repl" ->
	    begin
              replnotationhrefstack := Printf.sprintf "notation_%d" !notationhrefcntr::!replnotationhrefstack;
	      match yl with
	      | [y] ->
		  output_string ch "<span class='ltree'>{<i>B</i>| <i>x</i> &#x2208; <i>A</i>}</span> is notation for <span class='ltree'>";
		  output_name_whrefa_html cx ch y stmh sknh;
		  output_string ch " <i>A</i> (&#x03bb; <i>x</i> . <i>B</i>)</span>."
	      | _ ->
		  raise (Failure("Bad Repl notation"))
	    end
	| "Sep" ->
	    begin
              sepnotationhrefstack := Printf.sprintf "notation_%d" !notationhrefcntr::!sepnotationhrefstack;
	      match yl with
	      | [y] ->
		  output_string ch "<span class='ltree'>{<i>x</i> &#x2208; <i>A</i> | <i>B</i>}</span> is notation for <span class='ltree'>";
		  output_name_whrefa_html cx ch y stmh sknh;
		  output_string ch " <i>A</i> (&#x03bb; <i>x</i> . <i>B</i>)</span>."
	      | _ ->
		  raise (Failure("Bad Sep notation"))
	    end
	| "ReplSep" ->
	    begin
              replsepnotationhrefstack := Printf.sprintf "notation_%d" !notationhrefcntr::!replsepnotationhrefstack;
	      match yl with
	      | [y] ->
		  output_string ch "<span class='ltree'>{<i>B</i>| <i>x</i> &#x2208; <i>A</i>, <i>C</i>}</span> is notation for <span class='ltree'>";
		  output_name_whrefa_html cx ch y stmh sknh;
		  output_string ch " <i>A</i> (&#x03bb; <i>x</i> . <i>C</i>) (&#x03bb; <i>x</i> . <i>B</i>)</span>."
	      | _ ->
		  raise (Failure("Bad ReplSep notation"))
	    end
	| "SetEnum" ->
	    begin
              setenumnotationhrefstack := Printf.sprintf "notation_%d" !notationhrefcntr::!setenumnotationhrefstack;
	      output_string ch "We now use the set enumeration notation <span class='ltree'>{...,...,...}</span> in general. ";
	      let rec setenum_notation_expl_r i z yl =
		match yl with
		| [] ->
		    output_string ch "  If more than ";
		    if i = 1 then
		      output_string ch " element is "
		    else
		      output_string ch " elements are ";
		    output_string ch " given, then <span class='ltree'>";
		    output_name_whrefa_html cx ch z stmh sknh;
		    output_string ch "</span> is used to reduce to the case with one fewer elements."
		| (y::yr) ->
		    output_string ch "  If ";
		    output_string ch (string_of_int i);
		    if i = 1 then
		      output_string ch " element is "
		    else
		      output_string ch " elements are ";
		    output_string ch " given, then <span class='ltree'>";
		    output_name_whrefa_html cx ch z stmh sknh;
		    output_string ch "</span> is used to form the corresponding term.";
		    setenum_notation_expl_r (i+1) y yr
	      in
	      match yl with
	      | (y::yr) ->
		  setenum_notation_expl_r 0 y yr
	      | _ ->
		  raise (Failure("Bad SetEnum notation"))
	    end
	| "SetEnum0" ->
	    begin
              setenum0notationhrefstack := Printf.sprintf "notation_%d" !notationhrefcntr::!setenum0notationhrefstack;
	      match yl with
	      | [y] ->
		  output_string ch "<span class='ltree'>{}</span> is notation for <span class='ltree'>";
		  output_name_whrefa_html cx ch y stmh sknh;
		  output_string ch "</span>.";
	      | _ ->
		  raise (Failure("Bad SetEnum0 notation"))
	    end
	| "SetEnum1" ->
	    begin
              setenum1notationhrefstack := Printf.sprintf "notation_%d" !notationhrefcntr::!setenum1notationhrefstack;
	      match yl with
	      | [y] ->
		  output_string ch "<span class='ltree'>{<i>x</i>}</span> is notation for <span class='ltree'>";
		  output_name_whrefa_html cx ch y stmh sknh;
		  output_string ch " <i>x</i></span>.";
	      | _ ->
		  raise (Failure("Bad SetEnum1 notation"))
	    end
	| "SetEnum2" ->
	    begin
              setenum2notationhrefstack := Printf.sprintf "notation_%d" !notationhrefcntr::!setenum2notationhrefstack;
	      match yl with
	      | [y] ->
		  output_string ch "<span class='ltree'>{<i>x</i>,<i>y</i>}</span> is notation for <span class='ltree'>";
		  output_name_whrefa_html cx ch y stmh sknh;
		  output_string ch " <i>x</i> <i>y</i></span>.";
	      | _ ->
		  raise (Failure("Bad SetEnum2 notation"))
	    end
	| "Nat" ->
	    begin
              natnotationhrefstack := Printf.sprintf "notation_%d" !notationhrefcntr::!natnotationhrefstack;
	      match yl with
	      | [y0;yS] ->
		  output_string ch "Natural numbers 0,1,2,... are notation for the terms formed using <span class='ltree'>";
		  output_name_whrefa_html cx ch y0 stmh sknh;
		  output_string ch "</span> as 0 and forming successors with <span class='ltree'>";
		  output_name_whrefa_html cx ch yS stmh sknh;
		  output_string ch "</span>."
	      | _ ->
		  raise (Failure("Bad Nat notation"))
	    end
	| "SetLam" ->
	    begin
              setlamnotationhrefstack := Printf.sprintf "notation_%d" !notationhrefcntr::!setlamnotationhrefstack;
              if not (!ifnotationhrefstack = []) then declare_tuple_notation := true;
	      match yl with
	      | [y] ->
		  output_string ch "<span class='ltree'>&#x03bb; <i>x</i> &#x2208; <i>A</i> &#x21d2; <i>B</i></span> is notation for the set <span class='ltree'>";
		  output_name_whrefa_html cx ch y stmh sknh;
		  output_string ch " <i>A</i> (&#x03bb; <i>x</i> : set &#x21d2; <i>B</i>)</span>.";
	      | _ ->
		  raise (Failure("Bad SetLam notation"))
	    end
	| "SetImplicitOp" ->
	    begin
	      match yl with
	      | [y] ->
		  output_string ch "When <span class='ltree'><i>x</i></span> is a set, a term <span class='ltree'><i>x</i> <i>y</i></span> is notation for <span class='ltree'>";
		  output_name_whrefa_html cx ch y stmh sknh;
		  output_string ch " <i>x</i> <i>y</i></span>.";
	      | _ ->
		  raise (Failure("Bad SetImplicitOp notation"))
	    end
	| _ -> raise (Failure("Unknown notation " ^ x))
      end;
      output_string ch "</div>\n";
      if !declare_tuple_notation then
        begin
          incr notationhrefcntr;
          tuplenotationhrefstack := Printf.sprintf "notation_%d" !notationhrefcntr::!tuplenotationhrefstack;
          Printf.fprintf ch "<div class='notationdecl'><a name='notation_%d'/><b>Notation</b>. " !notationhrefcntr;
          output_string ch "We now use n-tuple notation (<i>a<sub>0</sub></i>,...,<i>a<sub>n-1</sub></i>) for n &geq; 2 for &#x03bb; i &#x2208; <i>n</i> . <span class='keyword'>if</span> i = 0 <span class='keyword'>then</span> <i>a<sub>0</sub></i> <span class='keyword'>else</span> ... if</span> i = <i>n-2</i> <span class='keyword'>then</span> <i>a<sub>n-2</sub></i> <span class='keyword'>else</span> <i>a<sub>n-1</sub></i>.\n";
          output_string ch "</div>\n";
          
        end
  | UnicodeDecl(x,ul) -> ()
  | SuperscriptDecl(x) -> (*** I should say something about notation here, but at the moment it would need to be "If x is a binder, then we write its bound variables as a superscript. If x is an infix operator, then we omit the operator and write the second argument as a superscript." ***)
      ()
  | SubscriptDecl(x) -> (*** I should say something about notation here, but at the moment it would need to be "If x is a binder, then we write its bound variables as a subscript. If x is an infix operator, then we omit the operator and write the second argument as a subscript." ***)
      ()
  | ParamDecl(x,a) ->
      Hashtbl.add localhrefh x ();
      output_string ch "<a name='";
      output_string ch (url_friendly_name x);
      output_string ch "'/>";
      output_string ch "<div class='paramdecl'><b>Primitive</b>. The name <span class='ltree'>";
      output_name_whrefa_html cx ch x stmh sknh;
      output_string ch "</span> is a term of type <span class='ltree'>";
      output_ltree_html cx ch a stmh sknh;
      output_string ch "</span>.</div>\n";
      begin
        try
          let xpfgtmroot = Hashtbl.find pfgtmroot x in
          let xpfgobjid = Hashtbl.find pfgobjid x in
          Printf.fprintf ch "<div class='pfglinks'>In Proofgold the corresponding term root is <a href='%s?b=%s'>%s...</a> and object id is <a href='%s?b=%s'>%s...</a></div>\n" !explorerurl xpfgtmroot (String.sub xpfgtmroot 0 6) !explorerurl xpfgobjid (String.sub xpfgobjid 0 6);
        with Not_found -> ()
      end;
      begin
	if x = "In" then
	  begin
	    output_string ch "<div class='infixdecl'><a name='In_notation'/><b>Notation</b>. We use <span class='ltree'>&#x2208;</span>";
	    output_string ch "</span> as an infix operator with priority 500";
	    output_string ch " and no associativity";
	    output_string ch " corresponding to applying term <span class='ltree'>";
	    output_name_whrefa_html cx ch x stmh sknh;
	    output_string ch "</span>. Furthermore, we may write <span class='ltree'>&#x2200; <I>x</I> &#x2208; <I>A</I>, <I>B</I></span> to mean <span class='ltree'>&#x2200; <I>x</I> : ";
	    output_name_whrefa_html cx ch "set" stmh sknh;
	    output_string ch ", <I>x</I> &#x2208; <I>A</I> &#x2192; <I>B</I></span>.</div>\n";
	  end
      end;
      begin
	if x = "Subq" then
	  begin
	    output_string ch "<div class='infixdecl'><a name='Subq_notation'/><b>Notation</b>. We use <span class='ltree'>&#x2286;</span>";
	    output_string ch "</span> as an infix operator with priority 500";
	    output_string ch " and no associativity";
	    output_string ch " corresponding to applying term <span class='ltree'>";
	    output_name_whrefa_html cx ch x stmh sknh;
	    output_string ch "</span>. Furthermore, we may write <span class='ltree'>&#x2200; <I>x</I> &#x2286; <I>A</I>, <I>B</I></span> to mean <span class='ltree'>&#x2200; <I>x</I> : ";
	    output_name_whrefa_html cx ch "set" stmh sknh;
	    output_string ch ", <I>x</I> &#x2286; <I>A</I> &#x2192; <I>B</I></span>.</div>\n";
	  end
      end
  | ParamHash(x,h,_) -> ()
  | DefDecl(x,None,a) ->
      Hashtbl.add localhrefh x ();
      output_string ch "<a name='";
      output_string ch (url_friendly_name x);
      output_string ch "'/>";
      output_string ch "<div class='defdecl'><b>Definition.</b> We define <span class='ltree'>";
      output_name_whrefa_html cx ch x stmh sknh;
      output_string ch "</span> to be <span class='ltree'>";
      output_ltree_html cx ch a stmh sknh;
      output_string ch "</span>.</div>\n";
      begin
        try
          let xpfgtmroot = Hashtbl.find pfgtmroot x in
          let xpfgobjid = Hashtbl.find pfgobjid x in
          Printf.fprintf ch "<div class='pfglinks'>In Proofgold the corresponding term root is <a href='%s?b=%s'>%s...</a> and object id is <a href='%s?b=%s'>%s...</a></div>\n" !explorerurl xpfgtmroot (String.sub xpfgtmroot 0 6) !explorerurl xpfgobjid (String.sub xpfgobjid 0 6);
        with Not_found -> ()
      end;
      begin
	if x = "Subq" then
	  begin
	    output_string ch "<div class='infixdecl'><a name='Subq_notation'/><b>Notation</b>. We use <span class='ltree'>&#x2286;</span>";
	    output_string ch "</span> as an infix operator with priority 500";
	    output_string ch " and no associativity";
	    output_string ch " corresponding to applying term <span class='ltree'>";
	    output_name_whrefa_html cx ch x stmh sknh;
	    output_string ch "</span>. Furthermore, we may write <span class='ltree'>&#x2200; <I>x</I> &#x2286; <I>A</I>, <I>B</I></span> to mean <span class='ltree'>&#x2200; <I>x</I> : ";
	    output_name_whrefa_html cx ch "set" stmh sknh;
	    output_string ch ", <I>x</I> &#x2286; <I>A</I> &#x2192; <I>B</I></span>.</div>\n";
	  end
      end
  | DefDecl(x,Some b,a) ->
      Hashtbl.add localhrefh x ();
      output_string ch "<a name='";
      output_string ch (url_friendly_name x);
      output_string ch "'/>";
      output_string ch "<div class='defdecl'><b>Definition.</b> We define <span class='ltree'>";
      output_name_whrefa_html cx ch x stmh sknh;
      output_string ch "</span> to be <span class='ltree'>";
      output_ltree_html cx ch a stmh sknh;
      output_string ch "</span> of type <span class='ltree'>";
      output_ltree_html cx ch b stmh sknh;
      output_string ch "</span>.</div>\n";
      begin
        try
          let xpfgtmroot = Hashtbl.find pfgtmroot x in
          let xpfgobjid = Hashtbl.find pfgobjid x in
          Printf.fprintf ch "<div class='pfglinks'>In Proofgold the corresponding term root is <a href='%s?b=%s'>%s...</a> and object id is <a href='%s?b=%s'>%s...</a></div>\n" !explorerurl xpfgtmroot (String.sub xpfgtmroot 0 6) !explorerurl xpfgobjid (String.sub xpfgobjid 0 6);
        with Not_found -> ()
      end;
      begin
	if x = "Subq" then
	  begin
	    output_string ch "<div class='infixdecl'><a name='Subq_notation'/><b>Notation</b>. We use <span class='ltree'>&#x2286;</span>";
	    output_string ch "</span> as an infix operator with priority 500";
	    output_string ch " and no associativity";
	    output_string ch " corresponding to applying term <span class='ltree'>";
	    output_name_whrefa_html cx ch x stmh sknh;
	    output_string ch "</span>. Furthermore, we may write <span class='ltree'>&#x2200; <I>x</I> &#x2286; <I>A</I>, <I>B</I></span> to mean <span class='ltree'>&#x2200; <I>x</I> : ";
	    output_name_whrefa_html cx ch "set" stmh sknh;
	    output_string ch ", <I>x</I> &#x2286; <I>A</I> &#x2192; <I>B</I></span>.</div>\n";
	  end
      end
  | AxDecl(x,a) ->
      Hashtbl.add localhrefh x ();
      output_string ch "<a name='";
      output_string ch (url_friendly_name x);
      output_string ch "'/>";
      output_string ch "<div class='axdecl'><b>Axiom.</b> (<span class='ltree'>";
      output_name_whrefa_html cx ch x stmh sknh;
      output_string ch "</span>) We take the following as an axiom:\n<div class='axiomprop'><span class='ltree'>";
      output_ltree_html cx ch a stmh sknh;
      output_string ch "</span></div></div>\n";
      begin
        try
          let xpfgtmroot = Hashtbl.find pfgtmroot x in
          let xpfgpropid = Hashtbl.find pfgpropid x in
          Printf.fprintf ch "<div class='pfglinks'>In Proofgold the corresponding term root is <a href='%s?b=%s'>%s...</a> and proposition id is <a href='%s?b=%s'>%s...</a></div>\n" !explorerurl xpfgtmroot (String.sub xpfgtmroot 0 6) !explorerurl xpfgpropid (String.sub xpfgpropid 0 6);
        with Not_found -> ()
      end;
  | ThmDecl(c,x,a) ->
      Hashtbl.add localhrefh x ();
      output_string ch "<a name='";
      output_string ch (url_friendly_name x);
      output_string ch "'/>";
      output_string ch "<div class='thmandproof'><div class='thmdecl'><b>";
      output_string ch c;
      output_string ch ".</b> (<span class='ltree'>";
      output_name_whrefa_html cx ch x stmh sknh;
      output_string ch "</span>) <div class='thmprop'><span class='ltree'>";
      output_ltree_html cx ch a stmh sknh;
      output_string ch "</span></div></div>\n";
      begin
        try
          let xpfgtmroot = Hashtbl.find pfgtmroot x in
          let xpfgpropid = Hashtbl.find pfgpropid x in
          Printf.fprintf ch "<div class='pfglinks'>In Proofgold the corresponding term root is <a href='%s?b=%s'>%s...</a> and proposition id is <a href='%s?b=%s'>%s...</a></div>\n" !explorerurl xpfgtmroot (String.sub xpfgtmroot 0 6) !explorerurl xpfgpropid (String.sub xpfgpropid 0 6);
        with Not_found -> ()
      end;
      incr thmcount;
      Buffer.reset pftext;
      Printf.fprintf ch "<div id='pf%d' class='proof'><div class='proofpres' onclick='g(this)'><b>Proof:</b><br/>" !thmcount

let text_row_col txt =
  let nli = ref 1 in
  let nch = ref 0 in
  let maxch = ref 0 in
  for i = 0 to String.length txt - 1 do
    let c = txt.[i] in
    if c = '\n' then
      (incr nli; nch := 0)
    else
      (incr nch; maxch := max !maxch !nch)
  done;
  (!nli,!maxch)

let rec output_comma_list_str ch f y yl =
  match yl with
  | [] -> Printf.fprintf ch " and "; f y
  | z::yr -> f y; Printf.fprintf ch ", "; output_comma_list_str ch f z yr

let output_pftacitem_html cx ch pftac stmh sknh laststructact =
  match pftac with
  | PfStruct i when i < 4 ->
      if laststructact = 1 then
	output_string ch "<div class='subproof'>"
      else if laststructact = 2 then
	output_string ch "</div>\n<div class='subproof'>"
      else if laststructact = 3 then
	output_string ch "</div>\n";
  | PfStruct 4 -> output_string ch "<div class='subproof'>";
  | PfStruct 5 -> output_string ch "</div>";
  | PfStruct _ -> ()
  | Exact(a) ->
      output_string ch "<div class='exact'>An <span class='pftackeyword'>exact</span> proof term for the current goal is <span class='ltree'>";
      output_ltree_html cx ch a stmh sknh;
      output_string ch "</span>.</div>\n"
  | LetTac(xl,None) ->
      output_string ch "<div class='lettac'><span class='pftackeyword'>Let</span> <span class='ltree'>";
      output_comma_names_html ch xl;
      output_string ch "</span> be given.</div>\n"
  | LetTac(xl,Some a) ->
      output_string ch "<div class='lettac'><span class='pftackeyword'>Let</span> <span class='ltree'>";
      output_comma_names_html ch xl;
      output_string ch "</span> of type <span class='ltree'>";
      output_ltree_html cx ch a stmh sknh;
      output_string ch "</span> be given.</div>\n"
  | SetTac(x,None,a) ->
      output_string ch "<div class='settac'><span class='pftackeyword'>Set</span> <span class='ltree'>";
      output_string ch x;
      output_string ch "</span> to be the term <span class='ltree'>";
      output_ltree_html cx ch a stmh sknh;
      output_string ch "</span>.</div>\n"
  | SetTac(x,Some(b),a) ->
      output_string ch "<div class='settac'><span class='pftackeyword'>Set</span> <span class='ltree'>";
      output_string ch x;
      output_string ch "</span> to be the term <span class='ltree'>";
      output_ltree_html cx ch a stmh sknh;
      output_string ch "</span> of type <span class='ltree'>";
      output_ltree_html cx ch b stmh sknh;
      output_string ch "</span>.</div>\n"
  | AssumeTac(xl,None) ->
      output_string ch "<div class='assumetac'><span class='pftackeyword'>Assume</span> <span class='ltree'>";
      output_names_html ch xl;
      output_string ch "</span>.</div>\n"
  | AssumeTac(xl,Some a) ->
      output_string ch "<div class='assumetac'><span class='pftackeyword'>Assume</span> <span class='ltree'>";
      output_names_html ch xl;
      output_string ch "</span>: <span class='ltree'>";
      output_ltree_html cx ch a stmh sknh;
      output_string ch "</span>.</div>\n"
  | ApplyTac(a) ->
      output_string ch "<div class='applytac'><span class='pftackeyword'>Apply</span> <span class='ltree'>";
      output_ltree_html cx ch a stmh sknh;
      output_string ch "</span> to the current goal.</div>\n"
  | ClaimTac(x,a) ->
      output_string ch "<div class='claimtac'>We prove the intermediate <span class='pftackeyword'>claim</span> <span class='ltree'>";
      output_name_html ch x;
      output_string ch "</span>: <span class='ltree'>";
      output_ltree_html cx ch a stmh sknh;
      output_string ch "</span>.</div>\n"
  | ProveTac(a,bl) ->
      output_string ch "<div class='provetac'>We will <span class='pftackeyword'>prove</span> ";
      output_ltree_html cx ch a stmh sknh;
      List.iter (fun b ->
	output_string ch ", <span class='ltree'>";
	output_ltree_html cx ch b stmh sknh;
	output_string ch "</span>")
	bl;
      output_string ch ".</div>\n"
  | CasesTac(a,cl) ->
      raise (Failure("Cases tactic not yet implemented"))
  | WitnessTac(a) ->
      output_string ch "<div class='witnesstac'>We use <span class='ltree'>";
      output_ltree_html cx ch a stmh sknh;
      output_string ch "</span> to <span class='pftackeyword'>witness</span> the existential quantifier.</div>\n";
  | RewriteTac(s,a,il) ->
      output_string ch "<div class='rewritetac'><span class='pftackeyword'>rewrite</span> the current goal using <span class='ltree'>";
      output_ltree_html cx ch a stmh sknh;
      output_string ch "</span>";
      if s then
	output_string ch " (from right to left)"
      else
	output_string ch " (from left to right)";
      begin
	match il with
	| [] -> ()
	| [i] ->
	    output_string ch " at position ";
	    output_string ch (string_of_int i);
	| (i::j::kl) ->
	    output_string ch " at positions ";
	    let rec posl i j kl =
	      match kl with
	      | k::kr ->
		  output_string ch (string_of_int i);
		  output_string ch ", ";
		  posl j k kr
	      | [] ->
		  output_string ch (string_of_int i);
		  output_string ch " and ";
		  output_string ch (string_of_int j)
	    in
	    posl i j kl
      end;
      output_string ch ".</div>\n"
  | SpecialTac(x,[]) -> Printf.fprintf ch "<div>Use %s.</div>\n" x
  | SpecialTac(x,y::yl) ->
     Printf.fprintf ch "<div>Use %s with " x;
     output_comma_list_str ch (fun a -> output_ltree_html cx ch a stmh sknh) y yl;
     Printf.fprintf ch ".</div>\n";
  | Qed ->
      output_string ch "&#x220e;\n";
      Printf.fprintf ch "</div><div id='pf%dcode' class='proofcodehidden'>\n" !thmcount;
      Printf.fprintf ch "<input type='hidden' id='pf%dcodeline' value='%d'/><input type='hidden' id='pf%dcodechar' value='%d'/>\n" !thmcount !pflinestart !thmcount !pfcharstart;
      if (String.length !currtmid > 0) then (Printf.fprintf ch "<input type='hidden' id='pf%dcodetmid' value='%s'/>\n" !thmcount !currtmid; currtmid := "");
      (*      
      let pftxt = Buffer.contents pftext in
      let (rowcount,colcount) = text_row_col pftxt in
Printf.fprintf ch "<textarea id='pf%dcodetext' rows=%d cols=%d>%s</textarea><br/><input type='button' value='Recheck' onclick='h(this)'/>\n" !thmcount rowcount colcount pftxt;
      Printf.fprintf ch "<div id='pf%dcoderesp' class='proofcoderesp'/></div>" !thmcount; *)
      output_string ch "</div></div></div>\n"
  | Admitted ->
      if laststructact < 0 then
	begin
	  output_string ch "<div class='admitted'>The rest of the proof is missing.</div>\n";
	  Printf.fprintf ch "</div><div id='pf%dcode' class='proofcodehidden'>\n" !thmcount;
	  Printf.fprintf ch "<input type='hidden' id='pf%dcodeline' value='%d'/><input type='hidden' id='pf%dcodechar' value='%d'/>\n" !thmcount !pflinestart !thmcount !pfcharstart;
	  if (String.length !currtmid > 0) then (Printf.fprintf ch "<input type='hidden' id='pf%dcodetmid' value='%s'/>\n" !thmcount !currtmid; currtmid := "");
	  Printf.fprintf ch "<textarea id='pf%dcodetext' rows=5 cols=80></textarea><br/><input type='button' value='Check' onclick='h(this)'/>\n" !thmcount; (*** just leave this one blank instead of just putting 'Admitted' ***)
	  Printf.fprintf ch "<div id='pf%dcoderesp' class='proofcoderesp'/></div>" !thmcount;
	  output_string ch "</div></div></div>\n"
	end
      else
	begin
	  output_string ch "<div class='admitted'>The rest of the proof is missing.</div>\n";
	  Printf.fprintf ch "</div><div id='pf%dcode' class='proofcodehidden'>\n" !thmcount;
	  Printf.fprintf ch "<input type='hidden' id='pf%dcodeline' value='%d'/><input type='hidden' id='pf%dcodechar' value='%d'/>\n" !thmcount !pflinestart !thmcount !pfcharstart;
	  if (String.length !currtmid > 0) then (Printf.fprintf ch "<input type='hidden' id='pf%dcodetmid' value='%s'/>\n" !thmcount !currtmid; currtmid := "");
	  let pftxt = Buffer.contents pftext in
	  let (rowcount,colcount) = text_row_col pftxt in
	  Printf.fprintf ch "<textarea id='pf%dcodetext' rows=%d cols=%d>%s</textarea><br/><input type='button' value='Check' onclick='h(this)'/>\n" !thmcount rowcount colcount pftxt;
	  Printf.fprintf ch "<div id='pf%dcoderesp' class='proofcoderesp'/></div>" !thmcount;
	  output_string ch "</div></div></div>\n"
	end
  | Admit ->
      output_string ch "<div class='admit'>The rest of this subproof is missing.</div>"
  | Aby(xl) ->
     match List.rev xl with
     | [] -> Printf.fprintf ch "<div class='aby'>The rest of this subproof can be completed by an ATP.</div>\n"
     | [x] -> Printf.fprintf ch "<div class='aby'>The rest of this subproof can be completed by an ATP using %s.</div>\n" x
     | [x;y] -> Printf.fprintf ch "<div class='aby'>The rest of this subproof can be completed by an ATP using %s and %s.</div>\n" y x
     | x::y::zr ->
        Printf.fprintf ch "<div class='aby'>The rest of this subproof can be completed by an ATP using ";
        List.iter (fun z -> Printf.fprintf ch "%s, " z) (List.rev zr);
        Printf.fprintf ch "%s and %s.</div>\n" y x

let rec stp_html_string_1 a p =
  match a with
  | TpVar 0 -> "&#x3b1;"
  | TpVar 1 -> "&#x3b2;"
  | TpVar 2 -> "&#x3b3;"
  | TpVar i -> raise (Failure("bad type var"))
  | Set -> "set"
  | Prop -> "prop"
  | Ar(b,c) when p -> "(" ^ stp_html_string_1 b true ^ " &#x2192; " ^ stp_html_string_1 c false ^ ")"
  | Ar(b,c) -> stp_html_string_1 b true ^ " &#x2192; " ^ stp_html_string_1 c false
      
let stp_html_string a = stp_html_string_1 a false

                                          (** latex **)
let latex_code x =
  let b = Buffer.create 10 in
  for i = 0 to String.length x - 1 do
    let cc = Char.code (x.[i]) in
    Buffer.add_char b (Char.chr (97 + (cc land 15)));
    Buffer.add_char b (Char.chr (97 + ((cc lsr 4) land 15)))
  done;
  Buffer.contents b
  
let output_name_latex_code ch x =
  for i = 0 to String.length x - 1 do
    let cc = Char.code (x.[i]) in
    Printf.fprintf ch "%c%c" (Char.chr (97 + (cc land 15))) (Char.chr (97 + ((cc lsr 4) land 15)))
  done
  
let output_unicode_latex ch u =
  output_string ch "\\uni";
  output_name_latex_code ch u

let esc_latex x =
  let b = Buffer.create 10 in
  for i = 0 to (String.length x) - 1 do
    let c = x.[i] in
    if c = '_' then Buffer.add_char b '\\';
    Buffer.add_char b c
  done;
  Buffer.contents b

let output_name_latex ch x =
  try
    let ul = Hashtbl.find unicode x in
    List.iter (fun u -> output_unicode_latex ch u) ul
  with Not_found -> output_string ch (esc_latex x)

let output_asckind_latex ch k =
  match k with
  | AscTp -> output_string ch " : "
  | AscSet -> output_string ch " \\in "
  | AscSubeq -> output_string ch " \\subseteq "

let output_setinfixop_latex ch k =
  match k with
  | InfMem -> output_string ch " \\in "
  | InfSubq -> output_string ch " \\subseteq "

let output_infixop_latex ch i =
  match i with
  | InfNam(x) -> output_name_latex ch x
  | InfSet(k) -> output_setinfixop_latex ch k

let output_midtok_latex ch m =
  if m = "," then
    output_string ch " . "
(*    output_string ch " , " *)
  else if m = "=>" then
    output_string ch " . "
(*    output_string ch " \\Rightarrow " *)
  else
    output_string ch m

let output_names_latex ch xl =
  match xl with
  | [] -> ()
  | (x::yl) ->
      output_name_latex ch x;
      List.iter
	(fun y ->
	  output_char ch ' ';
	  output_name_latex ch y)
	yl

let rec output_comma_names_latex ch xl =
  match xl with
  | [] -> ()
  | [x] ->
      output_name_latex ch x;
  | [x;y] ->
      output_name_latex ch x;
      output_string ch " and ";
      output_name_latex ch y;
  | (x::yl) ->
      output_name_latex ch x;
      output_string ch ", ";
      output_comma_names_latex ch yl

let globallatexname : (string,unit) Hashtbl.t = Hashtbl.create 100
let latexref : (string,string * string) Hashtbl.t = Hashtbl.create 100
                                                   
(*** <a> causes css problems in combination with <span> for some reason, so only call this if it's declaring the name (not inside an lterm).
    Eh, it also insists on screwing up the font. I've just changed all anchors to have the math friendly font. How annoying. ***)
let output_name_whref_latex ch x stmh sknh : unit =
  if x = "prop" then
    output_string ch "o"
  else if x = "set" then
    output_string ch "\\iota"
  else if x = "SType" then
    output_string ch "{\\mathsf{Type}}"
  else if List.mem x ["alpha";"beta";"gamma";"delta";"eta";"lambda"] then
    Printf.fprintf ch "\\%s" x
  else if Hashtbl.mem globallatexname x then
    begin
      Printf.fprintf ch "\\mname{%s}" (esc_latex x);
    end
  else
    try
      let (k,r) = Hashtbl.find latexref x in
      if k = "Hyp" then
        Printf.fprintf ch "(%s)" r
      else if k = "Axiom" then
        Printf.fprintf ch "{\\mbox{Axiom~%s}}" r
      else if k = "Theorem" then
        Printf.fprintf ch "{\\mbox{Theorem~%s}}" r
      else
        output_string ch (esc_latex x)
    with Not_found ->
      output_string ch (esc_latex x)

let output_name_whrefa_latex ch x stmh sknh =
  output_name_whref_latex ch x stmh sknh

let rec output_ltree_latex ch a stmh sknh : unit =
  output_string ch "{";
  output_ltree_latex_c ch a stmh sknh;
  output_string ch "}"
and output_ltree_latex_c ch a stmh sknh : unit =
  match a with
  | ByteL(x) -> Printf.fprintf ch "\\x%02x" x
  | StringL(x) -> output_char ch '"'; output_string ch x; output_char ch '"'
  | QStringL(x) -> output_char ch '?'; output_string ch x; output_char ch '?'
  | NaL(x) ->
      output_name_whref_latex ch x stmh sknh
  | NuL(b,x,None,None) ->
      begin
	if b then output_char ch '-';
	output_string ch x;
      end
  | NuL(b,x,Some y,None) ->
      begin
	if b then output_char ch '-';
	output_string ch x;
	output_char ch '.';
	output_string ch y;
      end
  | NuL(b,x,None,Some z) ->
      begin
	if b then output_char ch '-';
	output_string ch x;
	output_char ch 'E';
	output_string ch z;
      end
  | NuL(b,x,Some y,Some z) ->
      begin
	if b then output_char ch '-';
	output_string ch x;
	output_char ch '.';
	output_string ch y;
	output_char ch 'E';
	output_string ch z;
      end
  | LeL(x,None,a,c) ->
      begin
	output_string ch "\\mlet{";
	output_string ch x;
	output_string ch "}{";
	output_ltree_latex ch a stmh sknh;
	output_string ch "}{";
	output_ltree_latex ch c stmh sknh;
	output_string ch "}";
      end
  | LeL(x,Some(i,b),a,c) ->
      begin
	output_string ch "\\mleta{";
	output_string ch x;
	output_string ch "}{";
	output_asckind_latex ch i;
	output_string ch "}{";
	output_ltree_latex ch b stmh sknh;
	output_string ch "}{";
	output_ltree_latex ch a stmh sknh;
	output_string ch "}{";
	output_ltree_latex ch c stmh sknh;
	output_string ch "}";
      end
  | LeML(x,yl,a,c) ->
      begin
	output_string ch "\\mletm{";
	output_string ch x;
	List.iter
	  (fun y ->
	    output_char ch ',';
	    output_string ch y)
	  yl;
	output_string ch "}{";
	output_ltree_latex ch a stmh sknh;
	output_string ch "}{";
	output_ltree_latex ch c stmh sknh;
	output_string ch "}";
      end
  | BiL(x,m,[(xl,o)],c) ->
      let subp = Hashtbl.mem subscript x in
      let supp = Hashtbl.mem superscript x in
      output_name_latex ch x;
      output_char ch ' ';
      if subp then output_string ch "_{" else if supp then output_string ch "^{" else if not (Hashtbl.mem unicode x) then output_string ch " ";
      output_names_latex ch xl;
      begin
	match o with
	| None -> ()
	| Some(i,b) ->
	    output_asckind_latex ch i;
	    output_ltree_latex ch b stmh sknh
      end;
      if subp then
	output_string ch "}"
      else if supp then
	output_string ch "}"
      else
	begin
	  output_midtok_latex ch m;
	  output_string ch " "
	end;
      output_ltree_latex ch c stmh sknh;
  | BiL(x,m,vll,c) ->
      let subp = Hashtbl.mem subscript x in
      let supp = Hashtbl.mem superscript x in
      output_name_latex ch x;
      output_char ch ' ';
      if subp then output_string ch "_{" else if supp then output_string ch "^{";
      List.iter
	(fun (xl,o) ->
	  output_char ch '(';
	  output_names_latex ch xl;
	  begin
	    match o with
	    | None -> ()
	    | Some(i,b) ->
		output_asckind_latex ch i;
		output_ltree_latex ch b stmh sknh
	  end;
	  output_char ch ')')
	vll;
      if subp then
	output_string ch "}"
      else if supp then
	output_string ch "}"
      else
	output_midtok_latex ch m;
      output_ltree_latex ch c stmh sknh;
  | PreoL(x,a) ->
      output_string ch "\\pre";
      output_name_latex_code ch x;
      output_char ch '{';
      output_ltree_latex ch a stmh sknh;
      output_char ch '}';
  | PostoL(x,a) ->
      output_string ch "\\post";
      output_name_latex_code ch x;
      output_char ch '{';
      output_ltree_latex ch a stmh sknh;
      output_char ch '}';
  | InfoL(x,a,b) ->
      begin
	if match x with InfNam(y) -> Hashtbl.mem subscript y | _ -> false then
	  begin
	    output_ltree_latex ch a stmh sknh;
	    output_string ch "_{";
	    output_ltree_latex ch b stmh sknh;
	    output_string ch "}";
	  end
	else if match x with InfNam(y) -> Hashtbl.mem superscript y | _ -> false then
	  begin
	    output_ltree_latex ch a stmh sknh;
	    output_string ch "^{";
	    output_ltree_latex ch b stmh sknh;
	    output_string ch "}";
	  end
	else
	  begin
	    output_ltree_latex ch a stmh sknh;
            output_infixop_latex ch x;
	    output_ltree_latex ch b stmh sknh;
	  end
      end
  | ImplopL(a,b) ->
      output_ltree_latex ch a stmh sknh;
      output_char ch '~';
      output_ltree_latex ch b stmh sknh
  | SepL(x,i,a,b) ->
      output_string ch "\\{";
      output_name_latex ch x;
      output_setinfixop_latex ch i;
      output_ltree_latex ch a stmh sknh;
      output_char ch '|';
      output_ltree_latex ch b stmh sknh;
      output_string ch "\\}";
  | RepL(x,i,a,b) ->
      output_string ch "\\{";
      output_ltree_latex ch a stmh sknh;
      output_char ch '|';
      output_name_latex ch x;
      output_setinfixop_latex ch i;
      output_ltree_latex ch b stmh sknh;
      output_string ch "\\}";
  | SepRepL(x,i,a,b,c) ->
      output_string ch "\\{";
      output_ltree_latex ch a stmh sknh;
      output_char ch '|';
      output_name_latex ch x;
      output_setinfixop_latex ch i;
      output_ltree_latex ch b stmh sknh;
      output_string ch ", ";
      output_ltree_latex ch c stmh sknh;
      output_string ch "\\}";
  | SetEnumL([]) ->
      output_string ch "\\{\\}";
  | SetEnumL(a::bl) ->
     output_string ch "\\{";
     output_ltree_latex ch a stmh sknh;
     List.iter
       (fun b ->
	 output_char ch ',';
	 output_ltree_latex ch b stmh sknh;
       )
       bl;
     output_string ch "\\}";
  | MTupleL(a,bl) ->
      output_char ch '[';
      output_ltree_latex ch a stmh sknh;
      List.iter
	(fun b ->
	  output_char ch ',';
	  output_ltree_latex ch b stmh sknh;
	)
	bl;
      output_char ch ']';
  | ParenL(a,[]) ->
      output_char ch '(';
      output_ltree_latex ch a stmh sknh;
      output_char ch ')';
  | ParenL(a,b::cl) ->
      output_char ch '(';
      output_ltree_latex ch a stmh sknh;
      List.iter
	(fun c ->
	  output_char ch ',';
	  output_ltree_latex ch c stmh sknh;
	)
	(b::cl);
      output_char ch ')';
  | IfThenElseL(a,b,c) ->
      output_string ch "\\mif{";
      output_ltree_latex ch a stmh sknh;
      output_string ch "}{";
      output_ltree_latex ch b stmh sknh;
      output_string ch "}{";
      output_ltree_latex ch c stmh sknh;
      output_string ch "}"

let output_docitem_latex ch ditem stmh sknh =
  match ditem with
  | Author(x,yl) -> ()
  | Title(x) ->
     Printf.fprintf ch "\\chapter{%s}\n\n" x
  | Salt(x) -> ()
  | Opaque(_) -> ()
  | Transparent(_) -> ()
  | Treasure(x) -> ()
  | ShowProofTerms(_) -> ()
  | Section(_) -> ()
  | End(_) -> ()
  | VarDecl(xl,i,a) ->
     output_string ch "Let $";
     List.iter
       (fun x ->
	 output_char ch ' ';
	 output_string ch x;
       )
       xl;
     output_asckind_latex ch i;
     output_ltree_latex ch a stmh sknh;
     output_string ch "$ be given.\n";
  | LetDecl(x,None,b) ->
     output_string ch "Let $";
     output_string ch x;
     output_string ch "$ be $";
     output_ltree_latex ch b stmh sknh;
     output_string ch "$.\n";
  | LetDecl(x,Some(i,a),b) ->
     output_string ch "Let $";
     output_string ch x;
     output_asckind_latex ch i;
     output_ltree_latex ch a stmh sknh;
     output_string ch "$ be $";
     output_ltree_latex ch b stmh sknh;
     output_string ch "$.\n";
  | HypDecl(x,b) ->
     Hashtbl.add latexref x ("Hyp",Printf.sprintf "\\ref{hyp:%s}" (latex_code x));
     output_string ch "Assume the following.\n";
     output_string ch "\\begin{equation}\n";
     output_ltree_latex ch b stmh sknh;
     output_string ch "\\label{hyp:";
     output_name_latex_code ch x;
     output_string ch "}\n";
     output_string ch "\\end{equation}\n";
  | PostInfixDecl(x,b,p,InfixNone) ->
      output_string ch "{\\bf{Notation.}} We use $\\inf";
      output_name_latex_code ch x;
      output_string ch "$ as an infix operator ";
      output_string ch " corresponding to applying term $";
      output_ltree_latex ch b stmh sknh;
      output_string ch "$.\n";
  | PostInfixDecl(x,b,p,InfixLeft) ->
      output_string ch "{\\bf{Notation.}} We use $\\inf";
      output_name_latex_code ch x;
      output_string ch "$ as a left associative infix operator ";
      output_string ch " corresponding to applying term $";
      output_ltree_latex ch b stmh sknh;
      output_string ch "$.\n";
  | PostInfixDecl(x,b,p,InfixRight) ->
      output_string ch "{\\bf{Notation.}} We use $\\inf";
      output_name_latex_code ch x;
      output_string ch "$ as a right associative infix operator ";
      output_string ch " corresponding to applying term $";
      output_ltree_latex ch b stmh sknh;
      output_string ch "$.\n";
  | PostInfixDecl(x,b,p,Postfix) ->
      output_string ch "{\\bf{Notation.}} We use $\\post";
      output_name_latex_code ch x;
      output_string ch "{-}$ as a postfix operator ";
      output_string ch " corresponding to applying term $";
      output_ltree_latex ch b stmh sknh;
      output_string ch "$.\n";
  | PrefixDecl(x,b,p) ->
      output_string ch "{\\bf{Notation.}} We use $\\pre";
      output_name_latex_code ch x;
      output_string ch "{-}$ as a prefix operator ";
      output_string ch " corresponding to applying term $";
      output_ltree_latex ch b stmh sknh;
      output_string ch "$.\n";
  | BinderDecl(plus,comma,x,a,None) ->
     output_string ch "{\\bf{Notation.}} We use $\\bind";
     output_name_latex_code ch x;
     if plus then
       output_string ch " x,\\ldots,y "
     else
       output_string ch " x ";
     output_string ch " . ";
     output_string ch "$ as a binder notation corresponding to a term constructed using $";
     output_ltree_latex ch a stmh sknh;
     output_string ch "$.\n";
  | BinderDecl(plus,comma,x,a,Some(b)) ->
     output_string ch "{\\bf{Notation.}} We use $\\bind";
     output_name_latex_code ch x;
     if plus then
       output_string ch " x,\\ldots,y "
     else
       output_string ch " x ";
     output_string ch " . ";
     output_string ch "$ as a binder notation corresponding to a term constructed using $";
     output_ltree_latex ch a stmh sknh;
     output_string ch "$ and handling $\\in$ or $\\subseteq$ ascriptions using $\n";
     output_ltree_latex ch b stmh sknh;
     output_string ch "$.\n";
  | NotationDecl(x,yl) ->
      output_string ch "{\\bf{Notation.}} ";
      begin
	match x with
	| "IfThenElse" ->
	    begin
	      match yl with
	      | [y] ->
		  output_string ch "% <span class='ltree'><span class='keyword'>if</span> <i>cond</i> <span class='keyword'>then</span> <i>T</i> <span class='keyword'>else</span> <i>E</i></span> is notation corresponding to <span class='ltree'>";
		  output_string ch y;
		  output_string ch " <i>type</i> <i>cond</i> <i>T</i> <i>E</i></span> where <span class='ltree'><i>type</i></span> is the inferred type of <span class='ltree'><i>T</i></span>.\n"
	      | _ ->
		  raise (Failure("Bad IfThenElse notation"))
	    end
	| "Repl" ->
	    begin
	      match yl with
	      | [y] ->
		  output_string ch "% <span class='ltree'>{<i>B</i>| <i>x</i> &#x2208; <i>A</i>}</span> is notation for <span class='ltree'>";
		  output_name_whref_latex ch y stmh sknh;
		  output_string ch " <i>A</i> (&#x03bb; <i>x</i> . <i>B</i>)</span>.\n"
	      | _ ->
		  raise (Failure("Bad Repl notation"))
	    end
	| "Sep" ->
	    begin
	      match yl with
	      | [y] ->
		  output_string ch "% <span class='ltree'>{<i>x</i> &#x2208; <i>A</i> | <i>B</i>}</span> is notation for <span class='ltree'>";
		  output_name_whref_latex ch y stmh sknh;
		  output_string ch " <i>A</i> (&#x03bb; <i>x</i> . <i>B</i>)</span>.\n"
	      | _ ->
		  raise (Failure("Bad Sep notation"))
	    end
	| "ReplSep" ->
	    begin
	      match yl with
	      | [y] ->
		  output_string ch "% <span class='ltree'>{<i>B</i>| <i>x</i> &#x2208; <i>A</i>, <i>C</i>}</span> is notation for <span class='ltree'>";
		  output_name_whref_latex ch y stmh sknh;
		  output_string ch " <i>A</i> (&#x03bb; <i>x</i> . <i>C</i>) (&#x03bb; <i>x</i> . <i>B</i>)</span>.\n"
	      | _ ->
		  raise (Failure("Bad ReplSep notation"))
	    end
	| "SetEnum" ->
	    begin
	      output_string ch "% We now use the set enumeration notation <span class='ltree'>{...,...,...}</span> in general. ";
	      let rec setenum_notation_expl_r i z yl =
		match yl with
		| [] ->
		    output_string ch "  If more than ";
		    if i = 1 then
		      output_string ch " element is "
		    else
		      output_string ch " elements are ";
		    output_string ch " given, then <span class='ltree'>";
		    output_name_whref_latex ch z stmh sknh;
		    output_string ch "</span> is used to reduce to the case with one fewer elements.\n"
		| (y::yr) ->
		    output_string ch "  If ";
		    output_string ch (string_of_int i);
		    if i = 1 then
		      output_string ch " element is "
		    else
		      output_string ch " elements are ";
		    output_string ch " given, then <span class='ltree'>";
		    output_name_whref_latex ch z stmh sknh;
		    output_string ch "</span> is used to form the corresponding term.";
		    setenum_notation_expl_r (i+1) y yr
	      in
	      match yl with
	      | (y::yr) ->
		  setenum_notation_expl_r 0 y yr
	      | _ ->
		  raise (Failure("Bad SetEnum notation"))
	    end
	| "SetEnum0" ->
	    begin
	      match yl with
	      | [y] ->
		  output_string ch "% <span class='ltree'>{}</span> is notation for <span class='ltree'>";
		  output_name_whref_latex ch y stmh sknh;
		  output_string ch "</span>.\n";
	      | _ ->
		  raise (Failure("Bad SetEnum0 notation"))
	    end
	| "SetEnum1" ->
	    begin
	      match yl with
	      | [y] ->
		  output_string ch "% <span class='ltree'>{<i>x</i>}</span> is notation for <span class='ltree'>";
		  output_name_whref_latex ch y stmh sknh;
		  output_string ch " <i>x</i></span>.\n";
	      | _ ->
		  raise (Failure("Bad SetEnum1 notation"))
	    end
	| "SetEnum2" ->
	    begin
	      match yl with
	      | [y] ->
		  output_string ch "% <span class='ltree'>{<i>x</i>,<i>y</i>}</span> is notation for <span class='ltree'>";
		  output_name_whref_latex ch y stmh sknh;
		  output_string ch " <i>x</i> <i>y</i></span>.\n";
	      | _ ->
		  raise (Failure("Bad SetEnum2 notation"))
	    end
	| "Nat" ->
	    begin
	      match yl with
	      | [y0;yS] ->
		  output_string ch "% Natural numbers 0,1,2,... are notation for the terms formed using <span class='ltree'>";
		  output_name_whref_latex ch y0 stmh sknh;
		  output_string ch "</span> as 0 and forming successors with <span class='ltree'>";
		  output_name_whref_latex ch yS stmh sknh;
		  output_string ch "</span>.\n"
	      | _ ->
		  raise (Failure("Bad Nat notation"))
	    end
	| "SetLam" ->
	    begin
	      match yl with
	      | [y] ->
		  output_string ch "% <span class='ltree'>&#x03bb; <i>x</i> &#x2208; <i>A</i> &#x21d2; <i>B</i></span> is notation for the set <span class='ltree'>";
		  output_name_whref_latex ch y stmh sknh;
		  output_string ch " <i>A</i> (&#x03bb; <i>x</i> : set &#x21d2; <i>B</i>)</span>.\n";
	      | _ ->
		  raise (Failure("Bad SetLam notation"))
	    end
	| "SetImplicitOp" ->
	    begin
	      match yl with
	      | [y] ->
		  output_string ch "% When <span class='ltree'><i>x</i></span> is a set, a term <span class='ltree'><i>x</i> <i>y</i></span> is notation for <span class='ltree'>";
		  output_name_whref_latex ch y stmh sknh;
		  output_string ch " <i>x</i> <i>y</i></span>.\n";
	      | _ ->
		  raise (Failure("Bad SetImplicitOp notation"))
	    end
	| _ -> raise (Failure("Unknown notation " ^ x))
      end
  | UnicodeDecl(x,ul) -> ()
  | SuperscriptDecl(x) -> (*** I should say something about notation here, but at the moment it would need to be "If x is a binder, then we write its bound variables as a superscript. If x is an infix operator, then we omit the operator and write the second argument as a superscript." ***) (** If this is wrong, fix it by hand. **)
     Printf.fprintf ch "{\\bf{Notation.}} We use superscripts as notation for the infix operator $\\inf";
     output_name_latex_code ch x;
     Printf.fprintf ch "$.\n";
  | SubscriptDecl(x) -> (*** I should say something about notation here, but at the moment it would need to be "If x is a binder, then we write its bound variables as a subscript. If x is an infix operator, then we omit the operator and write the second argument as a subscript." ***) (** If this is wrong, fix it by hand. **)
     Printf.fprintf ch "{\\bf{Notation.}} We use subscripts as notation for the infix operator $\\inf";
     output_name_latex_code ch x;
     Printf.fprintf ch "$.\n";
  | ParamDecl(x,a) ->
     Hashtbl.add globallatexname x ();
      output_string ch "{\\bf{Primitive.}} The name $";
      output_name_whrefa_latex ch x stmh sknh;
      output_string ch "$ is a term of type $";
      output_ltree_latex ch a stmh sknh;
      output_string ch "$.\n";
      (**
      begin
	if x = "In" then
	  begin
	    output_string ch "{\\bf{Notation.}} We use <span class='ltree'>&#x2208;</span>";
	    output_string ch "</span> as an infix operator with priority 500";
	    output_string ch " and no associativity";
	    output_string ch " corresponding to applying term <span class='ltree'>";
	    output_name_whrefa_latex ch x stmh sknh;
	    output_string ch "</span>. Furthermore, we may write <span class='ltree'>&#x2200; <I>x</I> &#x2208; <I>A</I>, <I>B</I></span> to mean <span class='ltree'>&#x2200; <I>x</I> : ";
	    output_name_whrefa_latex ch "set" stmh sknh;
	    output_string ch ", <I>x</I> &#x2208; <I>A</I> &#x2192; <I>B</I></span>.</div>\n";
	  end
      end;
      begin
	if x = "Subq" then
	  begin
	    output_string ch "<div class='infixdecl'><a name='Subq_notation'/><b>Notation</b>. We use <span class='ltree'>&#x2286;</span>";
	    output_string ch "</span> as an infix operator with priority 500";
	    output_string ch " and no associativity";
	    output_string ch " corresponding to applying term <span class='ltree'>";
	    output_name_whrefa_latex ch x stmh sknh;
	    output_string ch "</span>. Furthermore, we may write <span class='ltree'>&#x2200; <I>x</I> &#x2286; <I>A</I>, <I>B</I></span> to mean <span class='ltree'>&#x2200; <I>x</I> : ";
	    output_name_whrefa_latex ch "set" stmh sknh;
	    output_string ch ", <I>x</I> &#x2286; <I>A</I> &#x2192; <I>B</I></span>.</div>\n";
	  end
      end
       **)
  | ParamHash(x,h,_) -> ()
  | DefDecl(x,None,a) ->
     Hashtbl.add globallatexname x ();
     Printf.fprintf ch "\\begin{definition}\\label{def:";
     output_name_latex_code ch x;
     Printf.fprintf ch "}\nWe define $";
     output_name_whrefa_latex ch x stmh sknh;
     output_string ch "$ to be $";
     output_ltree_latex ch a stmh sknh;
     output_string ch "$.\n\\end{definition}\n";
     (**
     begin
	if x = "Subq" then
	  begin
	    output_string ch "<div class='infixdecl'><a name='Subq_notation'/><b>Notation</b>. We use <span class='ltree'>&#x2286;</span>";
	    output_string ch "</span> as an infix operator with priority 500";
	    output_string ch " and no associativity";
	    output_string ch " corresponding to applying term <span class='ltree'>";
	    output_name_whrefa_latex ch x stmh sknh;
	    output_string ch "</span>. Furthermore, we may write <span class='ltree'>&#x2200; <I>x</I> &#x2286; <I>A</I>, <I>B</I></span> to mean <span class='ltree'>&#x2200; <I>x</I> : ";
	    output_name_whrefa_latex ch "set" stmh sknh;
	    output_string ch ", <I>x</I> &#x2286; <I>A</I> &#x2192; <I>B</I></span>.</div>\n";
	  end
      end
      **)
  | DefDecl(x,Some b,a) ->
     Hashtbl.add globallatexname x ();
     Printf.fprintf ch "\\begin{definition}\\label{def:";
     output_name_latex_code ch x;
     Printf.fprintf ch "}\nWe define $";
     output_name_whrefa_latex ch x stmh sknh;
     output_string ch "$ to be $";
     output_ltree_latex ch a stmh sknh;
     output_string ch "$ of type $";
     output_ltree_latex ch b stmh sknh;
     output_string ch "$.\n\\end{definition}\n";
  | AxDecl(x,a) ->
     Hashtbl.add latexref x ("Axiom",Printf.sprintf "\\ref{ax:%s}" (latex_code x));
     Printf.fprintf ch "\\begin{axiom}\\label{ax:";
     output_name_latex_code ch x;
     Printf.fprintf ch "} $";
     output_ltree_latex ch a stmh sknh;
     output_string ch "$.\n\\end{axiom}\n";
  | ThmDecl(c,x,a) ->
     Hashtbl.add latexref x ("Theorem",Printf.sprintf "\\ref{thm:%s}" (latex_code x));
     Printf.fprintf ch "\\begin{theorem}\\label{thm:";
     output_name_latex_code ch x;
     Printf.fprintf ch "} $";
     output_ltree_latex ch a stmh sknh;
     output_string ch "$.\n\\end{theorem}\n";
     incr thmcount;
     Printf.fprintf ch "\\begin{proof}\n"

let output_pftacitem_latex ch pftac stmh sknh laststructact =
  match pftac with
  | PfStruct i when i < 4 ->
      if laststructact = 1 then
	output_string ch "{"
      else if laststructact = 2 then
	output_string ch "}\n{"
      else if laststructact = 3 then
	output_string ch "}\n";
  | PfStruct 4 -> output_string ch "{";
  | PfStruct 5 -> output_string ch "}";
  | PfStruct _ -> ()
  | Exact(a) ->
      output_string ch "Exact $";
      output_ltree_latex ch a stmh sknh;
      output_string ch "$.\n"
  | LetTac(xl,None) ->
      output_string ch "Let $";
      output_comma_names_latex ch xl;
      output_string ch "$ be given.\n"
  | LetTac(xl,Some a) ->
      output_string ch "Let $";
      output_comma_names_latex ch xl;
      output_string ch "$ of type $";
      output_ltree_latex ch a stmh sknh;
      output_string ch "$ be given.\n"
  | SetTac(x,None,a) ->
      output_string ch "Set $";
      output_string ch x;
      output_string ch "$ to be the term $";
      output_ltree_latex ch a stmh sknh;
      output_string ch "$.\n"
  | SetTac(x,Some(b),a) ->
      output_string ch "Set $";
      output_string ch x;
      output_string ch "$ to be the term $";
      output_ltree_latex ch a stmh sknh;
      output_string ch "$ of type $";
      output_ltree_latex ch b stmh sknh;
      output_string ch "$.\n"
  | AssumeTac(xl,None) ->
      output_string ch "Assume $";
      output_names_latex ch xl;
      output_string ch "$.\n"
  | AssumeTac(xl,Some a) ->
      output_string ch "Assume $";
      output_names_latex ch xl;
      output_string ch "$: $";
      output_ltree_latex ch a stmh sknh;
      output_string ch "$.\n"
  | ApplyTac(a) ->
      output_string ch "Apply $";
      output_ltree_latex ch a stmh sknh;
      output_string ch "$ to the current goal.\n"
  | ClaimTac(x,a) ->
      output_string ch "We prove the intermediate claim $";
      output_name_latex ch x;
      output_string ch "$: $";
      output_ltree_latex ch a stmh sknh;
      output_string ch "$.\n"
  | ProveTac(a,bl) ->
      output_string ch "We will prove $";
      output_ltree_latex ch a stmh sknh;
      List.iter (fun b ->
	output_string ch ", ";
	output_ltree_latex ch b stmh sknh)
	bl;
      output_string ch "$.\n"
  | CasesTac(a,cl) ->
      raise (Failure("Cases tactic not yet implemented"))
  | WitnessTac(a) ->
      output_string ch "We use $";
      output_ltree_latex ch a stmh sknh;
      output_string ch "$ to witness the existential quantifier.\n";
  | RewriteTac(s,a,il) ->
      output_string ch "Rewrite the current goal using $";
      output_ltree_latex ch a stmh sknh;
      output_string ch "$";
      if s then
	output_string ch " (from right to left)"
      else
	output_string ch " (from left to right)";
      begin
	match il with
	| [] -> ()
	| [i] ->
	    output_string ch " at position ";
	    output_string ch (string_of_int i);
	| (i::j::kl) ->
	    output_string ch " at positions ";
	    let rec posl i j kl =
	      match kl with
	      | k::kr ->
		  output_string ch (string_of_int i);
		  output_string ch ", ";
		  posl j k kr
	      | [] ->
		  output_string ch (string_of_int i);
		  output_string ch " and ";
		  output_string ch (string_of_int j)
	    in
	    posl i j kl
      end;
      output_string ch ".\n"
  | SpecialTac(x,[]) -> Printf.fprintf ch "Use %s.\n" x
  | SpecialTac(x,y::yl) ->
     Printf.fprintf ch "Use %s with " x;
     output_comma_list_str ch (fun a -> output_ltree_latex ch a stmh sknh) y yl;
     Printf.fprintf ch ".\n";
  | Qed ->
     Printf.fprintf ch "\\end{proof}\n\n"
  | Admitted ->
     Printf.fprintf ch "{\\it{Proof unfinished.}}\n\\end{proof}\n\n"
  | Admit ->
     Printf.fprintf ch "{\\it{Subproof unfinished.}}\n"
  | Aby(xl) ->
     match List.rev xl with
     | [] -> Printf.fprintf ch "{\\it{Subproof by an ATP.}}\n"
     | [x] -> Printf.fprintf ch "{\\it{Subproof by an ATP using %s.}}\n" x
     | [x;y] -> Printf.fprintf ch "{\\it{Subproof by an ATP using %s and %s.}}\n" y x
     | x::y::zr ->
        Printf.fprintf ch "{\\it{Subproof by an ATP using ";
        List.iter (fun z -> Printf.fprintf ch "%s, " z) (List.rev zr);
        Printf.fprintf ch "%s and %s.}}\n" y x

let rec tp_pfgset_str a =
  match a with
  | TpVar(j) -> raise (Failure (Printf.sprintf "no polymorphism allowed in pfg: tp %d" j))
  | Prop -> "Prop"
  | Set -> "set"
  | Ar(a,b) -> Printf.sprintf "TpArr %s %s" (tp_pfgset_str a) (tp_pfgset_str b)

let rec tp_pfgsyn_str a =
  match a with
  | TpVar(j) -> raise (Failure (Printf.sprintf "no polymorphism allowed in pfg: tp %d" j))
  | Prop -> "Prop"
  | Set -> "syn"
  | Ar(a,b) -> Printf.sprintf "TpArr %s %s" (tp_pfgsyn_str a) (tp_pfgsyn_str b)

let tp_pfg_str a =
  match !pfgtheory with
  | HF -> tp_pfgset_str a
  | Egal -> tp_pfgset_str a
  | Mizar -> tp_pfgset_str a
  | HOAS -> tp_pfgsyn_str a
  | SetMM -> tp_pfgset_str a

let pfgvarcount = ref 0
let pfghypcount = ref 0
let pfgtmh : (string,string) Hashtbl.t = Hashtbl.create 100
let pfgtmhh : (string,Hash.hashval) Hashtbl.t = Hashtbl.create 100
let pfgknh : (string,string) Hashtbl.t = Hashtbl.create 100
let pfgknhh : (string,Hash.hashval) Hashtbl.t = Hashtbl.create 100
let pfgbvarh : (tm,string) Hashtbl.t = Hashtbl.create 100
let pfgpfbvarh : (pf,string) Hashtbl.t = Hashtbl.create 100
let pfghyph : (pf,string) Hashtbl.t = Hashtbl.create 100

let pfgex (a,m) = Mathdatapfg.Ex(a,Mathdatapfg.Ap(Mathdatapfg.uptrm m 0 1,Mathdatapfg.DB(0)))
let pfgeq (a,m,n) = Mathdatapfg.Eq(a,m,n)
  
let rec to_mathdatapfghf_tm m =
  match m with
  | DB(i) -> Mathdatapfg.DB(i)
  | TmH(h) ->
     begin
       try
         Mathdatapfg.Prim(Hashtbl.find pfghfprim h)
       with Not_found ->
         (try Mathdatapfg.TmH(Hashtbl.find pfgtmhh h) with Not_found -> raise (Failure (Printf.sprintf "Could not find corresponding obj id for TmH(%s)\n" h)))
     end
  | Prim(j) ->
     begin
       try
         let s = List.nth ["Eps";"In";"Empty";"Union";"Power";"Repl";"UnivOf"] j in
         if (s = "Eps" || s = "UnivOf") then raise (Failure "disallowed prims for pfg hf");
         if s = "In" then
           Mathdatapfg.Prim(7)
         else if s = "Empty" then
           Mathdatapfg.Prim(9)
         else if s = "Union" then
           Mathdatapfg.Prim(10)
         else if s = "Power" then
           Mathdatapfg.Prim(11)
         else if s = "Repl" then
           Mathdatapfg.Prim(12)
         else
           raise (Failure "disallowed prims for pfg hf")
       with _ -> raise (Failure (Printf.sprintf "bad prim %d case for pfg hf" j))
     end
  | Ap(TpAp(TmH(h),a1),m1) when h = "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099" ->
     pfgex(to_mathdatapfghf_tp a1,to_mathdatapfghf_tm m1)
  | TpAp(TmH(h),a) when h = "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a" ->
     let a1 = to_mathdatapfghf_tp a in
     Mathdatapfg.Lam(a1,Mathdatapfg.Lam(a1,pfgeq(a1,Mathdatapfg.DB 1,Mathdatapfg.DB 0)))
  | Ap(TpAp(TmH(h),a),m1) when h = "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a" ->
     let a1 = to_mathdatapfghf_tp a in
     Mathdatapfg.Lam(a1,pfgeq(a1,to_mathdatapfghf_tm (tmshift 0 1 m1),Mathdatapfg.DB 0))
  | Ap(Ap(TpAp(TmH(h),a),m1),m2) when h = "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a" ->
     pfgeq(to_mathdatapfghf_tp a,to_mathdatapfghf_tm m1,to_mathdatapfghf_tm m2)
  | TpAp(TmH(h),a) when h = "7966a66a9bb198103c2a540ccd5ebebdff33c10843cc10eebfc98715e142989c" ->
     let a1 = to_mathdatapfghf_tp a in
     Mathdatapfg.Lam(a1,Mathdatapfg.Lam(a1,Mathdatapfg.Ap(Mathdatapfg.Prim(3),pfgeq(a1,Mathdatapfg.DB 1,Mathdatapfg.DB 0))))
  | Ap(TpAp(TmH(h),a),m1) when h = "7966a66a9bb198103c2a540ccd5ebebdff33c10843cc10eebfc98715e142989c" ->
     let a1 = to_mathdatapfghf_tp a in
     Mathdatapfg.Lam(a1,Mathdatapfg.Ap(Mathdatapfg.Prim(3),pfgeq(a1,to_mathdatapfghf_tm (tmshift 0 1 m1),Mathdatapfg.DB 0)))
  | Ap(Ap(TpAp(TmH(h),a),m1),m2) when h = "7966a66a9bb198103c2a540ccd5ebebdff33c10843cc10eebfc98715e142989c" ->
     Mathdatapfg.Ap(Mathdatapfg.Prim(3),pfgeq(to_mathdatapfghf_tp a,to_mathdatapfghf_tm m1,to_mathdatapfghf_tm m2))
  | TpAp(_,_) -> raise (Failure (Printf.sprintf "no polymorphism allowed in pfg: tm_pfghf %s" (tm_to_str m)))
  | Ap(m,n) -> Mathdatapfg.Ap(to_mathdatapfghf_tm m,to_mathdatapfghf_tm n)
  | Lam(a,m) -> Mathdatapfg.Lam(to_mathdatapfghf_tp a,to_mathdatapfghf_tm m)
  | Imp(m,n) -> Mathdatapfg.Imp(to_mathdatapfghf_tm m,to_mathdatapfghf_tm n)
  | All(a,m) -> Mathdatapfg.All(to_mathdatapfghf_tp a,to_mathdatapfghf_tm m)

let rec to_mathdatapfgegal_tm m =
  match m with
  | DB(i) -> Mathdatapfg.DB(i)
  | TmH(h) ->
     begin
       try
         Mathdatapfg.Prim(Hashtbl.find pfgegalprim h)
       with Not_found ->
         (try Mathdatapfg.TmH(Hashtbl.find pfgtmhh h) with Not_found -> raise (Failure (Printf.sprintf "Could not find corresponding obj id for TmH(%s)\n" h)))
     end
  | Prim(j) when j > 0 -> Mathdatapfg.Prim(j)
  | Prim(j) -> raise (Failure (Printf.sprintf "bad prim %d case for pfg egal" j))
  | Ap(TpAp(TmH(h),a1),m1) when h = "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099" ->
     pfgex(to_mathdatapfgegal_tp a1,to_mathdatapfgegal_tm m1)
  | TpAp(TmH(h),a) when h = "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a" ->
     let a1 = to_mathdatapfgegal_tp a in
     Mathdatapfg.Lam(a1,Mathdatapfg.Lam(a1,pfgeq(a1,Mathdatapfg.DB 1,Mathdatapfg.DB 0)))
  | Ap(TpAp(TmH(h),a),m1) when h = "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a" ->
     let a1 = to_mathdatapfgegal_tp a in
     Mathdatapfg.Lam(a1,pfgeq(a1,to_mathdatapfgegal_tm (tmshift 0 1 m1),Mathdatapfg.DB 0))
  | Ap(Ap(TpAp(TmH(h),a),m1),m2) when h = "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a" ->
     pfgeq(to_mathdatapfgegal_tp a,to_mathdatapfgegal_tm m1,to_mathdatapfgegal_tm m2)
  | TpAp(TmH(h),a) when h = "7966a66a9bb198103c2a540ccd5ebebdff33c10843cc10eebfc98715e142989c" ->
     let a1 = to_mathdatapfgegal_tp a in
     Mathdatapfg.Lam(a1,Mathdatapfg.Lam(a1,Mathdatapfg.Imp(pfgeq(a1,Mathdatapfg.DB 1,Mathdatapfg.DB 0),Mathdatapfg.All(Mathdatapfg.Prop,Mathdatapfg.DB(0)))))
  | Ap(TpAp(TmH(h),a),m1) when h = "7966a66a9bb198103c2a540ccd5ebebdff33c10843cc10eebfc98715e142989c" ->
     let a1 = to_mathdatapfgegal_tp a in
     Mathdatapfg.Lam(a1,Mathdatapfg.Imp(pfgeq(a1,to_mathdatapfgegal_tm (tmshift 0 1 m1),Mathdatapfg.DB 0),Mathdatapfg.All(Mathdatapfg.Prop,Mathdatapfg.DB(0))))
  | Ap(Ap(TpAp(TmH(h),a),m1),m2) when h = "7966a66a9bb198103c2a540ccd5ebebdff33c10843cc10eebfc98715e142989c" ->
     Mathdatapfg.Imp(pfgeq(to_mathdatapfgegal_tp a,to_mathdatapfgegal_tm m1,to_mathdatapfgegal_tm m2),Mathdatapfg.All(Mathdatapfg.Prop,Mathdatapfg.DB(0)))
  | TpAp(_,_) -> raise (Failure (Printf.sprintf "no polymorphism allowed in pfg: tm_pfgegal %s" (tm_to_str m)))
  | Ap(m,n) -> Mathdatapfg.Ap(to_mathdatapfgegal_tm m,to_mathdatapfgegal_tm n)
  | Lam(a,m) -> Mathdatapfg.Lam(to_mathdatapfgegal_tp a,to_mathdatapfgegal_tm m)
  | Imp(m,n) -> Mathdatapfg.Imp(to_mathdatapfgegal_tm m,to_mathdatapfgegal_tm n)
  | All(a,m) -> Mathdatapfg.All(to_mathdatapfgegal_tp a,to_mathdatapfgegal_tm m)

let rec to_mathdatapfgmiz_tm m =
  match m with
  | DB(i) -> Mathdatapfg.DB(i)
  | TmH(h) ->
     begin
       try
         Mathdatapfg.Prim(Hashtbl.find pfgmizprim h)
       with Not_found ->
         (try Mathdatapfg.TmH(Hashtbl.find pfgtmhh h) with Not_found -> raise (Failure (Printf.sprintf "Could not find corresponding obj id for TmH(%s)\n" h)))
     end
  | Prim(j) when j = 1 || j = 3 -> Mathdatapfg.Prim(j)
  | Prim(j) -> raise (Failure (Printf.sprintf "bad prim %d case for pfg miz" j))
  | Ap(TpAp(TmH(h),a1),m1) when h = "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099" ->
     pfgex(to_mathdatapfgmiz_tp a1,to_mathdatapfgmiz_tm m1)
  | TpAp(TmH(h),a) when h = "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a" ->
     let a1 = to_mathdatapfgmiz_tp a in
     Mathdatapfg.Lam(a1,Mathdatapfg.Lam(a1,pfgeq(a1,Mathdatapfg.DB 1,Mathdatapfg.DB 0)))
  | Ap(TpAp(TmH(h),a),m1) when h = "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a" ->
     let a1 = to_mathdatapfgmiz_tp a in
     Mathdatapfg.Lam(a1,pfgeq(a1,to_mathdatapfgmiz_tm (tmshift 0 1 m1),Mathdatapfg.DB 0))
  | Ap(Ap(TpAp(TmH(h),a),m1),m2) when h = "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a" ->
     pfgeq(to_mathdatapfgmiz_tp a,to_mathdatapfgmiz_tm m1,to_mathdatapfgmiz_tm m2)
  | TpAp(TmH(h),a) when h = "7966a66a9bb198103c2a540ccd5ebebdff33c10843cc10eebfc98715e142989c" ->
     let a1 = to_mathdatapfgmiz_tp a in
     Mathdatapfg.Lam(a1,Mathdatapfg.Lam(a1,Mathdatapfg.Imp(pfgeq(a1,Mathdatapfg.DB 1,Mathdatapfg.DB 0),Mathdatapfg.All(Mathdatapfg.Prop,Mathdatapfg.DB(0)))))
  | Ap(TpAp(TmH(h),a),m1) when h = "7966a66a9bb198103c2a540ccd5ebebdff33c10843cc10eebfc98715e142989c" ->
     let a1 = to_mathdatapfgmiz_tp a in
     Mathdatapfg.Lam(a1,Mathdatapfg.Imp(pfgeq(a1,to_mathdatapfgmiz_tm (tmshift 0 1 m1),Mathdatapfg.DB 0),Mathdatapfg.All(Mathdatapfg.Prop,Mathdatapfg.DB(0))))
  | Ap(Ap(TpAp(TmH(h),a),m1),m2) when h = "7966a66a9bb198103c2a540ccd5ebebdff33c10843cc10eebfc98715e142989c" ->
     Mathdatapfg.Imp(pfgeq(to_mathdatapfgmiz_tp a,to_mathdatapfgmiz_tm m1,to_mathdatapfgmiz_tm m2),Mathdatapfg.All(Mathdatapfg.Prop,Mathdatapfg.DB(0)))
  | TpAp(_,_) -> raise (Failure (Printf.sprintf "no polymorphism allowed in pfg: tm_pfgmiz %s" (tm_to_str m)))
  | Ap(m,n) -> Mathdatapfg.Ap(to_mathdatapfgmiz_tm m,to_mathdatapfgmiz_tm n)
  | Lam(a,m) -> Mathdatapfg.Lam(to_mathdatapfgmiz_tp a,to_mathdatapfgmiz_tm m)
  | Imp(m,n) -> Mathdatapfg.Imp(to_mathdatapfgmiz_tm m,to_mathdatapfgmiz_tm n)
  | All(a,m) -> Mathdatapfg.All(to_mathdatapfgmiz_tp a,to_mathdatapfgmiz_tm m)

let rec to_mathdatapfgsetmm_tm m =
  match m with
  | DB(i) -> Mathdatapfg.DB(i)
  | TmH(h) ->
     begin
       try
         Mathdatapfg.Prim(Hashtbl.find pfgsetmmprim h)
       with Not_found ->
         (try Mathdatapfg.TmH(Hashtbl.find pfgtmhh h) with Not_found -> raise (Failure (Printf.sprintf "Could not find corresponding obj id for TmH(%s)\n" h)))
     end
  | Prim(j) when j < 1291 -> Mathdatapfg.Prim(j)
  | Prim(j) -> raise (Failure (Printf.sprintf "bad prim %d case for pfg setmm" j))
  | TpAp(_,_) -> raise (Failure (Printf.sprintf "no polymorphism allowed in pfg: tm_pfgsetmm %s" (tm_to_str m)))
  | Ap(m,n) -> Mathdatapfg.Ap(to_mathdatapfgsetmm_tm m,to_mathdatapfgsetmm_tm n)
  | Lam(a,m) -> Mathdatapfg.Lam(to_mathdatapfgsetmm_tp a,to_mathdatapfgsetmm_tm m)
  | Imp(m,n) -> Mathdatapfg.Imp(to_mathdatapfgsetmm_tm m,to_mathdatapfgsetmm_tm n)
  | All(a,m) -> Mathdatapfg.All(to_mathdatapfgsetmm_tp a,to_mathdatapfgsetmm_tm m)

let rec to_mathdatapfghoas_tm m =
  match m with
  | DB(i) -> Mathdatapfg.DB(i)
  | TmH(h) ->
     begin
       try
         Mathdatapfg.Prim(Hashtbl.find pfghoasprim h)
       with Not_found ->
         (try Mathdatapfg.TmH(Hashtbl.find pfgtmhh h) with Not_found -> raise (Failure (Printf.sprintf "Could not find corresponding obj id for TmH(%s)\n" h)))
     end
  | Prim(j) -> raise (Failure (Printf.sprintf "bad prim %d case for pfg hoas" j))
  | Ap(TpAp(TmH(h),a1),m1) when h = "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099" ->
     pfgex(to_mathdatapfghoas_tp a1,to_mathdatapfghoas_tm m1)
  | TpAp(TmH(h),a) when h = "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a" ->
     let a1 = to_mathdatapfghoas_tp a in
     Mathdatapfg.Lam(a1,Mathdatapfg.Lam(a1,pfgeq(a1,Mathdatapfg.DB 1,Mathdatapfg.DB 0)))
  | Ap(TpAp(TmH(h),a),m1) when h = "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a" ->
     let a1 = to_mathdatapfghoas_tp a in
     Mathdatapfg.Lam(a1,pfgeq(a1,to_mathdatapfghoas_tm (tmshift 0 1 m1),Mathdatapfg.DB 0))
  | Ap(Ap(TpAp(TmH(h),a),m1),m2) when h = "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a" ->
     pfgeq(to_mathdatapfghoas_tp a,to_mathdatapfghoas_tm m1,to_mathdatapfghoas_tm m2)
  | TpAp(TmH(h),a) when h = "7966a66a9bb198103c2a540ccd5ebebdff33c10843cc10eebfc98715e142989c" ->
     let a1 = to_mathdatapfghoas_tp a in
     Mathdatapfg.Lam(a1,Mathdatapfg.Lam(a1,Mathdatapfg.Imp(pfgeq(a1,Mathdatapfg.DB 1,Mathdatapfg.DB 0),Mathdatapfg.All(Mathdatapfg.Prop,Mathdatapfg.DB(0)))))
  | Ap(TpAp(TmH(h),a),m1) when h = "7966a66a9bb198103c2a540ccd5ebebdff33c10843cc10eebfc98715e142989c" ->
     let a1 = to_mathdatapfghoas_tp a in
     Mathdatapfg.Lam(a1,Mathdatapfg.Imp(pfgeq(a1,to_mathdatapfgmiz_tm (tmshift 0 1 m1),Mathdatapfg.DB 0),Mathdatapfg.All(Mathdatapfg.Prop,Mathdatapfg.DB(0))))
  | Ap(Ap(TpAp(TmH(h),a),m1),m2) when h = "7966a66a9bb198103c2a540ccd5ebebdff33c10843cc10eebfc98715e142989c" ->
     Mathdatapfg.Imp(pfgeq(to_mathdatapfgmiz_tp a,to_mathdatapfgmiz_tm m1,to_mathdatapfgmiz_tm m2),Mathdatapfg.All(Mathdatapfg.Prop,Mathdatapfg.DB(0)))
  | TpAp(_,_) -> raise (Failure (Printf.sprintf "no polymorphism allowed in pfg: tm_pfghf %s" (tm_to_str m)))
  | Ap(m,n) -> Mathdatapfg.Ap(to_mathdatapfghoas_tm m,to_mathdatapfghoas_tm n)
  | Lam(a,m) -> Mathdatapfg.Lam(to_mathdatapfghoas_tp a,to_mathdatapfghoas_tm m)
  | Imp(m,n) -> Mathdatapfg.Imp(to_mathdatapfghoas_tm m,to_mathdatapfghoas_tm n)
  | All(a,m) -> Mathdatapfg.All(to_mathdatapfghoas_tp a,to_mathdatapfghoas_tm m)
                               
let to_mathdatapfg_tm m =
  match !pfgtheory with
  | HF -> to_mathdatapfghf_tm m
  | Egal -> to_mathdatapfgegal_tm m
  | Mizar -> to_mathdatapfgmiz_tm m
  | HOAS -> to_mathdatapfghoas_tm m
  | SetMM -> to_mathdatapfgsetmm_tm m

let rec to_mathdatapfg_ptm_all i m =
  if i > 0 then
    raise (Failure "no poly in pfg")
  else
    to_mathdatapfg_tm m

let pfgthyid () =
  match !pfgtheory with
  | HF -> Some(hfthyid)
  | Egal -> Some(egalthyid)
  | Mizar -> Some(mizarthyid)
  | HOAS -> Some(hoasthyid)
  | SetMM -> Some(setmmthyid)

let pfg_propid m =
  let m2 = to_mathdatapfg_ptm_all 0 (tm_beta_eta_norm m) in
  let (m3,b) = Mathdatapfg.beta_eta_norm m2 20 in
  if b then
    let h = Mathdatapfg.tm_hashroot m3 in
    Hash.hashtag (Hash.hashopair2 (pfgthyid()) h) 33l
  else
    raise (Failure "norm problem in pfg_propid")

let pfg_propid2 m =
  let m2 = to_mathdatapfg_ptm_all 0 (tm_beta_eta_norm m) in
  let (m3,b) = Mathdatapfg.beta_eta_norm m2 20 in
  if b then
    let h = Mathdatapfg.tm_hashroot m3 in
    (h,Hash.hashtag (Hash.hashopair2 (pfgthyid()) h) 33l)
  else
    raise (Failure "norm problem in pfg_propid")

let pfg_objid_pure_to_thy h a =
  let ah = Mathdatapfg.hashtp (to_mathdatapfg_tp a) in
  Hash.hashtag (Hash.hashopair2 (pfgthyid()) (Hash.hashpair h ah)) 32l

let pfg_objid m a =
  let m2 = to_mathdatapfg_ptm_all 0 (tm_beta_eta_norm m) in
  let (m3,b) = Mathdatapfg.beta_eta_norm m2 20 in
  if b then
    let mh = Mathdatapfg.tm_hashroot m3 in
    (mh,pfg_objid_pure_to_thy mh a)
  else
    raise (Failure "norm problem in pfg_objid")

let nxtpfgvar phi =
  incr pfgvarcount;
  let x = ref (Printf.sprintf "x%d" !pfgvarcount) in
  while Hashtbl.mem pfgreserved !x || List.mem !x phi do
    incr pfgvarcount;
    x := Printf.sprintf "x%d" !pfgvarcount
  done;
  !x

let rec tm_pfghf_str_r m phi =
  match m with
  | DB(j) -> List.nth phi j
  | TmH(h) ->
     begin
       try
         Printf.sprintf "Prim %d" (Hashtbl.find pfghfprim h)
       with Not_found ->
         (try Hashtbl.find pfgtmh h with Not_found -> Printf.sprintf "#%s" h)
     end
  | Prim(j) ->
     begin
       try
         let s = List.nth ["Eps";"In";"Empty";"Union";"Power";"Repl";"UnivOf"] j in
         if (s = "Eps" || s = "UnivOf") then raise (Failure "disallowed prims for pfg hf");
         if s = "In" then
           "Prim 7"
         else if s = "Empty" then
           "Prim 9"
         else if s = "Union" then
           "Prim 10"
         else if s = "Power" then
           "Prim 11"
         else if s = "Repl" then
           "Prim 12"
         else
           raise (Failure "disallowed prims for pfg hf")
       with _ -> raise (Failure (Printf.sprintf "bad prim %d case for pfg hf" j))
     end
  | Ap(TpAp(TmH(h),a1),Lam(_,m1)) when h = "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099" ->
     let x =
       if free_in_tm_p m1 0 then
	 begin
	   try
	     Hashtbl.find pfgbvarh m
	   with Not_found ->
             nxtpfgvar phi
	 end
       else
	 "_"
     in
     Printf.sprintf "Ex %s %s %s" x (tp_pfgset_str a1) (tm_pfghf_str_r m1 (x::phi))
  | Ap(TpAp(TmH(h),a1),m1) when h = "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099" ->
     let x =
       begin
	 try
	   let z = Hashtbl.find pfgbvarh m in
           if Hashtbl.mem pfgreserved z then raise Not_found;
           if List.mem z phi then raise Not_found;
           z
	 with Not_found ->
           nxtpfgvar phi
       end
     in
     Printf.sprintf "Ex %s %s Ap %s %s" x (tp_pfgset_str a1) (tm_pfghf_str_r m1 phi) x
  | Ap(Ap(TpAp(TmH(h),a),m1),m2) when h = "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a" ->
     Printf.sprintf "Eq %s %s %s" (tp_pfgset_str a) (tm_pfghf_str_r m1 phi) (tm_pfghf_str_r m2 phi)
  | Ap(Ap(TpAp(TmH(h),a),m1),m2) when h = "7966a66a9bb198103c2a540ccd5ebebdff33c10843cc10eebfc98715e142989c" ->
     Printf.sprintf "Ap Prim 3 Eq %s %s %s" (tp_pfgset_str a) (tm_pfghf_str_r m1 phi) (tm_pfghf_str_r m2 phi)
  | TpAp(_,a) -> raise (Failure (Printf.sprintf "no polymorphism allowed in pfg: tm_pfghf %s" (tm_to_str m)))
  | Ap(m1,m2) -> Printf.sprintf "Ap %s %s" (tm_pfghf_str_r m1 phi) (tm_pfghf_str_r m2 phi)
  | Imp(m1,m2) -> Printf.sprintf "Imp %s %s" (tm_pfghf_str_r m1 phi) (tm_pfghf_str_r m2 phi)
  | All(a1,m1) ->
      begin
	let x =
	  if free_in_tm_p m1 0 then
	    begin
	      try
	        let z = Hashtbl.find pfgbvarh m in
                if Hashtbl.mem pfgreserved z then raise Not_found;
                if List.mem z phi then raise Not_found;
                z
	      with Not_found ->
                nxtpfgvar phi
	    end
	  else
	    "_"
	in
	Printf.sprintf "All %s %s %s" x (tp_pfgset_str a1) (tm_pfghf_str_r m1 (x::phi))
      end
  | Lam(a1,m1) ->
      begin
	let x =
	  if free_in_tm_p m1 0 then
	    begin
	      try
	        let z = Hashtbl.find pfgbvarh m in
                if Hashtbl.mem pfgreserved z then raise Not_found;
                if List.mem z phi then raise Not_found;
                z
	      with Not_found ->
                nxtpfgvar phi
	    end
	  else
	    "_"
	in
	Printf.sprintf "Lam %s %s %s" x (tp_pfgset_str a1) (tm_pfghf_str_r m1 (x::phi))
      end

let nxtpfghyp psi =
  incr pfghypcount;
  let x = ref (Printf.sprintf "A%d" !pfghypcount) in
  while Hashtbl.mem pfgreserved !x || List.mem !x psi do
    incr pfghypcount;
    x := Printf.sprintf "A%d" !pfghypcount
  done;
  !x

let rec tm_pfgegal_str_r m phi =
  match m with
  | DB(j) -> List.nth phi j
  | TmH(h) ->
     begin
       try
         Printf.sprintf "Prim %d" (Hashtbl.find pfgegalprim h)
       with Not_found ->
         (try Hashtbl.find pfgtmh h with Not_found -> Printf.sprintf "#%s" h)
     end
  | Prim(j) when j > 0 -> Printf.sprintf "Prim %d" j
  | Prim(j) -> raise (Failure (Printf.sprintf "bad prim %d case for pfg egal" j))
  | Ap(TpAp(TmH(h),a1),Lam(_,m1)) when h = "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099" ->
     let x =
       if free_in_tm_p m1 0 then
	 begin
	   try
	     let z = Hashtbl.find pfgbvarh m in
             if Hashtbl.mem pfgreserved z then raise Not_found;
             if List.mem z phi then raise Not_found;
             z
	   with Not_found ->
             nxtpfgvar phi
	 end
       else
	 "_"
     in
     Printf.sprintf "Ex %s %s %s" x (tp_pfgset_str a1) (tm_pfgegal_str_r m1 (x::phi))
  | Ap(TpAp(TmH(h),a1),m1) when h = "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099" ->
     let x =
       begin
	 try
	   let z = Hashtbl.find pfgbvarh m in
           if Hashtbl.mem pfgreserved z then raise Not_found;
           if List.mem z phi then raise Not_found;
           z
	 with Not_found ->
           nxtpfgvar phi
       end
     in
     Printf.sprintf "Ex %s %s Ap %s %s" x (tp_pfgset_str a1) (tm_pfgegal_str_r m1 phi) x
  | Ap(Ap(TpAp(TmH(h),a),m1),m2) when h = "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a" ->
     Printf.sprintf "Eq %s %s %s" (tp_pfgset_str a) (tm_pfgegal_str_r m1 phi) (tm_pfgegal_str_r m2 phi)
  | Ap(Ap(TpAp(TmH(h),a),m1),m2) when h = "7966a66a9bb198103c2a540ccd5ebebdff33c10843cc10eebfc98715e142989c" ->
     Printf.sprintf "Imp Eq %s %s %s All p Prop p" (tp_pfgset_str a) (tm_pfgegal_str_r m1 phi) (tm_pfgegal_str_r m2 phi)
  | TpAp(_,a) -> raise (Failure (Printf.sprintf "no polymorphism allowed in pfg: tm_pfgegal %s" (tm_to_str m)))
  | Ap(m1,m2) -> Printf.sprintf "Ap %s %s" (tm_pfgegal_str_r m1 phi) (tm_pfgegal_str_r m2 phi)
  | Imp(m1,m2) -> Printf.sprintf "Imp %s %s" (tm_pfgegal_str_r m1 phi) (tm_pfgegal_str_r m2 phi)
  | All(a1,m1) ->
      begin
	let x =
	  if free_in_tm_p m1 0 then
	    begin
	      try
	        let z = Hashtbl.find pfgbvarh m in
                if Hashtbl.mem pfgreserved z then raise Not_found;
                if List.mem z phi then raise Not_found;
                z
	      with Not_found ->
                nxtpfgvar phi
	    end
	  else
	    "_"
	in
	Printf.sprintf "All %s %s %s" x (tp_pfgset_str a1) (tm_pfgegal_str_r m1 (x::phi))
      end
  | Lam(a1,m1) ->
      begin
	let x =
	  if free_in_tm_p m1 0 then
	    begin
	      try
	        let z = Hashtbl.find pfgbvarh m in
                if Hashtbl.mem pfgreserved z then raise Not_found;
                if List.mem z phi then raise Not_found;
                z
	      with Not_found ->
                nxtpfgvar phi
	    end
	  else
	    "_"
	in
	Printf.sprintf "Lam %s %s %s" x (tp_pfgset_str a1) (tm_pfgegal_str_r m1 (x::phi))
      end


let rec tm_pfgmiz_str_r m phi =
  match m with
  | DB(j) -> List.nth phi j
  | TmH(h) ->
     begin
       try
         Printf.sprintf "Prim %d" (Hashtbl.find pfgmizprim h)
       with Not_found ->
         (try Hashtbl.find pfgtmh h with Not_found -> Printf.sprintf "#%s" h)
     end
  | Prim(j) when j = 1 || j = 3 -> Printf.sprintf "Prim %d" j
  | Prim(j) -> raise (Failure (Printf.sprintf "bad prim %d case for pfg miz" j))
  | Ap(TpAp(TmH(h),a1),Lam(_,m1)) when h = "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099" ->
     let x =
       if free_in_tm_p m1 0 then
	 begin
	   try
	     let z = Hashtbl.find pfgbvarh m in
             if Hashtbl.mem pfgreserved z then raise Not_found;
             if List.mem z phi then raise Not_found;
             z
	   with Not_found ->
             nxtpfgvar phi
	 end
       else
	 "_"
     in
     Printf.sprintf "Ex %s %s %s" x (tp_pfgset_str a1) (tm_pfgmiz_str_r m1 (x::phi))
  | Ap(TpAp(TmH(h),a1),m1) when h = "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099" ->
     let x =
       begin
	 try
	   let z = Hashtbl.find pfgbvarh m in
           if Hashtbl.mem pfgreserved z then raise Not_found;
           if List.mem z phi then raise Not_found;
           z
	 with Not_found ->
           nxtpfgvar phi
       end
     in
     Printf.sprintf "Ex %s %s Ap %s %s" x (tp_pfgset_str a1) (tm_pfgmiz_str_r m1 phi) x
  | Ap(Ap(TpAp(TmH(h),a),m1),m2) when h = "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a" ->
     Printf.sprintf "Eq %s %s %s" (tp_pfgset_str a) (tm_pfgmiz_str_r m1 phi) (tm_pfgmiz_str_r m2 phi)
  | Ap(Ap(TpAp(TmH(h),a),m1),m2) when h = "7966a66a9bb198103c2a540ccd5ebebdff33c10843cc10eebfc98715e142989c" ->
     Printf.sprintf "Imp Eq %s %s %s All p Prop p" (tp_pfgset_str a) (tm_pfgmiz_str_r m1 phi) (tm_pfgmiz_str_r m2 phi)
  | TpAp(_,a) -> raise (Failure (Printf.sprintf "no polymorphism allowed in pfg: tm_pfgmiz %s" (tm_to_str m)))
  | Ap(m1,m2) -> Printf.sprintf "Ap %s %s" (tm_pfgmiz_str_r m1 phi) (tm_pfgmiz_str_r m2 phi)
  | Imp(m1,m2) -> Printf.sprintf "Imp %s %s" (tm_pfgmiz_str_r m1 phi) (tm_pfgmiz_str_r m2 phi)
  | All(a1,m1) ->
      begin
	let x =
	  if free_in_tm_p m1 0 then
	    begin
	      try
	        let z = Hashtbl.find pfgbvarh m in
                if Hashtbl.mem pfgreserved z then raise Not_found;
                if List.mem z phi then raise Not_found;
                z
	      with Not_found ->
                nxtpfgvar phi
	    end
	  else
	    "_"
	in
	Printf.sprintf "All %s %s %s" x (tp_pfgset_str a1) (tm_pfgmiz_str_r m1 (x::phi))
      end
  | Lam(a1,m1) ->
      begin
	let x =
	  if free_in_tm_p m1 0 then
	    begin
	      try
	        let z = Hashtbl.find pfgbvarh m in
                if Hashtbl.mem pfgreserved z then raise Not_found;
                if List.mem z phi then raise Not_found;
                z
	      with Not_found ->
                nxtpfgvar phi
	    end
	  else
	    "_"
	in
	Printf.sprintf "Lam %s %s %s" x (tp_pfgset_str a1) (tm_pfgmiz_str_r m1 (x::phi))
      end

let rec tm_pfghoas_str_r m phi =
  match m with
  | DB(j) -> List.nth phi j
  | TmH(h) ->
     begin
       try
         Printf.sprintf "Prim %d" (Hashtbl.find pfghoasprim h)
       with Not_found ->
         (try Hashtbl.find pfgtmh h with Not_found -> Printf.sprintf "#%s" h)
     end
  | Prim(j) when j = 0 || j = 1 -> Printf.sprintf "Prim %d" j
  | Prim(j) -> raise (Failure (Printf.sprintf "bad prim %d case for pfg hoas" j))
  | Ap(TpAp(TmH(h),a1),Lam(_,m1)) when h = "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099" ->
     let x =
       if free_in_tm_p m1 0 then
	 begin
	   try
	     let z = Hashtbl.find pfgbvarh m in
             if Hashtbl.mem pfgreserved z then raise Not_found;
             if List.mem z phi then raise Not_found;
             z
	   with Not_found ->
             nxtpfgvar phi
	 end
       else
	 "_"
     in
     Printf.sprintf "Ex %s %s %s" x (tp_pfgsyn_str a1) (tm_pfghoas_str_r m1 (x::phi))
  | Ap(TpAp(TmH(h),a1),m1) when h = "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099" ->
     let x =
       begin
	 try
	   let z = Hashtbl.find pfgbvarh m in
           if Hashtbl.mem pfgreserved z then raise Not_found;
           if List.mem z phi then raise Not_found;
           z
	 with Not_found ->
           nxtpfgvar phi
       end
     in
     Printf.sprintf "Ex %s %s Ap %s %s" x (tp_pfgsyn_str a1) (tm_pfghoas_str_r m1 phi) x
  | Ap(Ap(TpAp(TmH(h),a),m1),m2) when h = "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a" ->
     Printf.sprintf "Eq %s %s %s" (tp_pfgsyn_str a) (tm_pfghoas_str_r m1 phi) (tm_pfghoas_str_r m2 phi)
  | Ap(Ap(TpAp(TmH(h),a),m1),m2) when h = "7966a66a9bb198103c2a540ccd5ebebdff33c10843cc10eebfc98715e142989c" ->
     Printf.sprintf "Imp Eq %s %s %s All p Prop p" (tp_pfgsyn_str a) (tm_pfghoas_str_r m1 phi) (tm_pfghoas_str_r m2 phi)
  | TpAp(_,a) -> raise (Failure (Printf.sprintf "no polymorphism allowed in pfg: tm_pfghoas %s" (tm_to_str m)))
  | Ap(m1,m2) -> Printf.sprintf "Ap %s %s" (tm_pfghoas_str_r m1 phi) (tm_pfghoas_str_r m2 phi)
  | Imp(m1,m2) -> Printf.sprintf "Imp %s %s" (tm_pfghoas_str_r m1 phi) (tm_pfghoas_str_r m2 phi)
  | All(a1,m1) ->
      begin
	let x =
	  if free_in_tm_p m1 0 then
	    begin
	      try
	        let z = Hashtbl.find pfgbvarh m in
                if Hashtbl.mem pfgreserved z then raise Not_found;
                if List.mem z phi then raise Not_found;
                z
	      with Not_found ->
                nxtpfgvar phi
	    end
	  else
	    "_"
	in
	Printf.sprintf "All %s %s %s" x (tp_pfgsyn_str a1) (tm_pfghoas_str_r m1 (x::phi))
      end
  | Lam(a1,m1) ->
      begin
	let x =
	  if free_in_tm_p m1 0 then
	    begin
	      try
	        let z = Hashtbl.find pfgbvarh m in
                if Hashtbl.mem pfgreserved z then raise Not_found;
                if List.mem z phi then raise Not_found;
                z
	      with Not_found ->
                nxtpfgvar phi
	    end
	  else
	    "_"
	in
	Printf.sprintf "Lam %s %s %s" x (tp_pfgsyn_str a1) (tm_pfghoas_str_r m1 (x::phi))
      end

let knowncnt = ref 0

let rec tm_pfghf_decl dh tmph m =
  match m with
  | TmH(h) when not (Hashtbl.mem pfgtmh h) && not (Hashtbl.mem pfghfprim h) ->
     begin
       try
         let (x,a,om) = Hashtbl.find tmph h in
         if Hashtbl.mem dh h then
           begin (** Include def for delta in some proof **)
             Hashtbl.add pfgtmh h x;
             match om with
             | Some(m) ->
                tm_pfghf_decl dh tmph m;
                Printf.printf "Def %s : %s\n := %s\n" x (tp_pfgset_str a) (tm_pfghf_str_r m [])
             | _ -> raise (Failure (Printf.sprintf "delta required for %s [%s] but do not have def" x h))
           end
         else
           begin (** No deltas needed, so just include as opaque param **)
             try
               let pfghv = Hashtbl.find pfgtmhh h in
               Hashtbl.add pfgtmh h x;
               Printf.printf "Param %s %s : %s\n" (Hash.hashval_hexstring pfghv) x (tp_pfgset_str a)
             with Not_found -> raise (Failure (Printf.sprintf "do not know pfg id corresponding to %s" h))
           end
       with Not_found -> raise (Failure (Printf.sprintf "cannot find info for %s to create pfg version" h))
     end
  | Ap(m1,m2) -> tm_pfghf_decl dh tmph m1; tm_pfghf_decl dh tmph m2
  | Lam(_,m2) -> tm_pfghf_decl dh tmph m2
  | Imp(m1,m2) -> tm_pfghf_decl dh tmph m1; tm_pfghf_decl dh tmph m2
  | All(_,m2) -> tm_pfghf_decl dh tmph m2
  | _ -> ()

let rec pf_pfghf_decl dh tmph knph d =
  match d with
  | Known(h) when not (Hashtbl.mem pfgknh h) && not (h = "5626ac8cb7c90418f6c980ffedd6f45097048659977d8690c44f9d34feb6b2d3") ->
     begin
       let p = Hashtbl.find knph h in
       tm_pfghf_decl dh tmph p;
       let nm =
         try
           Hashtbl.find pfghfknname h
         with _ -> incr knowncnt; Printf.sprintf "Known%d" !knowncnt
       in
       Printf.printf "Known %s : %s\n" nm (tm_pfghf_str_r p []);
       Hashtbl.add pfgknh h nm
     end
  | PTpAp(d1,_) -> pf_pfghf_decl dh tmph knph d1
  | PTmAp(d1,m2) -> tm_pfghf_decl dh tmph m2; pf_pfghf_decl dh tmph knph d1
  | PPfAp(d1,d2) -> pf_pfghf_decl dh tmph knph d1; pf_pfghf_decl dh tmph knph d2
  | PLam(p1,d2) -> tm_pfghf_decl dh tmph p1; pf_pfghf_decl dh tmph knph d2
  | TLam(_,d2) -> pf_pfghf_decl dh tmph knph d2
  | _ -> ()

let rec tm_pfgegal_decl dh tmph m =
  match m with
  | TmH(h) when not (Hashtbl.mem pfgtmh h) && not (Hashtbl.mem pfgegalprim h) ->
     begin
       try
         let (x,a,om) = Hashtbl.find tmph h in
         if Hashtbl.mem dh h || h = "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87" then (** never make False opaque in Egal **)
           begin (** Include def for delta in some proof **)
             Hashtbl.add pfgtmh h x;
             match om with
             | Some(m) ->
                tm_pfgegal_decl dh tmph m;
                Printf.printf "Def %s : %s\n := %s\n" x (tp_pfgset_str a) (tm_pfgegal_str_r m [])
             | _ -> raise (Failure (Printf.sprintf "delta required for %s [%s] but do not have def" x h))
           end
         else
           begin (** No deltas needed, so just include as opaque param **)
             try
               let pfghv = Hashtbl.find pfgtmhh h in
               Hashtbl.add pfgtmh h x;
               Printf.printf "Param %s %s : %s\n" (Hash.hashval_hexstring pfghv) x (tp_pfgset_str a)
             with Not_found -> raise (Failure (Printf.sprintf "do not know pfg id corresponding to %s" h))
           end
       with Not_found -> raise (Failure (Printf.sprintf "cannot find info for %s to create pfg version" h))
     end
  | Ap(m1,m2) -> tm_pfgegal_decl dh tmph m1; tm_pfgegal_decl dh tmph m2
  | Lam(_,m2) -> tm_pfgegal_decl dh tmph m2
  | Imp(m1,m2) -> tm_pfgegal_decl dh tmph m1; tm_pfgegal_decl dh tmph m2
  | All(_,m2) -> tm_pfgegal_decl dh tmph m2
  | _ -> ()

let rec tm_pfgmiz_decl dh tmph m =
  match m with
  | TmH(h) when not (Hashtbl.mem pfgtmh h) && not (Hashtbl.mem pfgmizprim h) ->
     begin
       try
         let (x,a,om) = Hashtbl.find tmph h in
         if Hashtbl.mem dh h || h = "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87" then (** never make False opaque in Mizar **)
           begin (** Include def for delta in some proof **)
             Hashtbl.add pfgtmh h x;
             match om with
             | Some(m) ->
                tm_pfgmiz_decl dh tmph m;
                Printf.printf "Def %s : %s\n := %s\n" x (tp_pfgset_str a) (tm_pfgmiz_str_r m [])
             | _ -> raise (Failure (Printf.sprintf "delta required for %s [%s] but do not have def" x h))
           end
         else
           begin (** No deltas needed, so just include as opaque param **)
             try
               let pfghv = Hashtbl.find pfgtmhh h in
               Hashtbl.add pfgtmh h x;
               Printf.printf "Param %s %s : %s\n" (Hash.hashval_hexstring pfghv) x (tp_pfgset_str a)
             with Not_found -> raise (Failure (Printf.sprintf "do not know pfg id corresponding to %s" h))
           end
       with Not_found -> raise (Failure (Printf.sprintf "cannot find info for %s to create pfg version" h))
     end
  | Ap(m1,m2) -> tm_pfgmiz_decl dh tmph m1; tm_pfgmiz_decl dh tmph m2
  | Lam(_,m2) -> tm_pfgmiz_decl dh tmph m2
  | Imp(m1,m2) -> tm_pfgmiz_decl dh tmph m1; tm_pfgmiz_decl dh tmph m2
  | All(_,m2) -> tm_pfgmiz_decl dh tmph m2
  | _ -> ()

let rec tm_pfgsetmm_str_r m phi =
  match m with
  | DB(j) -> List.nth phi j
  | TmH(h) ->
     begin
       try
         Printf.sprintf "Prim %d" (Hashtbl.find pfgsetmmprim h)
       with Not_found ->
         (try Hashtbl.find pfgtmh h with Not_found -> Printf.sprintf "#%s" h)
     end
  | Prim(j) when j < 1291 -> Printf.sprintf "Prim %d" j
  | Prim(j) -> raise (Failure (Printf.sprintf "bad prim %d case for pfg setmm" j))
  | TpAp(_,a) -> raise (Failure (Printf.sprintf "no polymorphism allowed in pfg: tm_pfgsetmm %s" (tm_to_str m)))
  | Ap(m1,m2) -> Printf.sprintf "Ap %s %s" (tm_pfgsetmm_str_r m1 phi) (tm_pfgsetmm_str_r m2 phi)
  | Imp(m1,m2) -> Printf.sprintf "Imp %s %s" (tm_pfgsetmm_str_r m1 phi) (tm_pfgsetmm_str_r m2 phi)
  | All(a1,m1) ->
      begin
	let x =
	  if free_in_tm_p m1 0 then
	    begin
	      try
	        let z = Hashtbl.find pfgbvarh m in
                if Hashtbl.mem pfgreserved z then raise Not_found;
                if List.mem z phi then raise Not_found;
                z
	      with Not_found ->
                nxtpfgvar phi
	    end
	  else
	    "_"
	in
	Printf.sprintf "All %s %s %s" x (tp_pfgset_str a1) (tm_pfgsetmm_str_r m1 (x::phi))
      end
  | Lam(a1,m1) ->
      begin
	let x =
	  if free_in_tm_p m1 0 then
	    begin
	      try
	        let z = Hashtbl.find pfgbvarh m in
                if Hashtbl.mem pfgreserved z then raise Not_found;
                if List.mem z phi then raise Not_found;
                z
	      with Not_found ->
                nxtpfgvar phi
	    end
	  else
	    "_"
	in
	Printf.sprintf "Lam %s %s %s" x (tp_pfgset_str a1) (tm_pfgsetmm_str_r m1 (x::phi))
      end

let rec tm_pfgsetmm_decl dh tmph m =
  match m with
  | TmH(h) when not (Hashtbl.mem pfgtmh h) && not (Hashtbl.mem pfgsetmmprim h) ->
     begin
       try
         let (x,a,om) = Hashtbl.find tmph h in
         if Hashtbl.mem dh h then
           begin (** Include def for delta in some proof **)
             Hashtbl.add pfgtmh h x;
             match om with
             | Some(m) ->
                tm_pfgsetmm_decl dh tmph m;
                Printf.printf "Def %s : %s\n := %s\n" x (tp_pfgset_str a) (tm_pfgsetmm_str_r m [])
             | _ -> raise (Failure (Printf.sprintf "delta required for %s [%s] but do not have def" x h))
           end
         else
           begin (** No deltas needed, so just include as opaque param **)
             try
               let pfghv = Hashtbl.find pfgtmhh h in
               Hashtbl.add pfgtmh h x;
               Printf.printf "Param %s %s : %s\n" (Hash.hashval_hexstring pfghv) x (tp_pfgset_str a)
             with Not_found -> raise (Failure (Printf.sprintf "do not know pfg id corresponding to %s" h))
           end
       with Not_found -> raise (Failure (Printf.sprintf "cannot find info for %s to create pfg version" h))
     end
  | Ap(m1,m2) -> tm_pfgsetmm_decl dh tmph m1; tm_pfgsetmm_decl dh tmph m2
  | Lam(_,m2) -> tm_pfgsetmm_decl dh tmph m2
  | Imp(m1,m2) -> tm_pfgsetmm_decl dh tmph m1; tm_pfgsetmm_decl dh tmph m2
  | All(_,m2) -> tm_pfgsetmm_decl dh tmph m2
  | _ -> ()

let rec pf_pfgegal_decl dh tmph knph d =
  match d with
  | Known(h) when not (Hashtbl.mem pfgknh h) && not (h = "5626ac8cb7c90418f6c980ffedd6f45097048659977d8690c44f9d34feb6b2d3") ->
     begin
       let p = Hashtbl.find knph h in
       tm_pfgegal_decl dh tmph p;
       let nm =
         try
           Hashtbl.find pfgegalknname h
         with _ -> incr knowncnt; Printf.sprintf "Known%d" !knowncnt
       in
       Printf.printf "Known %s : %s\n" nm (tm_pfgegal_str_r p []);
       Hashtbl.add pfgknh h nm
     end
  | PTpAp(d1,_) -> pf_pfgegal_decl dh tmph knph d1
  | PTmAp(d1,m2) -> tm_pfgegal_decl dh tmph m2; pf_pfgegal_decl dh tmph knph d1
  | PPfAp(d1,d2) -> pf_pfgegal_decl dh tmph knph d1; pf_pfgegal_decl dh tmph knph d2
  | PLam(p1,d2) -> tm_pfgegal_decl dh tmph p1; pf_pfgegal_decl dh tmph knph d2
  | TLam(_,d2) -> pf_pfgegal_decl dh tmph knph d2
  | _ -> ()

let rec pf_pfgmiz_decl dh tmph knph d =
  match d with
  | Known(h) when not (Hashtbl.mem pfgknh h) && not (h = "5626ac8cb7c90418f6c980ffedd6f45097048659977d8690c44f9d34feb6b2d3") ->
     begin
       let p = Hashtbl.find knph h in
       tm_pfgmiz_decl dh tmph p;
       let nm =
         try
           Hashtbl.find pfgmizknname h
         with _ -> incr knowncnt; Printf.sprintf "Known%d" !knowncnt
       in
       Printf.printf "Known %s : %s\n" nm (tm_pfgmiz_str_r p []);
       Hashtbl.add pfgknh h nm
     end
  | PTpAp(d1,_) -> pf_pfgmiz_decl dh tmph knph d1
  | PTmAp(d1,m2) -> tm_pfgmiz_decl dh tmph m2; pf_pfgmiz_decl dh tmph knph d1
  | PPfAp(d1,d2) -> pf_pfgmiz_decl dh tmph knph d1; pf_pfgmiz_decl dh tmph knph d2
  | PLam(p1,d2) -> tm_pfgmiz_decl dh tmph p1; pf_pfgmiz_decl dh tmph knph d2
  | TLam(_,d2) -> pf_pfgmiz_decl dh tmph knph d2
  | _ -> ()

let rec pf_pfgsetmm_decl dh tmph knph d =
  match d with
  | Known(h) when not (Hashtbl.mem pfgknh h) ->
     begin
       let p = Hashtbl.find knph h in
       tm_pfgsetmm_decl dh tmph p;
       let nm =
         try
           Hashtbl.find pfgsetmmknname h (** This is empty, but could be set to use the same names as in MetaMath. **)
         with _ -> incr knowncnt; Printf.sprintf "Known%d" !knowncnt
       in
       Printf.printf "Known %s : %s\n" nm (tm_pfgsetmm_str_r p []);
       Hashtbl.add pfgknh h nm
     end
  | PTpAp(d1,_) -> pf_pfgsetmm_decl dh tmph knph d1
  | PTmAp(d1,m2) -> tm_pfgsetmm_decl dh tmph m2; pf_pfgsetmm_decl dh tmph knph d1
  | PPfAp(d1,d2) -> pf_pfgsetmm_decl dh tmph knph d1; pf_pfgsetmm_decl dh tmph knph d2
  | PLam(p1,d2) -> tm_pfgsetmm_decl dh tmph p1; pf_pfgsetmm_decl dh tmph knph d2
  | TLam(_,d2) -> pf_pfgsetmm_decl dh tmph knph d2
  | _ -> ()

let rec tm_pfghoas_decl dh tmph m =
  match m with
  | TmH(h) when not (Hashtbl.mem pfgtmh h) && not (Hashtbl.mem pfghoasprim h) ->
     begin
       try
         let (x,a,om) = Hashtbl.find tmph h in
         if Hashtbl.mem dh h || h = "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87" then (** never make False opaque in HOAS **)
           begin (** Include def for delta in some proof **)
             Hashtbl.add pfgtmh h x;
             match om with
             | Some(m) ->
                tm_pfghoas_decl dh tmph m;
                Printf.printf "Def %s : %s\n := %s\n" x (tp_pfgsyn_str a) (tm_pfghoas_str_r m [])
             | _ -> raise (Failure (Printf.sprintf "delta required for %s [%s] but do not have def" x h))
           end
         else
           begin (** No deltas needed, so just include as opaque param **)
             try
               let pfghv = Hashtbl.find pfgtmhh h in
               Hashtbl.add pfgtmh h x;
               Printf.printf "Param %s %s : %s\n" (Hash.hashval_hexstring pfghv) x (tp_pfgsyn_str a)
             with Not_found -> raise (Failure (Printf.sprintf "do not know pfg id corresponding to %s" h))
           end
       with Not_found -> raise (Failure (Printf.sprintf "cannot find info for %s to create pfg version" h))
     end
  | Ap(m1,m2) -> tm_pfghoas_decl dh tmph m1; tm_pfghoas_decl dh tmph m2
  | Lam(_,m2) -> tm_pfghoas_decl dh tmph m2
  | Imp(m1,m2) -> tm_pfghoas_decl dh tmph m1; tm_pfghoas_decl dh tmph m2
  | All(_,m2) -> tm_pfghoas_decl dh tmph m2
  | _ -> ()

let rec pf_pfghoas_decl dh tmph knph d =
  match d with
  | Known(h) when not (Hashtbl.mem pfgknh h) && not (h = "5626ac8cb7c90418f6c980ffedd6f45097048659977d8690c44f9d34feb6b2d3") ->
     begin
       let p = Hashtbl.find knph h in
       tm_pfghoas_decl dh tmph p;
       let nm =
         try
           Hashtbl.find pfghoasknname h
         with _ ->
           incr knowncnt;
           Printf.sprintf "Known%d" !knowncnt
       in
       Printf.printf "Known %s : %s\n" nm (tm_pfghoas_str_r p []);
       Hashtbl.add pfgknh h nm
     end
  | PTpAp(d1,_) -> pf_pfghoas_decl dh tmph knph d1
  | PTmAp(d1,m2) -> tm_pfghoas_decl dh tmph m2; pf_pfghoas_decl dh tmph knph d1
  | PPfAp(d1,d2) -> pf_pfghoas_decl dh tmph knph d1; pf_pfghoas_decl dh tmph knph d2
  | PLam(p1,d2) -> tm_pfghoas_decl dh tmph p1; pf_pfghoas_decl dh tmph knph d2
  | TLam(_,d2) -> pf_pfghoas_decl dh tmph knph d2
  | _ -> ()

let tm_pfg_decl dh tmph m =
  match !pfgtheory with
  | HF -> tm_pfghf_decl dh tmph m
  | Egal -> tm_pfgegal_decl dh tmph m
  | Mizar -> tm_pfgmiz_decl dh tmph m
  | HOAS -> tm_pfghoas_decl dh tmph m
  | SetMM -> tm_pfgsetmm_decl dh tmph m

let pf_pfg_decl dh tmph knph d =
  match !pfgtheory with
  | HF -> pf_pfghf_decl dh tmph knph d
  | Egal -> pf_pfgegal_decl dh tmph knph d
  | Mizar -> pf_pfgmiz_decl dh tmph knph d
  | HOAS -> pf_pfghoas_decl dh tmph knph d
  | SetMM -> pf_pfgsetmm_decl dh tmph knph d

let rec pf_pfghf_str_r d phi psi =
  match d with
  | Hyp(j) -> List.nth psi j
  | Known(h) -> (try Hashtbl.find pfgknh h with Not_found -> Printf.sprintf "#%s" h)
  | PTpAp(PTpAp(Known(h),a1),a2) when h = "5626ac8cb7c90418f6c980ffedd6f45097048659977d8690c44f9d34feb6b2d3" -> Printf.sprintf "Ext %s %s" (tp_pfgset_str a1) (tp_pfgset_str a2)
  | PTpAp(d1,a2) -> Printf.sprintf "TpAp %s %s" (pf_pfghf_str_r d1 phi psi) (tp_pfgset_str a2)
  | PTmAp(d1,m2) -> Printf.sprintf "TmAp %s %s" (pf_pfghf_str_r d1 phi psi) (tm_pfghf_str_r m2 phi)
  | PPfAp(d1,d2) -> Printf.sprintf "PrAp %s %s" (pf_pfghf_str_r d1 phi psi) (pf_pfghf_str_r d2 phi psi)
  | PLam(m1,d2) ->
      begin
	let x =
	  if hyp_in_pf_p d2 0 then
	    begin
	      try
	        let z = Hashtbl.find pfghyph d in
                if Hashtbl.mem pfgreserved z then raise Not_found;
                if List.mem z psi then raise Not_found;
                z
	      with Not_found ->
                nxtpfghyp psi
	    end
	  else
	    "_"
	in
	Printf.sprintf "PrLa %s %s %s" x (tm_pfghf_str_r m1 phi) (pf_pfghf_str_r d2 phi (x::psi))
      end
  | TLam(a1,d2) ->
      begin
	let x =
	  if free_in_pf_p d2 0 then
	    begin
	      try
	        let z = Hashtbl.find pfgpfbvarh d in
                if Hashtbl.mem pfgreserved z then raise Not_found;
                if List.mem z phi then raise Not_found;
                z
	      with Not_found ->
                nxtpfgvar phi
	    end
	  else
	    "_"
	in
	Printf.sprintf "TmLa %s %s %s" x (tp_pfgset_str a1) (pf_pfghf_str_r d2 (x::phi) psi)
      end

let rec pf_pfgegal_str_r d phi psi =
  match d with
  | Hyp(j) -> List.nth psi j
  | Known(h) -> (try Hashtbl.find pfgknh h with Not_found -> Printf.sprintf "#%s" h)
  | PTpAp(PTpAp(Known(h),a1),a2) when h = "5626ac8cb7c90418f6c980ffedd6f45097048659977d8690c44f9d34feb6b2d3" -> Printf.sprintf "Ext %s %s" (tp_pfgset_str a1) (tp_pfgset_str a2)
  | PTpAp(d1,a2) -> Printf.sprintf "TpAp %s %s" (pf_pfgegal_str_r d1 phi psi) (tp_pfgset_str a2)
  | PTmAp(d1,m2) -> Printf.sprintf "TmAp %s %s" (pf_pfgegal_str_r d1 phi psi) (tm_pfgegal_str_r m2 phi)
  | PPfAp(d1,d2) -> Printf.sprintf "PrAp %s %s" (pf_pfgegal_str_r d1 phi psi) (pf_pfgegal_str_r d2 phi psi)
  | PLam(m1,d2) ->
      begin
	let x =
	  if hyp_in_pf_p d2 0 then
	    begin
	      try
	        let z = Hashtbl.find pfghyph d in
                if Hashtbl.mem pfgreserved z then raise Not_found;
                if List.mem z psi then raise Not_found;
                z
	      with Not_found ->
                nxtpfghyp psi
	    end
	  else
	    "_"
	in
	Printf.sprintf "PrLa %s %s %s" x (tm_pfgegal_str_r m1 phi) (pf_pfgegal_str_r d2 phi (x::psi))
      end
  | TLam(a1,d2) ->
      begin
	let x =
	  if free_in_pf_p d2 0 then
	    begin
	      try
	        let z = Hashtbl.find pfgpfbvarh d in
                if Hashtbl.mem pfgreserved z then raise Not_found;
                if List.mem z phi then raise Not_found;
                z
	      with Not_found ->
                nxtpfgvar phi
	    end
	  else
	    "_"
	in
	Printf.sprintf "TmLa %s %s %s" x (tp_pfgset_str a1) (pf_pfgegal_str_r d2 (x::phi) psi)
      end

let rec pf_pfgmiz_str_r d phi psi =
  match d with
  | Hyp(j) -> List.nth psi j
  | Known(h) -> (try Hashtbl.find pfgknh h with Not_found -> Printf.sprintf "#%s" h)
  | PTpAp(PTpAp(Known(h),a1),a2) when h = "5626ac8cb7c90418f6c980ffedd6f45097048659977d8690c44f9d34feb6b2d3" -> Printf.sprintf "Ext %s %s" (tp_pfgset_str a1) (tp_pfgset_str a2)
  | PTpAp(d1,a2) -> Printf.sprintf "TpAp %s %s" (pf_pfgmiz_str_r d1 phi psi) (tp_pfgset_str a2)
  | PTmAp(d1,m2) -> Printf.sprintf "TmAp %s %s" (pf_pfgmiz_str_r d1 phi psi) (tm_pfgmiz_str_r m2 phi)
  | PPfAp(d1,d2) -> Printf.sprintf "PrAp %s %s" (pf_pfgmiz_str_r d1 phi psi) (pf_pfgmiz_str_r d2 phi psi)
  | PLam(m1,d2) ->
      begin
	let x =
	  if hyp_in_pf_p d2 0 then
	    begin
	      try
	        let z = Hashtbl.find pfghyph d in
                if Hashtbl.mem pfgreserved z then raise Not_found;
                if List.mem z psi then raise Not_found;
                z
	      with Not_found ->
                nxtpfghyp psi
	    end
	  else
	    "_"
	in
	Printf.sprintf "PrLa %s %s %s" x (tm_pfgmiz_str_r m1 phi) (pf_pfgmiz_str_r d2 phi (x::psi))
      end
  | TLam(a1,d2) ->
      begin
	let x =
	  if free_in_pf_p d2 0 then
	    begin
	      try
	        let z = Hashtbl.find pfgpfbvarh d in
                if Hashtbl.mem pfgreserved z then raise Not_found;
                if List.mem z phi then raise Not_found;
                z
	      with Not_found ->
                nxtpfgvar phi
	    end
	  else
	    "_"
	in
	Printf.sprintf "TmLa %s %s %s" x (tp_pfgset_str a1) (pf_pfgmiz_str_r d2 (x::phi) psi)
      end

let rec pf_pfgsetmm_str_r d phi psi =
  match d with
  | Hyp(j) -> List.nth psi j
  | Known(h) -> (try Hashtbl.find pfgknh h with Not_found -> Printf.sprintf "#%s" h)
  | PTpAp(d1,a2) -> Printf.sprintf "TpAp %s %s" (pf_pfgsetmm_str_r d1 phi psi) (tp_pfgset_str a2)
  | PTmAp(d1,m2) -> Printf.sprintf "TmAp %s %s" (pf_pfgsetmm_str_r d1 phi psi) (tm_pfgsetmm_str_r m2 phi)
  | PPfAp(d1,d2) -> Printf.sprintf "PrAp %s %s" (pf_pfgsetmm_str_r d1 phi psi) (pf_pfgsetmm_str_r d2 phi psi)
  | PLam(m1,d2) ->
      begin
	let x =
	  if hyp_in_pf_p d2 0 then
	    begin
	      try
	        let z = Hashtbl.find pfghyph d in
                if Hashtbl.mem pfgreserved z then raise Not_found;
                if List.mem z psi then raise Not_found;
                z
	      with Not_found ->
                nxtpfghyp psi
	    end
	  else
	    "_"
	in
	Printf.sprintf "PrLa %s %s %s" x (tm_pfgsetmm_str_r m1 phi) (pf_pfgsetmm_str_r d2 phi (x::psi))
      end
  | TLam(a1,d2) ->
      begin
	let x =
	  if free_in_pf_p d2 0 then
	    begin
	      try
	        let z = Hashtbl.find pfgpfbvarh d in
                if Hashtbl.mem pfgreserved z then raise Not_found;
                if List.mem z phi then raise Not_found;
                z
	      with Not_found ->
                nxtpfgvar phi
	    end
	  else
	    "_"
	in
	Printf.sprintf "TmLa %s %s %s" x (tp_pfgset_str a1) (pf_pfgsetmm_str_r d2 (x::phi) psi)
      end

let rec pf_pfghoas_str_r d phi psi =
  match d with
  | Hyp(j) -> List.nth psi j
  | Known(h) -> (try Hashtbl.find pfgknh h with Not_found -> Printf.sprintf "#%s" h)
  | PTpAp(PTpAp(Known(h),a1),a2) when h = "5626ac8cb7c90418f6c980ffedd6f45097048659977d8690c44f9d34feb6b2d3" -> Printf.sprintf "Ext %s %s" (tp_pfgsyn_str a1) (tp_pfgsyn_str a2)
  | PTpAp(d1,a2) -> Printf.sprintf "TpAp %s %s" (pf_pfghoas_str_r d1 phi psi) (tp_pfgsyn_str a2)
  | PTmAp(d1,m2) -> Printf.sprintf "TmAp %s %s" (pf_pfghoas_str_r d1 phi psi) (tm_pfghoas_str_r m2 phi)
  | PPfAp(d1,d2) -> Printf.sprintf "PrAp %s %s" (pf_pfghoas_str_r d1 phi psi) (pf_pfghoas_str_r d2 phi psi)
  | PLam(m1,d2) ->
      begin
	let x =
	  if hyp_in_pf_p d2 0 then
	    begin
	      try
	        let z = Hashtbl.find pfghyph d in
                if Hashtbl.mem pfgreserved z then raise Not_found;
                if List.mem z psi then raise Not_found;
                z
	      with Not_found ->
                nxtpfghyp psi
	    end
	  else
	    "_"
	in
	Printf.sprintf "PrLa %s %s %s" x (tm_pfghoas_str_r m1 phi) (pf_pfghoas_str_r d2 phi (x::psi))
      end
  | TLam(a1,d2) ->
      begin
	let x =
	  if free_in_pf_p d2 0 then
	    begin
	      try
	        let z = Hashtbl.find pfgpfbvarh d in
                if Hashtbl.mem pfgreserved z then raise Not_found;
                if List.mem z phi then raise Not_found;
                z
	      with Not_found ->
                nxtpfgvar phi
	    end
	  else
	    "_"
	in
	Printf.sprintf "TmLa %s %s %s" x (tp_pfgsyn_str a1) (pf_pfghoas_str_r d2 (x::phi) psi)
      end

let tm_pfg_str m =
  pfgvarcount := 0;
  match !pfgtheory with
  | HF -> tm_pfghf_str_r m []
  | Egal -> tm_pfgegal_str_r m []
  | Mizar -> tm_pfgmiz_str_r m []
  | HOAS -> tm_pfghoas_str_r m []
  | SetMM -> tm_pfgsetmm_str_r m []

let pf_pfg_str d =
  pfgvarcount := 0;
  pfghypcount := 0;
  match !pfgtheory with
  | HF -> pf_pfghf_str_r d [] []
  | Egal -> pf_pfgegal_str_r d [] []
  | Mizar -> pf_pfgmiz_str_r d [] []
  | HOAS -> pf_pfghoas_str_r d [] []
  | SetMM -> pf_pfgsetmm_str_r d [] []

let pfg_prim_id_p h =
  match !pfgtheory with
  | HF -> Hashtbl.mem pfghfprim h
  | Egal -> Hashtbl.mem pfgegalprim h
  | Mizar -> Hashtbl.mem pfgmizprim h
  | HOAS -> Hashtbl.mem pfghoasprim h
  | SetMM -> Hashtbl.mem pfgsetmmprim h

let rec tp_ocaml a =
  match a with
  | Prop -> "Prop"
  | Set -> "Set"
  | Ar(a1,a2) -> Printf.sprintf "Ar(%s,%s)" (tp_ocaml a1) (tp_ocaml a2)
  | TpVar(i) -> Printf.sprintf "TpVar(%d)" i

let hoas_bind w = Ap(TmH("73c9efe869770ab42f7cde0b33fe26bbc3e2bd157dad141c0c27d1e7348d60f5"),Lam(Set,w))

(** nil := bind (fun x => x) **)
let hoas_nil () = hoas_bind (DB(0))

(** pair is Prim(0) **)
let hoas_pair m n = Ap(Ap(TmH("d58762d200971dcc7f1850726d9f2328403127deeba124fc3ba2d2d9f7c3cb8c"),m),n)

(** hex is a balanced binary tree of depth 2 with leaves from DB(0) and DB(1) **)
let hoas_hex_a h =
  hoas_pair
    (hoas_pair (DB((h lsr 3) land 1)) (DB((h lsr 2) land 1)))
    (hoas_pair (DB((h lsr 1) land 1)) (DB(h land 1)))

let hoas_hex h =
  hoas_bind (hoas_bind (hoas_hex_a h))

(** byte is a balanced binary tree of depth 3 with leaves from bit0 and bit1 **)
let hoas_byte_a by =
  hoas_pair (hoas_hex_a ((by lsr 4) land 15)) (hoas_hex_a (by land 15))

let hoas_byte by =
  hoas_bind (hoas_bind (hoas_byte_a by))

let rec var_free_in_pf_p d i =
  match d with
  | PTpAp(d1,a) -> var_free_in_pf_p d1 i
  | PTmAp(d1,m1) -> var_free_in_pf_p d1 i || free_in_tm_p m1 i
  | PPfAp(d1,d2) -> var_free_in_pf_p d1 i || var_free_in_pf_p d2 i
  | TLam(a1,d1) -> var_free_in_pf_p d1 (i+1)
  | PLam(p1,d1) -> free_in_tm_p p1 i || var_free_in_pf_p d1 i
  | _ -> false

let rec hyp_free_in_pf_p d i =
  match d with
  | Hyp(j) -> j = i
  | PTpAp(d1,a) -> hyp_free_in_pf_p d1 i
  | PTmAp(d1,m1) -> hyp_free_in_pf_p d1 i
  | PPfAp(d1,d2) -> hyp_free_in_pf_p d1 i || hyp_free_in_pf_p d2 i
  | TLam(a1,d1) -> hyp_free_in_pf_p d1 i
  | PLam(p1,d1) -> hyp_free_in_pf_p d1 (i+1)
  | _ -> false
  
let rec pftmsubst d i m  =
  match d with
  | PTpAp(d1,a) -> PTpAp(pftmsubst d1 i m,a)
  | PTmAp(d1,m1) -> PTmAp(pftmsubst d1 i m,tmsubst m1 i m)
  | PPfAp(d1,d2) -> PPfAp(pftmsubst d1 i m,pftmsubst d2 i m)
  | TLam(a1,d1) -> TLam(a1,pftmsubst d1 (i+1) m)
  | PLam(p1,d1) -> PLam(tmsubst p1 i m,pftmsubst d1 i m)
  | _ -> d

let rec pfsubst d l i e =
  match d with
  | Hyp(k) when k < i -> Hyp(k)
  | Hyp(k) when k = i -> pftmshift 0 l (pfshift 0 i e)
  | Hyp(k) when k > i -> Hyp(k-1)
  | PTpAp(d1,a) -> PTpAp(pfsubst d1 l i e,a)
  | PTmAp(d1,m1) -> PTmAp(pfsubst d1 l i e,m1)
  | PPfAp(d1,d2) -> PPfAp(pfsubst d1 l i e,pfsubst d2 l i e)
  | TLam(a1,d1) -> TLam(a1,pfsubst d1 (l+1) i e)
  | PLam(p1,d1) -> PLam(p1,pfsubst d1 l (i+1) e)
  | _ -> d

let varintb_pfg_size x =
  if x < 4 then
    4
  else if x < 20 then
    6
  else if x < 276 then
    10
  else
    18

let rec tp_pfg_size a =
  match a with
  | Ar(a,b) -> 2 + tp_pfg_size a + tp_pfg_size b
  | Prop -> 2
  | Set -> 5
  | _ -> 1

let rec tm_pfg_size m =
  match m with
  | Ap(TpAp(TmH(h),a1),Lam(_,m1)) when h = "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099" -> (* Ex *)
      4 + tp_pfg_size a1 + tm_pfg_size m1
  | Ap(Ap(TpAp(TmH(h),a),m1),m2) when h = "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a" -> (* Eq *)
      4 + tp_pfg_size a + tm_pfg_size m1 + tm_pfg_size m2
  | TmH(h) ->
     begin
       try
         let x =
           Hashtbl.find
             begin
               match !pfgtheory with
               | HF -> pfghfprim
               | Egal -> pfgegalprim
               | Mizar -> pfgmizprim
               | HOAS -> pfghoasprim
               | SetMM -> pfgsetmmprim
             end
             h
         in
         3 + varintb_pfg_size x
       with Not_found ->
         259
     end
  | DB(x) -> 3 + varintb_pfg_size x
  | Prim(x) -> 3 + varintb_pfg_size x
  | Ap(m1,m2) -> 3 + tm_pfg_size m1 + tm_pfg_size m2
  | Lam(a,m) -> 3 + tp_pfg_size a + tm_pfg_size m
  | Imp(m1,m2) -> 3 + tm_pfg_size m1 + tm_pfg_size m2
  | All(a,m) -> 3 + tp_pfg_size a + tm_pfg_size m
  | _ -> 16

let rec pf_pfg_size d =
  match d with
  | Hyp(i) -> 3 + varintb_pfg_size i
  | Known(_) -> 259
  | PTpAp(PTpAp(Known(h),a1),a2) when h = "5626ac8cb7c90418f6c980ffedd6f45097048659977d8690c44f9d34feb6b2d3" -> 3 + tp_pfg_size a1 + tp_pfg_size a2
  | PTmAp(d1,m2) -> 3 + pf_pfg_size d1 + tm_pfg_size m2
  | PPfAp(d1,d2) -> 3 + pf_pfg_size d1 + pf_pfg_size d2
  | PLam(m1,d2) -> 3 + tm_pfg_size m1 + pf_pfg_size d2
  | TLam(a1,d2) -> 3 + tp_pfg_size a1 + pf_pfg_size d2
  | _ -> 16

let rec reduce_pf d =
  match d with
  | PTpAp(d1,a) ->
     let (d1,b1) = reduce_pf d1 in
     (PTpAp(d1,a),b1)
  | PTmAp(TLam(_,d1),m) ->
     let d1a = normalize_pf d1 in
     (pftmsubst d1a 0 m,false)
  | PPfAp(PLam(_,d1),d2) ->
     let d1a = normalize_pf d1 in
     let d2a = normalize_pf d2 in
     (pfsubst d1a 0 0 d2a,false)
  | PTmAp(d1,m) ->
     let (d1,b1) = reduce_pf d1 in
     (PTmAp(d1,m),b1)
  | PPfAp(d1,d2) ->
     let (d1,b1) = reduce_pf d1 in
     let (d2,b2) = reduce_pf d2 in
     (PPfAp(d1,d2),b1 && b2)
  | PLam(p,d1) ->
     let (d1,b1) = reduce_pf d1 in
     (PLam(p,d1),b1)
  | TLam(a,d1) ->
     let (d1,b1) = reduce_pf d1 in
     (TLam(a,d1),b1)
  | _ -> (d,true)
and normalize_pf d =
  let (d,b) = reduce_pf d in
  if b then d else normalize_pf d

let rec optimize_pf_1 d =
  match d with
  | TLam(Ar(a1,Ar(a2,Prop)),PLam(Ap(Ap(DB(0),m1),m2),Hyp(0))) when a1 = a2 && m1 = m2 && not (free_in_tm_p m1 0) && tm_pfg_size m1 > 255 -> (** reflexivity of eq **)
      PTmAp(TLam(a1,TLam(Ar(a1,Ar(a2,Prop)),PLam(Ap(Ap(DB(0),DB(1)),DB(1)),Hyp(0)))),tmshift 0 (-1) m1)
  | PTmAp(d1,m1) ->
      begin
	let d1a = optimize_pf_1 d1 in
	let drb = PTmAp(d1a,m1) in
	match d1a with
	| TLam(a1,d1b) ->
	    let drc = pftmsubst d1b 0 m1 in
	    if pf_pfg_size drc < pf_pfg_size drb then
	      drc
	    else
	      drb
	| _ -> drb
      end
  | PPfAp(d1,d2) ->
      begin
	let d1a = optimize_pf_1 d1 in
	let d2a = optimize_pf_1 d2 in
	let drb = PPfAp(d1a,d2a) in
	match d1a with
	| PLam(p1,d1b) ->
	    let drc = pfsubst d1b 0 0 d2a in
	    if pf_pfg_size drc < pf_pfg_size drb then
	      drc
	    else
	      drb
	| _ -> drb
      end
  | TLam(a,d1) -> 
      begin
	let d1a = optimize_pf_1 d1 in
	let drb = TLam(a,d1a) in
	match d1a with
	| PTmAp(d1b,DB(0)) when not (var_free_in_pf_p d1b 0) ->
	    let drc = optimize_pf_1 (pftmshift 0 (-1) d1b) in
	    if pf_pfg_size drc < pf_pfg_size drb then
	      drc
	    else
	      drb
	| _ -> drb
      end
  | PLam(p1,d1) ->
      begin
	let d1a = optimize_pf_1 d1 in
	let drb = PLam(p1,d1a) in
	match d1a with 
	| PPfAp(d1b,Hyp(0)) when not (hyp_free_in_pf_p d1b 0) ->
	    let drc = optimize_pf_1 (pfshift 0 (-1) d1b) in
	    if pf_pfg_size drc < pf_pfg_size drb then
	      drc
	    else
	      drb
	| _ -> drb
      end
  | _ -> d
      
let optimize_pf_2 sgdelta sgtmof d tmcutoff pfcutoff =
  let htc : (tp list * tm,int) Hashtbl.t = Hashtbl.create 100 in
  let hc : (tp list * tm list * tm,int) Hashtbl.t = Hashtbl.create 100 in
  let hp : (tp list * tm list * tm,pf) Hashtbl.t = Hashtbl.create 100 in
  let rec g i cxtm cxpf cxpfa d p =
    match cxpf with
    | (q::cxpfr) ->
       if hyp_free_in_pf_p d i then
         g (i+1) cxtm cxpfr (q::cxpfa) d p
       else
         g i cxtm cxpfr cxpfa (pfshift i (-1) d) p
    | [] ->
       let cxpf = List.rev cxpfa in
       begin
         try
           let n = Hashtbl.find hc (cxtm,cxpf,p) in
           Hashtbl.replace hc (cxtm,cxpf,p) (n+1)
         with Not_found ->
           Hashtbl.add hc (cxtm,cxpf,p) 1
       end;
       begin
         try
           let e = Hashtbl.find hp (cxtm,cxpf,p) in
           if pf_pfg_size e < pf_pfg_size d then
             Hashtbl.replace hp (cxtm,cxpf,p) e
         with Not_found ->
           Hashtbl.add hp (cxtm,cxpf,p) d
       end
  in
  let rec f i cxtm cxpf cxtma d p =
    match cxtm with
    | (a::cxtmr) ->
       begin
         if var_free_in_pf_p d i || free_in_tm_p p i || List.exists (fun q -> free_in_tm_p q i) cxpf then
           f (i+1) cxtmr cxpf (a::cxtma) d p
         else
           let d1 = pftmshift i (-1) d in
           let p1 = tmshift i (-1) p in
           let cxpf1 = List.map (fun q -> tmshift i (-1) q) cxpf in
           f i cxtmr cxpf1 cxtma d1 p1
       end
    | [] -> g 0 (List.rev cxtma) cxpf [] d p
  in
  let rec h i cxtm cxtma m =
    match cxtm with
    | (a::cxtmr) ->
       begin
         if free_in_tm_p m i then
           h (i+1) cxtmr (a::cxtma) m
         else
           let m1 = tmshift i (-1) m in
           h i cxtmr cxtma m1
       end
    | [] ->
       let cxtm = List.rev cxtma in
       begin
         try
           let n = Hashtbl.find htc (cxtm,m) in
           Hashtbl.replace htc (cxtm,m) (n+1)
         with Not_found ->
           Hashtbl.add htc (cxtm,m) 1
       end
  in
  let rec process_tm cxtm m =
    if tm_pfg_size m > 32 then
      begin
        h 0 cxtm [] m;
        match m with
        | Ap(m1,m2) -> process_tm cxtm m1; process_tm cxtm m2
        | Lam(a1,m1) -> process_tm (a1::cxtm) m1
        | Imp(m1,m2) -> process_tm cxtm m1; process_tm cxtm m2
        | All(a1,m1) -> process_tm (a1::cxtm) m1
        | _ -> ()
      end
  in
  let rec optimize_pf_2_a cxtm cxpf d =
    if pf_pfg_size d > 32 then
      let (p,_) = extr_propofpf sgdelta sgtmof cxtm cxpf d [] in
      f 0 cxtm cxpf [] d p;
      match d with
      | PTmAp(d1,m1) -> process_tm cxtm m1; PTmAp(optimize_pf_2_a cxtm cxpf d1,m1)
      | PPfAp(d1,d2) -> PPfAp(optimize_pf_2_a cxtm cxpf d1,optimize_pf_2_a cxtm cxpf d2)
      | TLam(a1,d1) -> TLam(a1,optimize_pf_2_a (a1::cxtm) (List.map (fun q -> tmshift 0 1 q) cxpf) d1)
      | PLam(p1,d1) -> process_tm cxtm p1; PLam(p1,optimize_pf_2_a cxtm (p1::cxpf) d1)
      | _ -> d
    else
      d
  in
  let d = optimize_pf_2_a [] [] d in
  Hashtbl.iter
    (fun (cxtm,cxpf,p) n ->
      if n >= pfcutoff then
        Printf.printf "%% subpf %d %s\n" n (tm_to_str p))
    hc;
  Hashtbl.iter
    (fun (cxtm,m) n ->
      if n >= tmcutoff then
        Printf.printf "%% subtm %d %s\n" n (tm_to_str m))
    htc;
  d

exception NotFO

let tptp_id_name : (string,string * tp) Hashtbl.t = Hashtbl.create 100

let tptpize_name x =
  let l = String.length x in
  if l = 0 then
    "emptyname"
  else
    let y = Buffer.create 100 in
    let co = Char.code x.[0] in
    if not (co >= 97 && co <= 122) then Buffer.add_string y "c_";
    for i = 0 to (String.length x) - 1 do
      let c = x.[i] in
      let co = Char.code c in
      if (co >= 48 && co <= 57 || co >= 65 && co <= 90 || co >= 97 && co <= 122) then
        Buffer.add_char y c
      else
        begin
	  Buffer.add_char y '_';
	  Buffer.add_char y (hex_char ((co lsr 4) mod 16));
	  Buffer.add_char y (hex_char (co mod 16));
        end
    done;
    Buffer.contents y

let rec head_spine m sp =
  match m with
  | Ap(m1,m2) -> head_spine m1 (m2::sp)
  | _ -> (m,sp)

let rec fo_funtp_arity a =
  match a with
  | Set -> 0
  | Ar(Set,a) -> 1 + fo_funtp_arity a
  | _ -> raise NotFO

let rec fo_predtp_arity a =
  match a with
  | Prop -> 0
  | Ar(Set,a) -> 1 + fo_predtp_arity a
  | _ -> raise NotFO

let rec fo_gentp_arity a =
  match a with
  | Set -> (Set,0)
  | Prop -> (Prop,0)
  | Ar(Set,a) -> let (b,n) = fo_gentp_arity a in (b,1 + n)
  | _ -> raise NotFO

let rec fof_trm_str m cxtm n =
  let (h,sp) = head_spine m [] in
  match h with
  | DB(i) ->
     begin
       if sp = [] && i < n then
         begin
           let (x,a) = List.nth cxtm i in
           if a = Set then
             x
           else
             raise NotFO
         end
       else if n <= i then
         begin
           let (x,a) = List.nth cxtm i in
           let (b,n) = fo_gentp_arity a in
           if b = Set && n = List.length sp then
             if sp = [] then
               tptpize_name x
             else
               Printf.sprintf "%s(%s)" (tptpize_name x) (fof_spine_str sp cxtm n "")
           else
             raise NotFO
         end
       else
         raise NotFO
     end
  | TmH(h) ->
     begin
       try
         let (x,a) = Hashtbl.find tptp_id_name h in
         if fo_funtp_arity a = List.length sp then
           if a = Set then
             x
           else
             Printf.sprintf "%s(%s)" x (fof_spine_str sp cxtm n "")
         else
           raise NotFO
       with Not_found -> raise NotFO
     end
  | _ -> raise NotFO
and fof_spine_str sp cxtm n sep =
  match sp with
  | [] -> ""
  | m::spr -> Printf.sprintf "%s%s%s" sep (fof_trm_str m cxtm n) (fof_spine_str spr cxtm n ",")

let rec fof_prop_str m cxtm n =
  match m with
  | Imp(m1,m2) ->
     Printf.sprintf "(%s => %s)" (fof_prop_str m1 cxtm n) (fof_prop_str m2 cxtm n)
  | All(Set,m1) ->
     let x = Printf.sprintf "X%d" (List.length cxtm) in
     Printf.sprintf "(! [%s] : %s)" x (fof_prop_str m1 ((x,Set)::cxtm) (n+1))
  | TmH(h) when h = "5867641425602c707eaecd5be95229f6fd709c9b58d50af108dfe27cb49ac069" ->
     "$true"
  | TmH(h) when h = "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87" ->
     "$false"
  | Ap(TmH(h),m1) when h = "058f630dd89cad5a22daa56e097e3bdf85ce16ebd3dbf7994e404e2a98800f7f" ->
     Printf.sprintf "~ %s" (fof_prop_str m1 cxtm n)
  | Ap(Ap(TmH(h),m1),m2) when h = "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738" ->
     Printf.sprintf "(%s & %s)" (fof_prop_str m1 cxtm n) (fof_prop_str m2 cxtm n)
  | Ap(Ap(TmH(h),m1),m2) when h = "cfe97741543f37f0262568fe55abbab5772999079ff734a49f37ed123e4363d7" ->
     Printf.sprintf "(%s | %s)" (fof_prop_str m1 cxtm n) (fof_prop_str m2 cxtm n)
  | Ap(Ap(TmH(h),m1),m2) when h = "9c60bab687728bc4482e12da2b08b8dbc10f5d71f5cab91acec3c00a79b335a3" ->
     Printf.sprintf "(%s <=> %s)" (fof_prop_str m1 cxtm n) (fof_prop_str m2 cxtm n)
  | Ap(TpAp(TmH(h),a),Lam(_,m1)) when h = "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099" ->
     let x = Printf.sprintf "X%d" (List.length cxtm) in
     Printf.sprintf "(? [%s] : %s)" x (fof_prop_str m1 ((x,a)::cxtm) (n+1))
  | Ap(Ap(TpAp(TmH(h),a),m1),m2) when h = "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a" ->
     Printf.sprintf "(%s = %s)" (fof_trm_str m1 cxtm n) (fof_trm_str m2 cxtm n)
  | Ap(Ap(TpAp(TmH(h),a),m1),m2) when h = "7966a66a9bb198103c2a540ccd5ebebdff33c10843cc10eebfc98715e142989c" ->
     Printf.sprintf "~ (%s = %s)" (fof_trm_str m1 cxtm n) (fof_trm_str m2 cxtm n)
  | _ ->
     let (h,sp) = head_spine m [] in
     match h with
     | DB(i) ->
        if n <= i then
          begin
            let (x,a) = List.nth cxtm i in
            let (b,n) = fo_gentp_arity a in
            if b = Prop && n = List.length sp then
              if sp = [] then
                tptpize_name x
              else
                Printf.sprintf "%s(%s)" (tptpize_name x) (fof_spine_str sp cxtm n "")
            else
              raise NotFO
          end
        else
          raise NotFO
     | TmH(h) ->
        begin
          try
            let (x,a) = Hashtbl.find tptp_id_name h in
            if fo_predtp_arity a = List.length sp then
              if a = Prop then
                x
              else
                Printf.sprintf "%s(%s)" x (fof_spine_str sp cxtm n "")
            else
              raise NotFO
          with Not_found -> raise NotFO
        end
     | _ -> raise NotFO

let rec th0_stp_str a =
  match a with
  | Set -> "$i"
  | Prop -> "$o"
  | Ar(a,b) -> Printf.sprintf "(%s > %s)" (th0_stp_str a) (th0_stp_str b)
  | _ -> raise (Failure "no poly")
     
let rec th0_str m cxtm =
  match m with
  | DB(i) ->
     let (x,_) = List.nth cxtm i in
     x
  | TmH(h) when h = "5867641425602c707eaecd5be95229f6fd709c9b58d50af108dfe27cb49ac069" ->
     "$true"
  | TmH(h) when h = "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87" ->
     "$false"
  | TmH(h) when h = "058f630dd89cad5a22daa56e097e3bdf85ce16ebd3dbf7994e404e2a98800f7f" ->
     "(^ [P:$o] : (~ (P)))"
  | Ap(TmH(h),m1) when h = "058f630dd89cad5a22daa56e097e3bdf85ce16ebd3dbf7994e404e2a98800f7f" ->
     let r = th0_str m1 cxtm in
     if String.length r > 1 && r.[0] = '(' then
       Printf.sprintf "(~ %s)" r
     else
       Printf.sprintf "(~ (%s))" r
  | TmH(h) when h = "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738" ->
     "(^ [P:$o] : (^ [Q:$o] : (P & Q)))"
  | Ap(Ap(TmH(h),m1),m2) when h = "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738" ->
     Printf.sprintf "(%s & %s)" (th0_str m1 cxtm) (th0_str m2 cxtm)
  | TmH(h) when h = "cfe97741543f37f0262568fe55abbab5772999079ff734a49f37ed123e4363d7" ->
     "(^ [P:$o] : (^ [Q:$o] : (P | Q)))"
  | Ap(Ap(TmH(h),m1),m2) when h = "cfe97741543f37f0262568fe55abbab5772999079ff734a49f37ed123e4363d7" ->
     Printf.sprintf "(%s | %s)" (th0_str m1 cxtm) (th0_str m2 cxtm)
  | TmH(h) when h = "9c60bab687728bc4482e12da2b08b8dbc10f5d71f5cab91acec3c00a79b335a3" ->
     "(^ [P:$o] : (^ [Q:$o] : (P <=> Q)))"
  | Ap(Ap(TmH(h),m1),m2) when h = "9c60bab687728bc4482e12da2b08b8dbc10f5d71f5cab91acec3c00a79b335a3" ->
     Printf.sprintf "(%s <=> %s)" (th0_str m1 cxtm) (th0_str m2 cxtm)
  | TmH(h) ->
     let (x,_) = Hashtbl.find tptp_id_name h in
     x
  | Ap(TpAp(TmH(h),a),Lam(_,m1)) when h = "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099" ->
     let x = Printf.sprintf "X%d" (List.length cxtm) in
     Printf.sprintf "(? [%s:%s] : %s)" x (th0_stp_str a) (th0_str m1 ((x,a)::cxtm))
  | Ap(TpAp(TmH(h),a),m1) when h = "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099" ->
     let x = Printf.sprintf "X%d" (List.length cxtm) in
     Printf.sprintf "(? [%s:%s] : (%s @ %s))" x (th0_stp_str a) (th0_str m1 cxtm) x
  | TpAp(TmH(h),a) when h = "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099" ->
     Printf.sprintf "(^ [P:(%s > $o)] : (? [X:%s] : (P @ X)))" (th0_stp_str a) (th0_stp_str a)
  | TpAp(TmH(h),a) when h = "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a" ->
     Printf.sprintf "(^ [X:%s] : (^ [Y:%s] : (X = Y)))" (th0_stp_str a) (th0_stp_str a)
  | Ap(Ap(TpAp(TmH(h),a),m1),m2) when h = "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a" ->
     Printf.sprintf "(%s = %s)" (th0_str m1 cxtm) (th0_str m2 cxtm)
  | TpAp(TmH(h),a) when h = "7966a66a9bb198103c2a540ccd5ebebdff33c10843cc10eebfc98715e142989c" ->
     Printf.sprintf "(^ [X:%s] : (^ [Y:%s] : (~ (X = Y))))" (th0_stp_str a) (th0_stp_str a)
  | Ap(Ap(TpAp(TmH(h),a),m1),m2) when h = "7966a66a9bb198103c2a540ccd5ebebdff33c10843cc10eebfc98715e142989c" ->
     Printf.sprintf "(~ (%s = %s))" (th0_str m1 cxtm) (th0_str m2 cxtm)
  | Ap(m1,m2) -> Printf.sprintf "(%s @ %s)" (th0_str m1 cxtm) (th0_str m2 cxtm)
  | Imp(m1,m2) -> Printf.sprintf "(%s => %s)" (th0_str m1 cxtm) (th0_str m2 cxtm)
  | Lam(a,m1) ->
     let x = Printf.sprintf "X%d" (List.length cxtm) in
     Printf.sprintf "(^ [%s:%s] : %s)" x (th0_stp_str a) (th0_str m1 ((x,a)::cxtm))
  | All(a,m1) ->
     let x = Printf.sprintf "X%d" (List.length cxtm) in
     Printf.sprintf "(! [%s:%s] : %s)" x (th0_stp_str a) (th0_str m1 ((x,a)::cxtm))
  | _ ->
     raise (Failure (Printf.sprintf "unhandled th0_str case: %s" (tm_to_str m)))

let rec fof_def_str_r a d m cx =
  match a with
  | Set -> Printf.sprintf "(%s = %s)" (fof_trm_str d cx 0) (fof_trm_str m cx 0)
  | Prop -> Printf.sprintf "(%s <=> %s)" (fof_prop_str d cx 0) (fof_prop_str m cx 0)
  | Ar(Set,a2) ->
     let x = Printf.sprintf "X%d" (List.length cx) in
     Printf.sprintf "(! [%s:$i] : %s)" x (fof_def_str_r a2 (Ap(tmshift 0 1 d,DB(0))) (gen_lam_body m) ((x,Set)::cx))
  | _ -> raise NotFO

let fof_def_str a c m =
  fof_def_str_r a (TmH(c)) m []

let rec th0_def_str a c m =
  let (x,_) = Hashtbl.find tptp_id_name c in
  Printf.sprintf "(%s = %s)" x (th0_str m [])

let tm_deps m =
  let h : (tm,unit) Hashtbl.t = Hashtbl.create 10 in
  let rec tm_deps_h m =
    match m with
    | TmH(_) -> Hashtbl.replace h m ()
    | Prim(_) -> Hashtbl.replace h m ()
    | Ap(m1,m2) -> tm_deps_h m1; tm_deps_h m2
    | Imp(m1,m2) -> tm_deps_h m1; tm_deps_h m2
    | Lam(_,m1) -> tm_deps_h m1
    | All(_,m1) -> tm_deps_h m1
    | _ -> ()
  in
  tm_deps_h m;
  let r = ref [] in
  Hashtbl.iter (fun k () -> r := k::!r) h;
  !r

let rec pf_used d j usedknowns usedhyps =
  match d with
  | Hyp(i) -> if j <= i then Hashtbl.replace usedhyps (i-j) ()
  | Known(h) -> Hashtbl.replace usedknowns h ()
  | PTpAp(d1,_) -> pf_used d1 j usedknowns usedhyps
  | PTmAp(d1,_) -> pf_used d1 j usedknowns usedhyps
  | PPfAp(d1,d2) -> pf_used d1 j usedknowns usedhyps; pf_used d2 j usedknowns usedhyps
  | PLam(_,d1) -> pf_used d1 (j+1) usedknowns usedhyps
  | TLam(_,d1) -> pf_used d1 j usedknowns usedhyps

let logicop : (string,unit) Hashtbl.t = Hashtbl.create 100;;
Hashtbl.add logicop "5867641425602c707eaecd5be95229f6fd709c9b58d50af108dfe27cb49ac069" ();;
Hashtbl.add logicop "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87" ();;
Hashtbl.add logicop "058f630dd89cad5a22daa56e097e3bdf85ce16ebd3dbf7994e404e2a98800f7f" ();;
Hashtbl.add logicop "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738" ();;
Hashtbl.add logicop "cfe97741543f37f0262568fe55abbab5772999079ff734a49f37ed123e4363d7" ();;
Hashtbl.add logicop "9c60bab687728bc4482e12da2b08b8dbc10f5d71f5cab91acec3c00a79b335a3" ();;
Hashtbl.add logicop "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099" ();;
Hashtbl.add logicop "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a" ();;
Hashtbl.add logicop "7966a66a9bb198103c2a540ccd5ebebdff33c10843cc10eebfc98715e142989c" ();;
