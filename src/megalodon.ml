(* Copyright (c) 2026 AI4REASON *)
(* Copyright (c) 2020-2025 CIIRC (Czech Institute of Informatics, Robotics and Cybernetics) / CTU (Czech Technical University) *)

open Syntax
open Parser
open Megaauto
open Interpret

let preambleassig = ref false;;
let stm = ref "";;
let mycnt = ref 0;;
let archivefile = ref None;;
let allowincompleteqed = ref false;;
let trustdeclaredaxioms = ref false;;
let doublecheckpf = ref true;;
let maxbottlenecksreport = ref 3;;
let removepfs = ref None;;
let countremovedpfs = ref 0;;
let pfposinfo = ref [];;
let warnaboutreproven = ref false;;
let createabyprobs = ref false;;
let current_input_file : string option ref = ref None;;
let abyproblemscached = ref false;;
let sb : Buffer.t = Buffer.create 10000;;
let vampireaby : string option ref = ref None;;
let vampireabyoutdir : string ref = ref "vampire_aby";;
let vampireabytimeout : int ref = ref 60;;
let vampireabyschedule : string ref = ref "casc";;
let vampireabyproof : string ref = ref "tptp";;
let vampireabynative : bool ref = ref false;;
let vampireabynativestrict : bool ref = ref false;;
let vampireabyqualifying : bool ref = ref false;;
let vampireabytarget : (int * int) option ref = ref None;;
let vampireabytargetstop : bool ref = ref false;;
let vampirecertv1 : string option ref = ref None;;
let vampirecertv1source : string option ref = ref None;;
let vampirecertv1sourceaudit : bool ref = ref false;;
let vampirecertv1sourcecontext : bool ref = ref false;;
let vampirecertv1sourcecontextstrict : bool ref = ref false;;
let vampirecertv1strict : bool ref = ref false;;
let vampirecertv1closed : bool ref = ref false;;
let vampirecertv1coreclosed : bool ref = ref false;;
let vampirecertv1corepfcheck : bool ref = ref false;;
let vampirecertv1preprocesspfcheck : bool ref = ref false;;
let vampirecertv1emit : string option ref = ref None;;
let vampirechecklivepropchoice : bool ref = ref false;;
let bushy = ref false;;
let bushykdeps : (string,unit) Hashtbl.t = Hashtbl.create 10;;
let bushyhdeps : (int,unit) Hashtbl.t = Hashtbl.create 10;;
let fofskip : (string,unit) Hashtbl.t = Hashtbl.create 10;;
let th0skip : (string,unit) Hashtbl.t = Hashtbl.create 10;;
let usedknowns : (string,unit) Hashtbl.t = Hashtbl.create 10;;
let usedhyps : (int,unit) Hashtbl.t = Hashtbl.create 10;;
Hashtbl.add th0skip "5867641425602c707eaecd5be95229f6fd709c9b58d50af108dfe27cb49ac069" ();;
Hashtbl.add th0skip "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87" ();;
Hashtbl.add th0skip "058f630dd89cad5a22daa56e097e3bdf85ce16ebd3dbf7994e404e2a98800f7f" ();;
Hashtbl.add th0skip "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738" ();;
Hashtbl.add th0skip "cfe97741543f37f0262568fe55abbab5772999079ff734a49f37ed123e4363d7" ();;
Hashtbl.add th0skip "9c60bab687728bc4482e12da2b08b8dbc10f5d71f5cab91acec3c00a79b335a3" ();;
Hashtbl.add th0skip "8c71cf7ec1276527982a30a7e0cf59ab0066fe232b08a93bde0e96f04bd3c61e" ();;
Hashtbl.add th0skip "294aa57cc6984370c318cea497711321b40c0f0b05ee524a6d5aa73e794e39ea" ();;
Hashtbl.add th0skip "b20fe08e4deecde7da240694359a1d03879d693ecedd05b8558b7c8f97a27068" ();;
Hashtbl.add th0skip "7f6246d08629eeb16eab93529ffe4f929f43344833ab88c7786393693520e82b" ();;
Hashtbl.add th0skip "eb8814e5b67181dcc2fdd7f757e9f1e3c90bcd9b3117f2bb9aa7650cdaac5b42" ();;
Hashtbl.add th0skip "fec5ab340a042c8361bb0564ac980cfe10dabcf5c4aeacb0746c0daa4ac55417" ();;
Hashtbl.add th0skip "d5fdb4f6cfb82cab64716bee0629544da9b7530752eb0873529def98362fd6b4" ();;
Hashtbl.add th0skip "5ee4a4103f04cabe781fcdc73566d7dd74b33cb621a83145e1fcff8855469827" ();;
Hashtbl.add th0skip "22deae75a52553214777cb58d8b2125e35bc3126ecd8ebda4ac09b1d2797aa65" ();;
Hashtbl.add th0skip "bf8d387a1cdc4c9dea0b7e95765cc5b16227b88778c3fb3744c9fbc25117af2b" ();;
Hashtbl.add th0skip "ae12f3d888f0852224b7800963449ca794c37e1ea961e7055db83b51de0c6cc9" ();;
Hashtbl.add th0skip "bfd151f806ea28dc7a1dc0837502b7ceb6f8c9d6f8ca53206a01a29e23c88acf" ();;
Hashtbl.add th0skip "5a4bbc1e6228cfca5f449799d8b79de665c1a48f3d2119d65f9309c4242d2cf7" ();;

Hashtbl.add fofskip "5867641425602c707eaecd5be95229f6fd709c9b58d50af108dfe27cb49ac069" ();;
Hashtbl.add fofskip "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87" ();;
Hashtbl.add fofskip "058f630dd89cad5a22daa56e097e3bdf85ce16ebd3dbf7994e404e2a98800f7f" ();;
Hashtbl.add fofskip "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738" ();;
Hashtbl.add fofskip "cfe97741543f37f0262568fe55abbab5772999079ff734a49f37ed123e4363d7" ();;
Hashtbl.add fofskip "9c60bab687728bc4482e12da2b08b8dbc10f5d71f5cab91acec3c00a79b335a3" ();;
Hashtbl.add fofskip "8c71cf7ec1276527982a30a7e0cf59ab0066fe232b08a93bde0e96f04bd3c61e" ();;
Hashtbl.add fofskip "294aa57cc6984370c318cea497711321b40c0f0b05ee524a6d5aa73e794e39ea" ();;
Hashtbl.add fofskip "b20fe08e4deecde7da240694359a1d03879d693ecedd05b8558b7c8f97a27068" ();;
Hashtbl.add fofskip "7f6246d08629eeb16eab93529ffe4f929f43344833ab88c7786393693520e82b" ();;
Hashtbl.add fofskip "eb8814e5b67181dcc2fdd7f757e9f1e3c90bcd9b3117f2bb9aa7650cdaac5b42" ();;
Hashtbl.add fofskip "fec5ab340a042c8361bb0564ac980cfe10dabcf5c4aeacb0746c0daa4ac55417" ();;
Hashtbl.add fofskip "d5fdb4f6cfb82cab64716bee0629544da9b7530752eb0873529def98362fd6b4" ();;
Hashtbl.add fofskip "5ee4a4103f04cabe781fcdc73566d7dd74b33cb621a83145e1fcff8855469827" ();;
Hashtbl.add fofskip "22deae75a52553214777cb58d8b2125e35bc3126ecd8ebda4ac09b1d2797aa65" ();;
Hashtbl.add fofskip "bf8d387a1cdc4c9dea0b7e95765cc5b16227b88778c3fb3744c9fbc25117af2b" ();;
Hashtbl.add fofskip "ae12f3d888f0852224b7800963449ca794c37e1ea961e7055db83b51de0c6cc9" ();;
Hashtbl.add fofskip "bfd151f806ea28dc7a1dc0837502b7ceb6f8c9d6f8ca53206a01a29e23c88acf" ();;
Hashtbl.add fofskip "5a4bbc1e6228cfca5f449799d8b79de665c1a48f3d2119d65f9309c4242d2cf7" ();;

let fof : string option ref = ref None
let fofallsubgoals : bool ref = ref false
let fofpostsubgoals : bool ref = ref false
let fofsubgoalcnt : int ref = ref 0
let th0 : string option ref = ref None
let th0ps1 : bool ref = ref false
let th0singlesubgoal : (int * int) option ref = ref None
let th0allsubgoals : bool ref = ref false
let th0postsubgoals : bool ref = ref false
let th0subgoalcnt : int ref = ref 0
let sexprallsubgoals_inclfile : out_channel option ref = ref None
let sexprallsubgoals : (string * string * int) option ref = ref None
let normalizepf : bool ref = ref false
let optimizepf1 : bool ref = ref false
let optimizepf2 : bool ref = ref false
let optimizepf2tc : int ref = ref 99
let optimizepf2pc : int ref = ref 99
let reporteachitem : bool ref = ref false
let reportids : bool ref = ref true
let reportpfcomplexity : bool ref = ref false
let webout : bool ref = ref false
let ajax : bool ref = ref false
let ajaxactive : bool ref = ref false
let ajaxpffile : string ref = ref ""
let sqlout : bool ref = ref false
let sqltermout : bool ref = ref false
let presentationonly : bool ref = ref false
let mainfilehash : string option ref = ref None
let solvesproblemfile : string option ref = ref None

let thmsasexercises : bool ref = ref false
let exercises : string list ref = ref []

let indoutfile : string option ref = ref None;;
let indextms : (string,tp) Hashtbl.t = Hashtbl.create 1000;;
let indexknowns : (string,unit) Hashtbl.t = Hashtbl.create 1000;;
let ownedoutfile : string option ref = ref None;;
let ownedobj : (Hash.hashval,unit) Hashtbl.t = Hashtbl.create 1000;;
let ownedprop : (Hash.hashval,unit) Hashtbl.t = Hashtbl.create 1000;;


let combsigtm sgtmloc secstack =
  (List.concat
     (List.map (fun l -> List.map (fun (x,m,a,n,b) -> (x,(n,b))) l)
	(sgtmloc::(List.map (fun (_,_,_,stl,_) -> stl) secstack))))

exception AdmittedPf

let admitlinecnt : (int,int) Hashtbl.t = Hashtbl.create 10

let getadmitnumlineno () =
  try
    let n = Hashtbl.find admitlinecnt !lineno in
    Hashtbl.add admitlinecnt !lineno (n+1);
    n+1
  with Not_found ->
    Hashtbl.add admitlinecnt !lineno 0;
    0

let fofsg = ref []
let th0sg = ref []
let th0sgps1 = ref []

let fofp () = not (!fof = None)
let th0p () = not (!th0 = None) || not (!vampireaby = None)

let read_aby_script fn =
  let f = open_in fn in
  let rl = ref [] in
  try
    while true do
      let l = input_line f in
      if String.length l > 4 then
        let prefix = String.sub l 0 4 in
        if prefix = "th0:" then
          rl := (2,String.sub l 4 (String.length l - 4))::!rl
        else if prefix = "fof:" then
          rl := (1,String.sub l 4 (String.length l - 4))::!rl
    done;
    raise End_of_file
  with End_of_file ->
        close_in f;
        List.rev !rl

let rec tptpizecxtm cxtm =
  match cxtm with
  | [] -> []
  | (x,(a,Some(_)))::cxtmr -> tptpizecxtm cxtmr
  | (x,(a,None))::cxmtr -> (tptpize_name x,a)::tptpizecxtm cxmtr

let admitpfstateatp pfst =
  if !pfgtheory = Egal then
    match pfst with
    | PfStateGoal(startpos,atm,cxtm,cxpf) ->
       begin
         begin
           match !fof with
           | Some(c) when not !createabyprobs ->
              begin
                try
                  let z = fof_prop_str atm (tptpizecxtm cxtm) 0 in (** only if the conclusion is FO **)
                  let n = getadmitnumlineno() in
                  let fn =
                    if n = 0 then
                      Printf.sprintf "%s.%d.fof.p" c !lineno
                    else
                      Printf.sprintf "%s.%d.%d.fof.p" c !lineno n
                  in
                  let conjn =
                    if n = 0 then
                      Printf.sprintf "%s_%d" c !lineno
                    else
                      Printf.sprintf "%s_%d_%d" c !lineno n
                  in
                  let ch = open_out fn in
                  List.iter
                    (fun (_,_,_,a) -> Printf.fprintf ch "%s\n" a)
                    (List.rev !fofsg);
                  List.iter
                    (fun (x,p) ->
                      try
                        let a = fof_prop_str p (tptpizecxtm cxtm) 0 in
                        Printf.fprintf ch "fof(%s,axiom,%s).\n" (tptpize_name x) a
                      with NotFO -> ())
                    (List.rev cxpf);
                  Printf.fprintf ch "fof(conj_%s,conjecture,%s).\n" conjn z;
                  close_out ch
                with NotFO -> ()
              end
           | _ -> ()
         end;
         begin
           match !th0 with
           | Some(c) when not !createabyprobs && !th0singlesubgoal = None ->
              begin
                let n = getadmitnumlineno() in
                let fn =
                  if n = 0 then
                    Printf.sprintf "%s.%d.th0.p" c !lineno
                  else
                    Printf.sprintf "%s.%d.%d.th0.p" c !lineno n
                in
                let conjn =
                  if n = 0 then
                    Printf.sprintf "%s_%d" c !lineno
                  else
                    Printf.sprintf "%s_%d_%d" c !lineno n
                in
                if !th0ps1 then
                  begin
                    let inconj : (tm,unit) Hashtbl.t = Hashtbl.create 100 in
                    let rec trm_ps1 m =
                      match m with
                      | Prim(_) -> Hashtbl.replace inconj m ()
                      | TmH(h) when not (Hashtbl.mem logicop h) -> Hashtbl.replace inconj m ()
                      | Ap(m1,m2) -> trm_ps1 m1; trm_ps1 m2
                      | Lam(_,m1) -> trm_ps1 m1
                      | Imp(m1,m2) -> trm_ps1 m1; trm_ps1 m2
                      | All(_,m1) -> trm_ps1 m1
                      | _ -> ()
                    in
                    let rec th0_cx_ps1 cxtm =
                      match cxtm with
                      | [] -> ()
                      | (x,(a,d))::cxtmr ->
                         th0_cx_ps1 cxtmr;
                         match d with
                         | Some(d) -> trm_ps1 d
                         | None -> ()
                    in
                    th0_cx_ps1 cxtm;
                    List.iter
                      (fun (_,p) -> trm_ps1 p)
                      cxpf;
                    trm_ps1 atm;
                    let ch = open_out fn in
                    let rec th0_cx cxtm =
                      match cxtm with
                      | [] -> ()
                      | (x,(a,d))::cxtmr ->
                         th0_cx cxtmr;
                         Printf.fprintf ch "thf(%s_tp,type,(%s : %s)).\n" (tptpize_name x) (tptpize_name x) (th0_stp_str a);
                         match d with
                         | Some(d) ->
                            Printf.fprintf ch "thf(%s_def,definition,(%s = %s)).\n" (tptpize_name x) (tptpize_name x) (th0_str d (tptpizecxtm cxtmr))
                         | None -> ()
                    in
                    th0_cx cxtm;
                    List.iter
                      (fun (deps,a) ->
                        match deps with
                        | None -> Printf.fprintf ch "%s\n" a
                        | Some(hl) ->
                           if List.exists (fun h -> Hashtbl.mem inconj h) hl then
                             Printf.fprintf ch "%s\n" a)
                      (List.rev !th0sgps1);
                    let cnt = ref 0 in
                    List.iter
                      (fun (x,p) ->
                        incr cnt;
                        if not !bushy || Hashtbl.mem bushyhdeps !cnt then
                          let a = th0_str p (tptpizecxtm cxtm) in
                          Printf.fprintf ch "thf(%s,axiom,%s).\n" (tptpize_name x) a)
                      (List.rev cxpf);
                    Printf.fprintf ch "thf(conj_%s,conjecture,%s).\n" conjn (th0_str atm (tptpizecxtm cxtm));
                    close_out ch
                  end
                else
                  begin
                    let ch = open_out fn in
                    List.iter
                      (fun (_,_,_,a) -> Printf.fprintf ch "%s\n" a)
                      (List.rev !th0sg);
                    let rec th0_cx cxtm =
                      match cxtm with
                      | [] -> ()
                      | (x,(a,d))::cxtmr ->
                         th0_cx cxtmr;
                         Printf.fprintf ch "thf(%s_tp,type,(%s : %s)).\n" (tptpize_name x) (tptpize_name x) (th0_stp_str a);
                         match d with
                         | Some(d) ->
                            Printf.fprintf ch "thf(%s_def,definition,(%s = %s)).\n" (tptpize_name x) (tptpize_name x) (th0_str d (tptpizecxtm cxtmr))
                         | None -> ()
                    in
                    th0_cx cxtm;
                    let cnt = ref 0 in
                    List.iter
                      (fun (x,p) ->
                        incr cnt;
                        if not !bushy || Hashtbl.mem bushyhdeps !cnt then
                          let a = th0_str p (tptpizecxtm cxtm) in
                          Printf.fprintf ch "thf(%s,axiom,%s).\n" (tptpize_name x) a)
                      (List.rev cxpf);
                    Printf.fprintf ch "thf(conj_%s,conjecture,%s).\n" conjn (th0_str atm (tptpizecxtm cxtm));
                    close_out ch
                  end
              end
           | _ -> ()
         end;
       end
    | _ -> ()
             
let rec map_for f i n =
  if i <= n then
    (f i::map_for f (i+1) n)
  else
    [];;

let rec split_list n l =
  if n > 0 then
    match l with
    | (a::r) ->
      let (l1,l2) = split_list (n-1) r in
      (a::l1,l2)
    | [] -> ([],[])
  else
    ([],l)

let extract_pfg_id l =
  let ll = String.length l in
  let i = ref 0 in
  let spc = ref 0 in
  let rv = ref None in
  while !i < ll && !rv = None do
    let c = l.[!i] in
    incr i;
    if c = ' ' then incr spc;
    if !spc = 3 then rv := Some(String.sub l !i 64)
  done;
  begin
    match !rv with
    | Some(r) -> Hash.hexstring_hashval r
    | None -> raise (Failure "bad owned file line")
  end

(* Trusted are proved only with things that were proved or trusted because in owned or index *)
let istrustedhash = Hashtbl.create 1000;;
Hashtbl.add istrustedhash "5626ac8cb7c90418f6c980ffedd6f45097048659977d8690c44f9d34feb6b2d3" ();; (* Egal / Ext *)
let sigknh_rev : (string,string) Hashtbl.t  = Hashtbl.create 1000;;
let rec istrusted name = function
  | Hyp(_) -> ()
  | Known(h) ->
     begin
       if Hashtbl.mem istrustedhash h then ()
       else
         try
           let localname = Hashtbl.find sigknh_rev h in (* They are axioms so we cannot use pfg reverse mapping *)
           failwith (Printf.sprintf "Theorem %s ends with Qed but should not as it depends on non-proved %s" name localname)
         with
           Not_found -> failwith (Printf.sprintf "Theorem %s ends with Qed but should not as it depends on non-proved %s" name h)
     end
  | PTpAp(d1,a2) -> istrusted name d1
  | PTmAp(d1,m2) -> istrusted name d1
  | PPfAp(d1,d2) -> istrusted name d1; istrusted name d2
  | PLam(m1,d2) -> istrusted name d2
  | TLam(a1,d2) -> istrusted name d2;;

let read_ownedfile c =
  try
    while true do
      let l = input_line c in
      if String.length l >= 68 && String.sub l 0 4 = "Obj " then
        Hashtbl.add ownedobj (extract_pfg_id l) ()
      else if String.length l >= 69 && String.sub l 0 5 = "Prop " then
        Hashtbl.add ownedprop (extract_pfg_id l) ()
    done
  with End_of_file -> ()

let read_indexfile c =
  let tl = ref (TokStrRest(Lexer.token,Lexing.from_channel c)) in
  lineno := 1;
  charno := 0;
  try
    while true do
      let (iitem,tr) = parse_indexitem !tl in
      tl := tr;
      match iitem with
      | IndexTm(h,a) ->
	  if not (valid_id_p h) then raise (Failure(h ^ " in index file is not a valid id"));
	  let a = ltree_to_atree a in
	  let atp = extract_tp a [] in
          if !verbosity > 10 then Printf.printf "  Hashtbl.add indextms \"%s\" (%s);\n" h (tp_ocaml atp);
	  begin
	    try
	      let itp = Hashtbl.find indextms h in
	      if itp <> atp then raise (Failure("Mismatch in indexed type assignment for " ^ h))
	    with Not_found ->
	      Hashtbl.add indextms h atp
	  end
      | IndexKnown(h) ->
	  if not (valid_id_p h) then raise (Failure(h ^ " in index file is not a valid id"));
          if !verbosity > 10 then Printf.printf "  Hashtbl.add indexknowns \"%s\" ();\n" h;
	  Hashtbl.replace indexknowns h ();
          Hashtbl.replace istrustedhash h ()
    done
  with
  | Lexer.Eof ->
      ()
  | Failure(x) ->
      if !webout then
	begin
          Printf.printf "AF%d:%d\n"  !lineno !charno;
	  Printf.printf "<div class='documentfail'>Failure reading index file at line %d char %d: %s</div>" !lineno !charno x; flush stdout;
	  exit 1
	end
      else if !ajax then
	begin
	  Printf.printf "f\n" (*** this indicates a fundamental problem, not a problem with the ajax input ***)
	end
      else
	begin
	  Printf.printf "Failure reading index file at line %d char %d: %s\n" !lineno !charno x; flush stdout;
	  exit 1
	end

let latex = ref None;;
let html = ref None;;
let htmlonlypfgsupp = ref false;;
let supported = ref false;;
let pfgsuppparam : (string,unit) Hashtbl.t = Hashtbl.create 100;;
let pfgsuppdef : (string,unit) Hashtbl.t = Hashtbl.create 100;;
let pfgsuppknown : (string,unit) Hashtbl.t = Hashtbl.create 100;;
let pfgsuppthm : (string,unit) Hashtbl.t = Hashtbl.create 100;;
type megawiki_state = { ddir:string; tdir:string; cdir:string };;
type megawiki_thm_state =
  {
    hash:string;
    name:string;
    tempfile:string;
    tmpout:out_channel;
    statement_html:string;
  };;
let megawiki : megawiki_state option ref = ref None;;
let megawiki_thm : megawiki_thm_state option ref = ref None;;
let inchan = ref None;; (*** This is a possible second channel for reading the input file currently used to record a literal copy of the text of proofs ***)
let inchanline = ref 1;;
let inchanchar = ref 0;;
let includingsigfile = ref false;;
let includedsigfiles = ref [];;
let sigoutfile = ref None;;
let pfgout = ref false;;
let pfgsummary = ref false;;
type pfgitem = PfgParam of string * string * tp | PfgDef of string * string * tp * tm | PfgKnown of string * string * tm | PfgThm of string * string * tm * pf | PfgConj of string * string * tm
let pfgmain : pfgitem list ref = ref [];;
let pfgdelta : (string,unit) Hashtbl.t = Hashtbl.create 100;;
let pfgtmph : (string,string * tp * (tm option)) Hashtbl.t = Hashtbl.create 100;;
let pfgknph : (string,tm) Hashtbl.t = Hashtbl.create 100;;
let sigtmh : (string,string) Hashtbl.t  = Hashtbl.create 1000;;
let sigknh : (string,string) Hashtbl.t  = Hashtbl.create 1000;;
let sigtmof : (string,ptp) Hashtbl.t  = Hashtbl.create 1000;;
let sigdelta : (string,ptm) Hashtbl.t = Hashtbl.create 1000;;
let sigdelta_opaque : (string,ptm) Hashtbl.t = Hashtbl.create 1000;;
let sigtm = ref (Hashtbl.create 100);;
let sigpf = ref [];;

let trusted_classical_xm_axiom name poly proposition =
  name = "xm"
  && poly = 0
  &&
    let expected =
      All(Prop,Ap(Ap(TmH(!disj),DB(0)),Imp(DB(0),TmH(!fal))))
    in
    try
      match conv proposition expected sigdelta [] with
      | Some _ -> true
      | None -> false
    with _ -> false

let polytm = ref [];;
let polypf = ref [];;
let futurepolytm = ref [];;
let futurepolypf = ref [];;
let handlepolysnow () =
  polytm := !futurepolytm @ !polytm;
  polypf := !futurepolypf @ !polypf;
  futurepolytm := [];
  futurepolypf := [];;
let pushpolytm a = futurepolytm := a::!futurepolytm;;
let pushpolypf a = futurepolypf := a::!futurepolypf;;

let ensure_directory path =
  if Sys.file_exists path then
    begin
      let st = Unix.stat path in
      if st.Unix.st_kind <> Unix.S_DIR then
        raise (Failure(Printf.sprintf "%s exists but is not a directory" path))
    end
  else
    Unix.mkdir path 0o755

let rec string_contains_at s needle i =
  let sl = String.length s in
  let nl = String.length needle in
  if nl = 0 then
    true
  else if i + nl > sl then
    false
  else if String.sub s i nl = needle then
    true
  else
    string_contains_at s needle (i+1)

let string_contains_sub s needle = string_contains_at s needle 0

let native_certificate_start_marker = "megalodon_certificate_native_sexpr_start."
let native_certificate_end_marker = "megalodon_certificate_native_sexpr_end."

let native_certificate_payload output =
  let lines = String.split_on_char '\n' output in
  let rec scan collecting acc = function
    | [] -> None
    | line :: rest ->
        let trimmed = String.trim line in
        if trimmed = native_certificate_start_marker then
          scan true [] rest
        else if trimmed = native_certificate_end_marker then
          if collecting then Some (String.concat "\n" (List.rev acc) ^ "\n")
          else scan false [] rest
        else if collecting then
          scan true (line :: acc) rest
        else
          scan false acc rest
  in
  scan false [] lines

let rec read_process_lines ch b =
  try
    Buffer.add_string b (input_line ch);
    Buffer.add_char b '\n';
    read_process_lines ch b
  with End_of_file -> ()

let run_command_capture cmd =
  let ch = Unix.open_process_in cmd in
  let b = Buffer.create 4096 in
  read_process_lines ch b;
  let status = Unix.close_process_in ch in
  (Buffer.contents b,status)

let vampire_output_proved s =
  string_contains_sub s "SZS status Theorem"
  || string_contains_sub s "SZS status Unsatisfiable"
  || string_contains_sub s "SZS status ContradictoryAxioms"

let vampire_output_has_native_certificate s =
  match native_certificate_payload s with
  | Some _ -> true
  | None -> false

let vampire_output_has_proof_payload s =
  string_contains_sub s "inference("
  || string_contains_sub s "SZS output start Proof"
  || string_contains_sub s "Refutation"
  || string_contains_sub s "end vamproof"
  || string_contains_sub s "theorem fullProof"
  || string_contains_sub s "theorem full_proof"
  || (string_contains_sub s native_certificate_start_marker
      && string_contains_sub s native_certificate_end_marker)
  || (string_contains_sub s "megalodon_reconstruction_start."
      && string_contains_sub s "megalodon_step("
      && string_contains_sub s "megalodon_final_step("
      && string_contains_sub s "megalodon_reconstruction_end.")

let vampire_proof_options proof =
  match proof with
  | "leancheck" -> "--output_mode lean --proof_extra lean --skolemization syntactic --shuffle_input off"
  | "megalodon" -> "--proof_extra lean --skolemization syntactic --shuffle_input off"
  | _ -> ""

let status_to_string status =
  match status with
  | Unix.WEXITED n -> Printf.sprintf "exit %d" n
  | Unix.WSIGNALED n -> Printf.sprintf "signal %d" n
  | Unix.WSTOPPED n -> Printf.sprintf "stopped %d" n

let vampire_source_context_delta () =
  let delta = Hashtbl.copy sigdelta in
  Hashtbl.iter
    (fun h v ->
       if not (Hashtbl.mem delta h) then Hashtbl.add delta h v)
    sigdelta_opaque;
  delta

let vampire_source_context_delta_with_locals cxtm =
  let rec local_terms proof_index = function
    | [] -> []
    | (_, (_, Some _)) :: rest -> local_terms proof_index rest
    | (name, (tp, None)) :: rest ->
        (name, proof_index, tp) :: local_terms (proof_index + 1) rest
  in
  let local_terms = local_terms 0 cxtm in
  let rec localize depth = function
    | TmH name ->
        begin match List.find_opt (fun (local_name, _, _) -> local_name = name) local_terms with
        | Some (_, index, _) -> DB (index + depth)
        | None -> TmH name
        end
    | TpAp (body, tp) -> TpAp (localize depth body, tp)
    | Ap (left, right) -> Ap (localize depth left, localize depth right)
    | Lam (tp, body) -> Lam (tp, localize (depth + 1) body)
    | Imp (left, right) -> Imp (localize depth left, localize depth right)
    | All (tp, body) -> All (tp, localize (depth + 1) body)
    | DB _ | Prim _ as tm -> tm
  in
  let delta = vampire_source_context_delta () in
  List.iter
    (fun (name, (_, definition)) ->
       match definition with
       | Some tm ->
           Hashtbl.replace delta name (0, localize 0 tm)
       | None -> ())
    cxtm;
  delta

let vampire_source_map_entry_aliases entry =
  let add_name name names =
    if name = "" || List.mem name names then names else name :: names
  in
  let add_hash_name name names =
    if name = "" || name.[0] = '#' then names
    else add_name ("#" ^ name) names
  in
  []
  |> add_name entry.Vampire_cert_v1.source_map_tptp_name
  |> add_name entry.Vampire_cert_v1.source_map_source_name
  |> add_hash_name entry.Vampire_cert_v1.source_map_tptp_name
  |> add_hash_name entry.Vampire_cert_v1.source_map_source_name
  |> List.rev

let vampire_source_context_add_source_map_aliases delta source_map =
  let add_term_alias alias source_name =
    if alias <> "" && source_name <> "" then
      match Hashtbl.find_opt sigtmh source_name with
      | Some hash -> Hashtbl.replace delta alias (0, TmH hash)
      | None -> ()
  in
  List.iter
    (fun entry ->
       let kind = entry.Vampire_cert_v1.source_map_kind in
       let hash = entry.Vampire_cert_v1.source_map_hash in
       List.iter
         (fun alias ->
            add_term_alias
              alias
              entry.Vampire_cert_v1.source_map_source_name)
         (vampire_source_map_entry_aliases entry);
       if (kind = "def" || kind = "definition" || kind = "local_definition")
          && hash <> "" then
         match Hashtbl.find_opt delta hash with
         | None -> ()
         | Some definition ->
             begin match Hashtbl.find_opt sigtmh entry.Vampire_cert_v1.source_map_source_name with
             | Some live_hash ->
                 Hashtbl.replace delta live_hash definition
             | None -> ()
             end;
             List.iter
               (fun alias -> Hashtbl.replace delta alias definition)
               (vampire_source_map_entry_aliases entry))
    source_map;
  delta

let vampire_source_context_add_local_type_aliases delta cxtm source_map =
  let rec local_terms proof_index = function
    | [] -> []
    | (_, (_, Some _)) :: rest -> local_terms proof_index rest
    | (name, (tp, None)) :: rest ->
        (name, proof_index, tp) :: local_terms (proof_index + 1) rest
  in
  let local_terms = local_terms 0 cxtm in
  List.iter
    (fun entry ->
       if entry.Vampire_cert_v1.source_map_kind = "local_type" then
         match
           List.find_opt
             (fun (local_name, _, _) ->
                local_name = entry.Vampire_cert_v1.source_map_source_name)
             local_terms
         with
         | Some (_, index, _) ->
           List.iter
             (fun alias ->
                Hashtbl.replace delta alias (0, DB index))
             (vampire_source_map_entry_aliases entry)
       | None -> ())
    source_map;
  delta

let vampire_source_context_delta_with_source_map ?cxtm source_map =
  let delta =
    match cxtm with
    | Some cxtm -> vampire_source_context_delta_with_locals cxtm
    | None -> vampire_source_context_delta ()
  in
  let delta = vampire_source_context_add_source_map_aliases delta source_map in
  match cxtm with
  | Some cxtm -> vampire_source_context_add_local_type_aliases delta cxtm source_map
  | None -> delta

let vampire_merge_reconstruction_delta proof_delta extra_delta =
  Hashtbl.iter
    (fun h v ->
       if not (Hashtbl.mem proof_delta h) then
         Hashtbl.add proof_delta h v
       else if not (valid_id_p h) then
         Hashtbl.replace proof_delta h v)
    extra_delta

let vampire_parse_thf_type text =
  let len = String.length text in
  let rec skip i =
    if i < len && (text.[i] = ' ' || text.[i] = '\t' || text.[i] = '\n') then
      skip (i + 1)
    else i
  in
  let rec parse_arrow i =
    let left, i = parse_atom i in
    let i = skip i in
    if i < len && text.[i] = '>' then
      let right, j = parse_arrow (skip (i + 1)) in
      (Ar (left, right), j)
    else
      (left, i)
  and parse_atom i =
    let i = skip i in
    if i + 1 < len && text.[i] = '$' && text.[i + 1] = 'i' then
      (Set, i + 2)
    else if i + 1 < len && text.[i] = '$' && text.[i + 1] = 'o' then
      (Prop, i + 2)
    else if i < len && text.[i] = '(' then
      let tp, j = parse_arrow (i + 1) in
      let j = skip j in
      if j < len && text.[j] = ')' then (tp, j + 1)
      else raise Not_found
    else
      raise Not_found
  in
  try
    let tp, i = parse_arrow 0 in
    if skip i = len then Some tp else None
  with Not_found -> None

let vampire_source_map_type_decl entry =
  match entry.Vampire_cert_v1.source_map_kind,
        entry.Vampire_cert_v1.source_map_decl_formula
  with
  | ("type" | "local_type"), Some formula ->
      begin
        try
          let colon = String.index formula ':' in
          let close =
            try String.rindex formula ')'
            with Not_found -> String.length formula
          in
          let start = colon + 1 in
          let len = max 0 (close - start) in
          let type_text = String.sub formula start len in
          vampire_parse_thf_type type_text
        with Not_found | Invalid_argument _ -> None
      end
  | _ -> None

let vampire_source_context_symbol_table_with_source_map source_map =
  let symbols = Hashtbl.copy sigtmof in
  List.iter
    (fun entry ->
       begin match vampire_source_map_type_decl entry with
       | Some tp ->
           List.iter
             (fun alias -> Hashtbl.replace symbols alias (0, tp))
             (vampire_source_map_entry_aliases entry)
       | None -> ()
       end;
       let add_symbol_alias alias source_name =
         if alias <> "" && source_name <> "" then
           match Hashtbl.find_opt sigtmh source_name with
           | Some hash ->
               begin match Hashtbl.find_opt sigtmof hash with
               | Some tp -> Hashtbl.replace symbols alias tp
               | None -> ()
               end
           | None -> ()
       in
       List.iter
         (fun alias ->
            add_symbol_alias
              alias
              entry.Vampire_cert_v1.source_map_source_name)
         (vampire_source_map_entry_aliases entry))
    source_map;
  symbols

let vampire_local_definition_expander cxtm =
  let rec local_terms proof_index = function
    | [] -> []
    | (_, (_, Some _)) :: rest -> local_terms proof_index rest
    | (name, (tp, None)) :: rest ->
        (name, proof_index, tp) :: local_terms (proof_index + 1) rest
  in
  let local_terms = local_terms 0 cxtm in
  let local_definition_bodies =
    List.filter_map
      (fun (name, (_, definition)) ->
         match definition with
         | Some tm -> Some (name, tm)
         | None -> None)
      cxtm
  in
  let rec expand_tm depth = function
    | TmH name ->
        begin match List.assoc_opt name local_definition_bodies with
        | Some tm -> localize_definition depth tm
        | None -> TmH name
        end
    | TpAp (body, tp) -> TpAp (expand_tm depth body, tp)
    | Ap (left, right) -> Ap (expand_tm depth left, expand_tm depth right)
    | Lam (tp, body) -> Lam (tp, expand_tm (depth + 1) body)
    | Imp (left, right) -> Imp (expand_tm depth left, expand_tm depth right)
    | All (tp, body) -> All (tp, expand_tm (depth + 1) body)
    | DB _ | Prim _ as tm -> tm
  and localize_definition depth tm =
    let rec localize local_depth = function
      | TmH name ->
          begin match
            List.find_opt
              (fun (local_name, _, _) -> local_name = name)
              local_terms
          with
          | Some (_, index, _) -> DB (index + depth + local_depth)
          | None -> TmH name
          end
      | TpAp (body, tp) -> TpAp (localize local_depth body, tp)
      | Ap (left, right) ->
          Ap (localize local_depth left, localize local_depth right)
      | Lam (tp, body) -> Lam (tp, localize (local_depth + 1) body)
      | Imp (left, right) ->
          Imp (localize local_depth left, localize local_depth right)
      | All (tp, body) -> All (tp, localize (local_depth + 1) body)
      | DB index when index >= local_depth -> DB (index + depth)
      | DB _ | Prim _ as tm -> tm
    in
    localize 0 tm
  in
  let rec expand_pf depth = function
    | PTpAp (proof, tp) -> PTpAp (expand_pf depth proof, tp)
    | PTmAp (proof, tm) -> PTmAp (expand_pf depth proof, expand_tm depth tm)
    | PPfAp (left, right) -> PPfAp (expand_pf depth left, expand_pf depth right)
    | PLam (prop, proof) -> PLam (expand_tm depth prop, expand_pf depth proof)
    | TLam (tp, proof) -> TLam (tp, expand_pf (depth + 1) proof)
    | Hyp _ | Known _ as proof -> proof
  in
  expand_pf 0

let vampire_source_map_expander cxtm source_map =
  let aliases = Hashtbl.create 101 in
  let rec local_terms proof_index = function
    | [] -> []
    | (_, (_, Some _)) :: rest -> local_terms proof_index rest
    | (name, (tp, None)) :: rest ->
        (name, proof_index, tp) :: local_terms (proof_index + 1) rest
  in
  let local_terms = local_terms 0 cxtm in
  let local_definition_names =
    List.filter_map
      (fun (name, (_, definition)) ->
         match definition with
         | Some _ -> Some name
         | None -> None)
      cxtm
  in
  let local_term_index source_name =
    match
      List.find_opt
        (fun (local_name, _, _) -> local_name = source_name)
        local_terms
    with
    | Some (_, index, _) -> Some index
    | None -> None
  in
  let add_alias alias source_name =
    if alias <> "" && source_name <> "" then
      match Hashtbl.find_opt sigtmh source_name with
      | Some hash -> Hashtbl.replace aliases alias (`Global hash)
      | None ->
          begin match local_term_index source_name with
          | Some index -> Hashtbl.replace aliases alias (`Local index)
          | None ->
              if List.mem source_name local_definition_names then
                Hashtbl.replace aliases alias (`LocalDefinition source_name)
          end
  in
  List.iter
    (fun entry ->
       List.iter
         (fun alias ->
            add_alias alias entry.Vampire_cert_v1.source_map_source_name)
         (vampire_source_map_entry_aliases entry))
    source_map;
  let rec expand_tm depth = function
    | TmH ("vampire_false" | "f__false") -> TmH (!fal)
    | TmH name ->
        begin match Hashtbl.find_opt aliases name with
        | Some (`Global hash) -> TmH hash
        | Some (`Local index) -> DB (index + depth)
        | Some (`LocalDefinition source_name) -> TmH source_name
        | None -> TmH name
        end
    | TpAp (body, tp) -> TpAp (expand_tm depth body, tp)
    | Ap (left, right) -> Ap (expand_tm depth left, expand_tm depth right)
    | Lam (tp, body) -> Lam (tp, expand_tm (depth + 1) body)
    | Imp (left, right) -> Imp (expand_tm depth left, expand_tm depth right)
    | All (tp, body) -> All (tp, expand_tm (depth + 1) body)
    | DB _ | Prim _ as tm -> tm
  in
  let rec expand_pf depth = function
    | PTpAp (proof, tp) -> PTpAp (expand_pf depth proof, tp)
    | PTmAp (proof, tm) -> PTmAp (expand_pf depth proof, expand_tm depth tm)
    | PPfAp (left, right) -> PPfAp (expand_pf depth left, expand_pf depth right)
    | PLam (prop, proof) -> PLam (expand_tm depth prop, expand_pf depth proof)
    | TLam (tp, proof) -> TLam (tp, expand_pf (depth + 1) proof)
    | Hyp _ | Known _ as proof -> proof
  in
  fun proof -> (vampire_local_definition_expander cxtm) (expand_pf 0 proof)

let vampire_extra_delta_expander extra_delta proof =
  let rec expand_tm_raw depth = function
    | TmH name ->
        begin match Hashtbl.find_opt extra_delta name with
        | Some (_, body) -> tmshift 0 depth body
        | None -> TmH name
        end
    | TpAp (body, tp) -> TpAp (expand_tm_raw depth body, tp)
    | Ap (left, right) ->
        Ap (expand_tm_raw depth left, expand_tm_raw depth right)
    | Lam (tp, body) -> Lam (tp, expand_tm_raw (depth + 1) body)
    | Imp (left, right) ->
        Imp (expand_tm_raw depth left, expand_tm_raw depth right)
    | All (tp, body) -> All (tp, expand_tm_raw (depth + 1) body)
    | DB _ | Prim _ as tm -> tm
  in
  let expand_tm depth tm =
    tm_beta_eta_norm (expand_tm_raw depth tm)
  in
  let rec expand_pf depth = function
    | PTpAp (proof, tp) -> PTpAp (expand_pf depth proof, tp)
    | PTmAp (proof, tm) -> PTmAp (expand_pf depth proof, expand_tm depth tm)
    | PPfAp (left, right) -> PPfAp (expand_pf depth left, expand_pf depth right)
    | PLam (prop, proof) -> PLam (expand_tm depth prop, expand_pf depth proof)
    | TLam (tp, proof) -> TLam (tp, expand_pf (depth + 1) proof)
    | Hyp _ | Known _ as proof -> proof
  in
  expand_pf 0 proof

let vampire_expand_returned_proof ?extra_delta cxtm source_map proof =
  let timing_start = Unix.gettimeofday () in
  let timing_last = ref timing_start in
  let timing stage =
    if Sys.getenv_opt "MEGALODON_CERT_DEBUG_TIMING" = Some "1" then
      begin
        let now = Unix.gettimeofday () in
        Printf.printf
          "Vampire returned-proof expansion timing %s: +%.3fs total %.3fs.\n"
          stage
          (now -. !timing_last)
          (now -. timing_start);
        timing_last := now;
        flush stdout
      end
  in
  let base_expander =
    match source_map with
    | None -> vampire_local_definition_expander cxtm
    | Some source_map -> vampire_source_map_expander cxtm source_map
  in
  match extra_delta with
  | None ->
      timing "base:start";
      let result = base_expander proof in
      timing "base:done";
      result
  | Some extra_delta ->
      timing "merge:start";
      let merged_delta = Hashtbl.create 17 in
      Hashtbl.iter
        (fun h v ->
           if not (Hashtbl.mem sigdelta h) then Hashtbl.replace merged_delta h v)
        (Vampire_cert_v1.approved_native_sgdelta ());
      vampire_merge_reconstruction_delta merged_delta extra_delta;
      timing "merge:done";
      timing "extra_delta:start";
      let expanded = vampire_extra_delta_expander merged_delta proof in
      timing "extra_delta:done";
      timing "base:start";
      let result = base_expander expanded in
      timing "base:done";
      result

let vampire_expand_returned_tm ?extra_delta cxtm source_map tm =
  match vampire_expand_returned_proof ?extra_delta cxtm source_map (PLam (tm, Hyp 0)) with
  | PLam (expanded, _) -> expanded
  | _ -> tm

let vampire_certificate_only_symbol_in_tm live_symbols extra_symbols tm =
  let rec tm_symbol = function
    | TmH name when Hashtbl.mem extra_symbols name && not (Hashtbl.mem live_symbols name) ->
        Some name
    | TmH _ | DB _ | Prim _ -> None
    | TpAp (body, _) -> tm_symbol body
    | Ap (left, right) ->
        begin match tm_symbol left with
        | Some _ as result -> result
        | None -> tm_symbol right
        end
    | Lam (_, body) | All (_, body) -> tm_symbol body
    | Imp (left, right) ->
        begin match tm_symbol left with
        | Some _ as result -> result
        | None -> tm_symbol right
        end
  in
  tm_symbol tm

let vampire_live_safe_extra_delta ?(body_expander=(fun tm -> tm)) live_symbols extra_symbols extra_delta =
  let filtered = Hashtbl.create (Hashtbl.length extra_delta) in
  let expanded_bodies = Hashtbl.create (Hashtbl.length extra_delta) in
  let debug = Sys.getenv_opt "MEGALODON_CERT_DEBUG_LIVE_SAFE_DELTA" = Some "1" in
  let expanded_body name body =
    match Hashtbl.find_opt expanded_bodies name with
    | Some body -> body
    | None ->
        let body = body_expander body in
        Hashtbl.replace expanded_bodies name body;
        body
  in
  let add_filtered_definition name arity body =
    let add name =
      Hashtbl.replace filtered name (arity, body)
    in
    add name;
    let alias =
      if String.length name > 0 && name.[0] = '#' then
        String.sub name 1 (String.length name - 1)
      else
        "#" ^ name
    in
    if alias <> name
       && not (Hashtbl.mem live_symbols alias) then
      add alias
  in
  let rec unsafe_symbol_in_tm = function
    | TmH name
        when Hashtbl.mem extra_symbols name
             && not (Hashtbl.mem live_symbols name)
             && not (Hashtbl.mem filtered name) ->
        Some name
    | TmH _ | DB _ | Prim _ -> None
    | TpAp (body, _) -> unsafe_symbol_in_tm body
    | Ap (left, right) ->
        begin match unsafe_symbol_in_tm left with
        | Some _ as result -> result
        | None -> unsafe_symbol_in_tm right
        end
    | Lam (_, body) | All (_, body) -> unsafe_symbol_in_tm body
    | Imp (left, right) ->
        begin match unsafe_symbol_in_tm left with
        | Some _ as result -> result
        | None -> unsafe_symbol_in_tm right
        end
  in
  let changed = ref true in
  while !changed do
    changed := false;
    Hashtbl.iter
      (fun name (arity, body) ->
         if not (Hashtbl.mem filtered name) then
           let body = expanded_body name body in
           match unsafe_symbol_in_tm body with
           | Some _ -> ()
           | None ->
               if debug then
                 begin
                   Printf.printf
                     "Vampire native live-safe delta kept %s: %s\n"
                     name
                     (tm_to_str body);
                   flush stdout
                 end;
               add_filtered_definition name arity body;
               changed := true)
      extra_delta
  done;
  if debug then
    begin
      Hashtbl.iter
        (fun name (_, body) ->
           if not (Hashtbl.mem filtered name) then
             let body = expanded_body name body in
             match unsafe_symbol_in_tm body with
             | Some symbol ->
                 Printf.printf
                   "Vampire native live-safe delta skipped %s because body contains certificate-only symbol %s: %s\n"
                   name
                   symbol
                   (tm_to_str body)
             | None -> ())
        extra_delta;
      flush stdout
    end;
  filtered

let vampire_qed_registered_delta : string list ref = ref []
let vampire_qed_registered_symbols : string list ref = ref []

let vampire_register_reconstruction_delta_for_qed extra_symbols extra_delta =
  if !vampireabyqualifying then
    raise
      (Failure
         "Qualifying Vampire reconstruction may not install certificate-local definitions globally");
  Hashtbl.iter
    (fun name (arity, body) ->
       if not (Hashtbl.mem sigdelta name) then
         begin
           Hashtbl.add sigdelta name (arity, body);
           vampire_qed_registered_delta := name :: !vampire_qed_registered_delta
         end)
    extra_delta;
  Hashtbl.iter
    (fun name binding ->
       if not (Hashtbl.mem sigtmof name) then
         begin
           Hashtbl.add sigtmof name binding;
           vampire_qed_registered_symbols := name :: !vampire_qed_registered_symbols
         end)
    extra_symbols

let vampire_clear_reconstruction_delta_for_qed () =
  if !vampireabyqualifying
     || (Sys.getenv_opt "MEGALODON_CERT_KEEP_QED_DELTA" <> Some "1" && not !pfgout) then
    begin
      List.iter (Hashtbl.remove sigdelta) !vampire_qed_registered_delta;
      List.iter (Hashtbl.remove sigtmof) !vampire_qed_registered_symbols;
      vampire_qed_registered_delta := [];
      vampire_qed_registered_symbols := []
    end

let vampire_assert_no_qed_reconstruction_state where =
  if !vampireabyqualifying
     && (!vampire_qed_registered_delta <> [] || !vampire_qed_registered_symbols <> []) then
    raise
      (Failure
         (Printf.sprintf
            "Qualifying Vampire reconstruction leaked certificate-local Qed state after %s"
            where))

let vampire_certificate_only_symbol_in_proof live_symbols extra_delta extra_symbols proof =
  let tm_symbol = vampire_certificate_only_symbol_in_tm live_symbols extra_symbols in
  let rec pf_symbol = function
    | Hyp _ -> None
    | Known name when Hashtbl.mem extra_delta name && not (Hashtbl.mem sigdelta name) ->
        Some name
    | Known _ -> None
    | PTpAp (body, _) -> pf_symbol body
    | PTmAp (body, tm) ->
        begin match pf_symbol body with
        | Some _ as result -> result
        | None -> tm_symbol tm
        end
    | PPfAp (left, right) ->
        begin match pf_symbol left with
        | Some _ as result -> result
        | None -> pf_symbol right
        end
    | PLam (prop, body) ->
        begin match tm_symbol prop with
        | Some _ as result -> result
        | None -> pf_symbol body
        end
    | TLam (_, body) -> pf_symbol body
  in
  pf_symbol proof

let vampire_debug_certificate_only_symbol_in_proof live_symbols extra_delta extra_symbols proof =
  let short_tm tm =
    let text = tm_to_str tm in
    if String.length text <= 500 then text
    else String.sub text 0 500 ^ "..."
  in
  let short_pf pf =
    let text = pf_to_str pf in
    if String.length text <= 500 then text
    else String.sub text 0 500 ^ "..."
  in
  let rec find_tm path enclosing tm =
    match tm with
    | TmH name when Hashtbl.mem extra_symbols name && not (Hashtbl.mem live_symbols name) ->
        Some
          (Printf.sprintf
             "%s: certificate-only term symbol %s in term %s; enclosing term %s"
             path
             name
             (short_tm tm)
             (short_tm enclosing))
    | TmH _ | DB _ | Prim _ -> None
    | TpAp (body, _) -> find_tm (path ^ ".tp") tm body
    | Ap (left, right) ->
        begin match find_tm (path ^ ".left") tm left with
        | Some _ as result -> result
        | None -> find_tm (path ^ ".right") tm right
        end
    | Lam (_, body) -> find_tm (path ^ ".lam") tm body
    | All (_, body) -> find_tm (path ^ ".all") tm body
    | Imp (left, right) ->
        begin match find_tm (path ^ ".antecedent") tm left with
        | Some _ as result -> result
        | None -> find_tm (path ^ ".consequent") tm right
        end
  in
  let rec find_pf path pf =
    match pf with
    | Hyp _ -> None
    | Known name when Hashtbl.mem extra_delta name && not (Hashtbl.mem sigdelta name) ->
        Some
          (Printf.sprintf
             "%s: certificate-only known proof symbol %s in proof %s"
             path
             name
             (short_pf pf))
    | Known _ -> None
    | PTpAp (body, _) -> find_pf (path ^ ".tp") body
    | PTmAp (body, tm) ->
        begin match find_pf (path ^ ".proof") body with
        | Some _ as result -> result
        | None -> find_tm (path ^ ".term") tm tm
        end
    | PPfAp (left, right) ->
        begin match find_pf (path ^ ".left") left with
        | Some _ as result -> result
        | None -> find_pf (path ^ ".right") right
        end
    | PLam (prop, body) ->
        begin match find_tm (path ^ ".prop") prop prop with
        | Some _ as result -> result
        | None -> find_pf (path ^ ".body") body
        end
    | TLam (_, body) -> find_pf (path ^ ".body") body
  in
  find_pf "root" proof

let vampire_certificate_only_unsafe_prop_symbol_in_proof ?extra_delta live_symbols extra_symbols proof =
  let prop_choice_symbol name =
    name = "Eps_prop" || name = "#Eps_prop"
  in
  let prop_typed_certificate_symbol name =
    match Hashtbl.find_opt extra_symbols name with
    | Some (_, Prop) -> true
    | _ -> false
  in
  let unsafe_symbol name =
    Hashtbl.mem extra_symbols name
    && not (Hashtbl.mem live_symbols name)
    && (prop_choice_symbol name || prop_typed_certificate_symbol name)
  in
  let rec find_tm = function
    | TmH name when unsafe_symbol name ->
        Some name
    | TmH _ | DB _ | Prim _ -> None
    | TpAp (body, _) -> find_tm body
    | Ap (left, right) ->
        begin match find_tm left with
        | Some _ as result -> result
        | None -> find_tm right
        end
    | Lam (_, body) | All (_, body) -> find_tm body
    | Imp (left, right) ->
        begin match find_tm left with
        | Some _ as result -> result
        | None -> find_tm right
        end
  in
  let find_known_body name =
    match extra_delta with
    | Some extra_delta ->
        begin match Hashtbl.find_opt extra_delta name with
        | Some (_, body) -> find_tm body
        | None -> None
        end
    | None -> None
  in
  let rec find_pf = function
    | Hyp _ -> None
    | Known name -> find_known_body name
    | PTpAp (body, _) -> find_pf body
    | PTmAp (body, tm) ->
        begin match find_pf body with
        | Some _ as result -> result
        | None -> find_tm tm
        end
    | PPfAp (left, right) ->
        begin match find_pf left with
        | Some _ as result -> result
        | None -> find_pf right
        end
    | PLam (prop, body) ->
        begin match find_tm prop with
        | Some _ as result -> result
        | None -> find_pf body
        end
    | TLam (_, body) -> find_pf body
  in
  find_pf proof

let vampire_source_context_local_definition_names cxtm =
  List.filter_map
    (fun (name, (_, definition)) ->
       match definition with
       | Some _ -> Some name
       | None -> None)
    cxtm

let vampire_pure_prop_schema_context cxtm cxpf =
  List.for_all
    (fun (_, (tp, definition)) ->
       tp = Prop && definition = None)
    cxtm
  && cxpf = []

let vampire_source_map_definition_kind kind =
  kind = "def" || kind = "definition" || kind = "local_definition"

let vampire_source_map_definition_names source_map =
  let add_nonempty name names =
    if name = "" then names else name :: names
  in
  source_map
  |> List.fold_left
       (fun names entry ->
          if vampire_source_map_definition_kind
               entry.Vampire_cert_v1.source_map_kind
          then
            names
            |> add_nonempty entry.Vampire_cert_v1.source_map_tptp_name
            |> add_nonempty entry.Vampire_cert_v1.source_map_source_name
          else names)
       []
  |> List.sort_uniq compare

let vampire_source_map_external_symbol_names source_map =
  let add_nonempty name names =
    if name = "" then names else name :: names
  in
  source_map
  |> List.fold_left
       (fun names entry ->
          match entry.Vampire_cert_v1.source_map_kind with
          | "type" | "def" | "definition" | "local_definition" ->
              names
              |> add_nonempty entry.Vampire_cert_v1.source_map_tptp_name
              |> add_nonempty entry.Vampire_cert_v1.source_map_source_name
          | _ -> names)
       []
  |> List.sort_uniq compare

let vampire_source_context_external_definition_names cxtm source_map =
  List.sort_uniq compare
    (vampire_source_context_local_definition_names cxtm
     @ vampire_source_map_external_symbol_names source_map)

let vampire_aby_source_context cxtm cxpf =
  let rec local_term_projection proof_index = function
    | [] -> []
    | (_, (_, Some _)) :: rest ->
        None :: local_term_projection proof_index rest
    | (_, (_, None)) :: rest ->
        Some proof_index :: local_term_projection (proof_index + 1) rest
  in
  let rec local_terms proof_index = function
    | [] -> []
    | (_, (_, Some _)) :: rest -> local_terms proof_index rest
    | (name, (tp, None)) :: rest ->
        (name, proof_index, tp) :: local_terms (proof_index + 1) rest
  in
  {
    Vampire_source_context.proof_delta = vampire_source_context_delta ();
    known_table = sigknh;
    symbol_table = sigtmof;
    term_context =
      List.filter_map
        (fun (_, (tp, definition)) ->
           match definition with
           | None -> Some tp
           | Some _ -> None)
        cxtm;
    local_term_projection = local_term_projection 0 cxtm;
    local_terms = local_terms 0 cxtm;
    local_hypotheses = cxpf;
    local_definitions =
      List.filter_map
        (fun (name, (tp, definition)) ->
           match definition with
           | Some tm -> Some (name, tp, tm)
           | None -> None)
        cxtm;
  }

let vampire_native_core_false_tm = All(Prop,DB(0))

let vampire_native_core_exists tp body =
  All
    (Prop,
     Imp
       (All (tp, Imp (tmshift 1 1 body, DB 1)),
        DB 0))

let vampire_native_core_not_forall_exists_hash_tp = function
  | "vampire_not_forall_exists_set" -> Some Set
  | "vampire_not_forall_exists_prop" -> Some Prop
  | "vampire_not_forall_exists_set_prop" -> Some (Ar (Set, Prop))
  | "vampire_not_forall_exists_set_set" -> Some (Ar (Set, Set))
  | "vampire_not_forall_exists_set_set_prop" -> Some (Ar (Set, Ar (Set, Prop)))
  | _ -> None

let vampire_source_step_has_proof source_audit step =
  List.exists
    (fun (source_step, _) -> source_step = step)
    source_audit.Vampire_source_context.source_proofs

let vampire_source_proof_list_has_step source_proofs step =
  List.exists (fun (source_step, _) -> source_step = step) source_proofs

let vampire_generated_source_kind kind =
  kind = "set_reflexivity" || kind = "local_set_reflexivity"

let vampire_remaining_source_bindings_for_proofs source_proofs source_bindings =
  List.filter
    (fun binding ->
       (not
          (vampire_source_proof_list_has_step
             source_proofs
             binding.Vampire_cert_v1.core_native_source_step))
       && not
            (vampire_generated_source_kind
               binding.Vampire_cert_v1.core_native_source_map_kind))
    source_bindings

let vampire_debug_source_binding prefix binding =
  if Sys.getenv_opt "MEGALODON_CERT_DEBUG" = Some "1" then
    begin
      Printf.printf
        "%s step=%s cert_kind=%s map_kind=%s source=%s proposition=%s\n"
        prefix
        binding.Vampire_cert_v1.core_native_source_step
        binding.Vampire_cert_v1.core_native_certificate_source_kind
        binding.Vampire_cert_v1.core_native_source_map_kind
        binding.Vampire_cert_v1.core_native_source_name
        (tm_to_str binding.Vampire_cert_v1.core_native_source_proposition);
      flush stdout
    end

let vampire_source_binding_report_kind binding =
  let map_kind = binding.Vampire_cert_v1.core_native_source_map_kind in
  let cert_kind = binding.Vampire_cert_v1.core_native_certificate_source_kind in
  if map_kind = "known" || map_kind = "axiom" then "known"
  else if map_kind = "local_fact" then "local"
  else if map_kind = "def"
          || map_kind = "definition"
          || map_kind = "local_definition" then "definition"
  else if vampire_generated_source_kind map_kind then "generated"
  else if cert_kind = "negated_conjecture"
          || map_kind = "conjecture"
          || map_kind = "negated_conjecture" then "conjecture"
  else "unresolved"

let vampire_source_binding_report_counts bindings =
  List.fold_left
    (fun (known, local, definition, generated, conjecture, unresolved) binding ->
       match vampire_source_binding_report_kind binding with
       | "known" -> (known + 1, local, definition, generated, conjecture, unresolved)
       | "local" -> (known, local + 1, definition, generated, conjecture, unresolved)
       | "definition" -> (known, local, definition + 1, generated, conjecture, unresolved)
       | "generated" -> (known, local, definition, generated + 1, conjecture, unresolved)
       | "conjecture" -> (known, local, definition, generated, conjecture + 1, unresolved)
       | _ -> (known, local, definition, generated, conjecture, unresolved + 1))
    (0, 0, 0, 0, 0, 0)
    bindings

let vampire_print_remaining_source_summary prefix source_proofs source_bindings =
  let remaining =
    vampire_remaining_source_bindings_for_proofs source_proofs source_bindings
  in
  let known, local, definition, generated, conjecture, unresolved =
    vampire_source_binding_report_counts remaining
  in
  Printf.printf
    "%s source assumptions remaining by kind known=%d local=%d definition=%d generated=%d conjecture=%d unresolved=%d.\n"
    prefix
    known
    local
    definition
    generated
    conjecture
    unresolved

let vampire_core_source_proofs source_audit =
  List.filter
    (fun (step, _) ->
       match List.assoc_opt step source_audit.Vampire_source_context.resolved with
       | Some (Vampire_source_context.LocalHyp _) -> false
       | Some (Vampire_source_context.Definitional _) -> false
       | _ -> true)
    source_audit.Vampire_source_context.source_proofs

let vampire_source_context_variable_names cxtm =
  let rec collect index = function
    | [] -> []
    | (_, (_, Some _)) :: rest -> collect index rest
    | (name, (_, None)) :: rest ->
        (index, name) :: collect (index + 1) rest
  in
  collect 0 cxtm

let vampire_reify_source_context_variables cxtm tm =
  let source_variables = vampire_source_context_variable_names cxtm in
  let rec lookup index = function
    | [] -> None
    | (source_index, name) :: rest ->
        if source_index = index then Some name else lookup index rest
  in
  let rec reify depth = function
    | DB index when index >= depth ->
        begin match lookup (index - depth) source_variables with
        | Some name -> TmH name
        | None -> DB index
        end
    | DB _ as tm -> tm
    | TmH _ | Prim _ as tm -> tm
    | TpAp (body, tp) -> TpAp (reify depth body, tp)
    | Ap (left, right) -> Ap (reify depth left, reify depth right)
    | Lam (tp, body) -> Lam (tp, reify (depth + 1) body)
    | Imp (left, right) -> Imp (reify depth left, reify depth right)
    | All (tp, body) -> All (tp, reify (depth + 1) body)
  in
  reify 0 tm

let vampire_core_external_hypotheses cert cxtm source_map source_audit cxpf =
  let native_source_bindings =
    Vampire_cert_v1.native_certificate_source_bindings_native_context
      ~source_map
      ~external_definition_names:
        (vampire_source_context_external_definition_names cxtm source_map)
      cert
  in
  let native_source_proposition step fallback =
    match
      List.find_opt
        (fun binding -> binding.Vampire_cert_v1.core_native_source_step = step)
        native_source_bindings
    with
    | Some binding -> binding.Vampire_cert_v1.core_native_source_proposition
    | None -> fallback
  in
  let source_context_proposition proposition =
    vampire_reify_source_context_variables cxtm proposition
  in
  let external_hypotheses =
    Array.of_list (List.map (fun (_, proposition) -> source_context_proposition proposition) cxpf)
  in
  List.iter
    (fun (step, source_proof) ->
       match source_proof with
       | Vampire_source_context.LocalHyp (index, proposition)
           when index >= 0 && index < Array.length external_hypotheses ->
          let proposition =
            native_source_proposition step proposition
            |> source_context_proposition
          in
          if Sys.getenv_opt "MEGALODON_CERT_DEBUG" = Some "1" then
            prerr_endline
              ("Vampire native source external local hypothesis "
               ^ step
                ^ " -> __"
                ^ string_of_int index
                ^ " : "
                ^ tm_to_str proposition);
           external_hypotheses.(index) <- proposition
       | _ -> ())
    source_audit.Vampire_source_context.resolved;
  if Sys.getenv_opt "MEGALODON_CERT_DEBUG" = Some "1" then
    Array.iteri
      (fun index proposition ->
         prerr_endline
           ("Vampire native source external hypothesis __"
            ^ string_of_int index
            ^ " final : "
            ^ tm_to_str proposition))
      external_hypotheses;
  Array.to_list external_hypotheses

let vampire_source_proof source_audit step =
  List.assoc_opt step source_audit.Vampire_source_context.source_proofs

let vampire_iff_intro_proof left right left_to_right right_to_left =
  match Hashtbl.find_opt sigknh "iffI" with
  | Some iffI_hash ->
      PPfAp
        (PPfAp
           (PTmAp (PTmAp (Known iffI_hash, left), right),
            left_to_right),
         right_to_left)
  | None ->
      let and_intro_id =
        "7f6246d08629eeb16eab93529ffe4f929f43344833ab88c7786393693520e82b"
      in
      let forward = Imp (left, right) in
      let backward = Imp (right, left) in
      if Hashtbl.mem sigdelta and_intro_id then
        PPfAp
          (PPfAp
             (PTmAp (PTmAp (Known and_intro_id, forward), backward),
              left_to_right),
           right_to_left)
      else
        let shifted_forward_proof =
          pfshift 0 1 (pftmshift 0 1 left_to_right)
        in
        let shifted_backward_proof =
          pfshift 0 1 (pftmshift 0 1 right_to_left)
        in
        TLam
          (Prop,
           PLam
             (Imp
                (tmshift 0 1 forward,
                 Imp (tmshift 0 1 backward, DB 0)),
              PPfAp
                (PPfAp (Hyp 0, shifted_forward_proof),
                 shifted_backward_proof)))

let vampire_expanded_equality_proof tp left right eq_proof =
  let predicate_sort = Ar (tp, Ar (tp, Prop)) in
  let premise =
    Ap (Ap (DB 0, tmshift 0 1 left), tmshift 0 1 right)
  in
  TLam
    (predicate_sort,
     PLam
       (premise,
        PPfAp
          (PTmAp (pfshift 0 1 (pftmshift 0 1 eq_proof), DB 0),
           Hyp 0)))

let vampire_loaded_prop_ext_expander ?delta:_ proof =
  match Hashtbl.find_opt sigknh "prop_ext" with
  | None -> proof
  | Some prop_ext_hash ->
      let rec expand = function
        | PPfAp
            (PPfAp
               (PTmAp (PTmAp (Known h, left), right), left_to_right),
             right_to_left)
            when h = prop_ext_hash || h = Vampire_cert_v1.native_core_prop_ext_hash ->
            let left_to_right = expand left_to_right in
            let right_to_left = expand right_to_left in
            let iff_proof =
              vampire_iff_intro_proof
                left
                right
                left_to_right
                right_to_left
            in
            let eq_proof =
              PPfAp
                (PTmAp (PTmAp (Known prop_ext_hash, left), right),
                 iff_proof)
            in
            if h = Vampire_cert_v1.native_core_prop_ext_hash then
              vampire_expanded_equality_proof Prop left right eq_proof
            else
              eq_proof
        | PTpAp (body, tp) -> PTpAp (expand body, tp)
        | PTmAp (body, tm) -> PTmAp (expand body, tm)
        | PPfAp (left, right) -> PPfAp (expand left, expand right)
        | PLam (prop, body) -> PLam (prop, expand body)
        | TLam (tp, body) -> TLam (tp, expand body)
        | Hyp _ | Known _ as proof -> proof
      in
      expand proof

let vampire_directional_prop_ext_expander proof =
  match Hashtbl.find_opt sigknh "prop_ext", Hashtbl.find_opt sigknh "iffI" with
  | Some prop_ext_hash, Some iffI_hash ->
      let prop_ext_like h =
        h = prop_ext_hash || h = Vampire_cert_v1.native_core_prop_ext_hash
      in
      let rec expand = function
        | PPfAp
            (PTmAp (PTmAp (Known h, left), right),
             PPfAp
               (PPfAp
                  (PTmAp (PTmAp (Known iff_h, _), _),
                   left_to_right),
                right_to_left))
            when prop_ext_like h
                 && iff_h = iffI_hash ->
            PPfAp
              (PPfAp
                 (PTmAp (PTmAp (Known h, left), right),
                  expand left_to_right),
               expand right_to_left)
        | PTpAp (body, tp) -> PTpAp (expand body, tp)
        | PTmAp (body, tm) -> PTmAp (expand body, tm)
        | PPfAp (left, right) -> PPfAp (expand left, expand right)
        | PLam (prop, body) -> PLam (prop, expand body)
        | TLam (tp, body) -> TLam (tp, expand body)
        | Hyp _ | Known _ as proof -> proof
      in
      expand proof
  | _ -> proof

let vampire_live_not_tm target =
  match Hashtbl.find_opt sigtmh "not" with
  | Some not_hash -> Ap (TmH not_hash, target)
  | None -> Imp (target, TmH (!fal))

let vampire_live_case_not_tm target =
  match Hashtbl.find_opt sigknh "notE" with
  | Some _ -> vampire_live_not_tm target
  | None -> Imp (target, TmH (!fal))

let vampire_currently_proving name =
  match !proving with
  | Some (current_name, _, _, _, _) -> current_name = name
  | None -> false

let vampire_available_known name =
  if vampire_currently_proving name then None
  else Hashtbl.find_opt sigknh name

let vampire_live_false_elim proof target =
  match vampire_available_known "FalseE" with
  | Some false_elim_hash -> PTmAp (PPfAp (Known false_elim_hash, proof), target)
  | None -> PTmAp (proof, target)

let vampire_live_not_elim target not_proof target_proof =
  match Hashtbl.find_opt sigknh "notE" with
  | Some not_elim_hash ->
      PPfAp
        (PPfAp (PTmAp (Known not_elim_hash, target), not_proof),
         target_proof)
  | None -> PPfAp (not_proof, target_proof)

let vampire_live_prop_choice_witness predicate =
  vampire_live_case_not_tm (Ap (predicate, TmH (!fal)))

let vampire_native_exists_intro tp predicate witness witness_proof =
  TLam
    (Prop,
     PLam
       (All (tp, Imp (Ap (tmshift 0 2 predicate, DB 0), DB 1)),
        PPfAp
          (PTmAp (Hyp 0, tmshift 0 1 witness),
           pfshift 0 1 (pftmshift 0 1 witness_proof))))

let vampire_live_not_forall_exists_proof tp =
  let p_x = Ap (DB 2, DB 0) in
  let exists_q = vampire_native_core_exists tp (Ap (DB 1, DB 0)) in
  let not_exists_q = vampire_live_case_not_tm exists_q in
  let not_p_x = vampire_live_case_not_tm p_x in
  match Hashtbl.find_opt sigknh "xm" with
  | None -> None
  | Some xm_hash ->
      let rec proof () =
        TLam
          (Ar (tp, Prop),
           TLam
             (Ar (tp, Prop),
              PLam
                (All (tp, Imp (Imp (Ap (DB 2, DB 0), vampire_native_core_false_tm),
                               Ap (DB 1, DB 0))),
                 PLam
                   (Imp (All (tp, Ap (DB 2, DB 0)), vampire_native_core_false_tm),
                    PPfAp
                      (PPfAp
                         (PTmAp (PTmAp (Known xm_hash, exists_q), exists_q),
                          PLam (exists_q, Hyp 0)),
                       PLam
                         (not_exists_q,
                          let all_p =
                            TLam
                              (tp,
                               PPfAp
                                 (PPfAp
                                    (PTmAp (PTmAp (Known xm_hash, p_x), p_x),
                                     PLam (p_x, Hyp 0)),
                                  PLam
                                    (not_p_x,
                                     let native_not_p_x =
                                       PLam
                                         (p_x,
                                          vampire_live_false_elim
                                            (vampire_live_not_elim p_x (Hyp 1) (Hyp 0))
                                            vampire_native_core_false_tm)
                                     in
                                     let q_proof =
                                       PPfAp (PTmAp (Hyp 3, DB 0), native_not_p_x)
                                     in
                                     let exists_q_proof =
                                       vampire_native_exists_intro tp (DB 1) (DB 0) q_proof
                                     in
                                     let contradiction =
                                       PPfAp (Hyp 1, exists_q_proof)
                                     in
                                     vampire_live_false_elim contradiction p_x)))
                          in
                          let contradiction =
                            PPfAp (Hyp 1, all_p)
                          in
                          PTmAp (contradiction, exists_q)))))))
      in
      Some (proof ())

let vampire_live_exists_set_choice_proof () =
  match Hashtbl.find_opt sigtmh "Eps_i", Hashtbl.find_opt sigknh "Eps_i_ax" with
  | Some eps_hash, Some eps_ax_hash ->
      let predicate_tp = Ar (Set, Prop) in
      let predicate = DB 0 in
      let witness = Ap (TmH eps_hash, predicate) in
      let target = Ap (predicate, witness) in
      let exists_predicate =
        vampire_native_core_exists Set (Ap (DB 1, DB 0))
      in
      Some
        (TLam
           (predicate_tp,
            PLam
              (exists_predicate,
               PPfAp
                 (PTmAp (Hyp 0, target),
                  TLam
                    (Set,
                     PLam
                       (Ap (DB 1, DB 0),
                        PPfAp
                          (PTmAp
                             (PTmAp (Known eps_ax_hash, DB 1),
                              DB 0),
                           Hyp 0)))))))
  | _ -> None

let vampire_live_prop_ext_eq_proof left right left_to_right right_to_left =
  match Hashtbl.find_opt sigknh "prop_ext_2" with
  | Some prop_ext_2_hash ->
      Some
        (PPfAp
           (PPfAp
              (PTmAp (PTmAp (Known prop_ext_2_hash, left), right),
               left_to_right),
            right_to_left))
  | None ->
      begin match Hashtbl.find_opt sigknh "prop_ext" with
      | Some prop_ext_hash ->
          Some
            (PPfAp
               (PTmAp (PTmAp (Known prop_ext_hash, left), right),
                vampire_iff_intro_proof
                  left
                  right
                  left_to_right
                  right_to_left))
      | None -> None
      end

let vampire_prop_pred_transport pred source target eq_target_source source_proof =
  let motive =
    Lam
      (Prop,
       Lam (Prop, Ap (tmshift 0 2 pred, DB 0)))
  in
  PPfAp (PTmAp (eq_target_source, motive), source_proof)

let vampire_live_exists_prop_choice_proof () =
  match Hashtbl.find_opt sigknh "xm" with
  | None -> None
  | Some xm_hash ->
      let false_tm = TmH (!fal) in
      let predicate = DB 0 in
      let p_false = Ap (predicate, false_tm) in
      let not_p_false = vampire_live_prop_choice_witness predicate in
      let target = Ap (predicate, not_p_false) in
      let exists_predicate =
        vampire_native_core_exists Prop (Ap (DB 1, DB 0))
      in
      let left_branch () =
        let not_to_false =
          PLam
            (not_p_false,
             vampire_live_not_elim p_false (Hyp 0) (Hyp 1))
        in
        let false_to_not =
          PLam
            (false_tm,
             vampire_live_false_elim (Hyp 0) not_p_false)
        in
        match
          vampire_live_prop_ext_eq_proof
            not_p_false
            false_tm
            not_to_false
            false_to_not
        with
        | None -> None
        | Some eq_not_false ->
            Some
              (vampire_prop_pred_transport
                 predicate
                 false_tm
                 not_p_false
                 eq_not_false
                 (Hyp 0))
      in
      let true_witness_branch () =
        let x = DB 0 in
        let predicate = DB 1 in
        let not_p_false = vampire_live_prop_choice_witness predicate in
        let not_to_x = PLam (not_p_false, Hyp 1) in
        let x_to_not = PLam (x, Hyp 3) in
        match
          vampire_live_prop_ext_eq_proof
            not_p_false
            x
            not_to_x
            x_to_not
        with
        | None -> None
        | Some eq_not_x ->
            Some
              (vampire_prop_pred_transport
                 predicate
                 x
                 not_p_false
                 eq_not_x
                 (Hyp 1))
      in
      let false_witness_branch () =
        let x = DB 0 in
        let predicate = DB 1 in
        let not_p_false = vampire_live_prop_choice_witness predicate in
        let target = Ap (predicate, not_p_false) in
        let false_to_x =
          PLam
            (false_tm,
             vampire_live_false_elim (Hyp 0) x)
        in
        let x_to_false =
          PLam
            (x,
             vampire_live_not_elim x (Hyp 1) (Hyp 0))
        in
        match
          vampire_live_prop_ext_eq_proof
            false_tm
            x
            false_to_x
            x_to_false
        with
        | None -> None
        | Some eq_false_x ->
            let p_false_proof =
              vampire_prop_pred_transport
                predicate
                x
                false_tm
                eq_false_x
                (Hyp 1)
            in
            let contradiction = PPfAp (Hyp 2, p_false_proof) in
            Some (vampire_live_false_elim contradiction target)
      in
      begin match left_branch (), true_witness_branch (), false_witness_branch () with
      | Some left_case, Some true_case, Some false_case ->
          let witness_case_target =
            Ap (DB 1, vampire_live_prop_choice_witness (DB 1))
          in
          let witness_case =
            PPfAp
              (PPfAp
                 (PTmAp (PTmAp (Known xm_hash, DB 0), witness_case_target),
                  PLam (DB 0, true_case)),
               PLam (vampire_live_case_not_tm (DB 0), false_case))
          in
          let right_case =
            PPfAp
              (PTmAp (Hyp 1, target),
               TLam
                 (Prop,
                  PLam
                    (Ap (DB 1, DB 0),
                     witness_case)))
          in
          Some
            (TLam
               (Ar (Prop, Prop),
                PLam
                  (exists_predicate,
                   PPfAp
                     (PPfAp
                        (PTmAp (PTmAp (Known xm_hash, p_false), target),
                         PLam (p_false, left_case)),
                      PLam (vampire_live_case_not_tm p_false, right_case)))))
      | _ -> None
      end

let vampire_live_exists_prop_choice_checked_cache : pf option option ref = ref None

let vampire_live_exists_prop_choice_prop () =
  let predicate = DB 0 in
  let target =
    Ap (predicate, vampire_live_prop_choice_witness predicate)
  in
  All
    (Ar (Prop, Prop),
     Imp
       (vampire_native_core_exists Prop (Ap (DB 1, DB 0)),
        target))

let vampire_live_exists_prop_choice_checked_proof () =
  match !vampire_live_exists_prop_choice_checked_cache with
  | Some result -> result
  | None ->
      let result =
        match vampire_live_exists_prop_choice_proof () with
        | None -> None
        | Some proof ->
            let proposition = vampire_live_exists_prop_choice_prop () in
            begin match check_propofpf sigdelta sigtmof [] [] proof proposition [] with
            | Some _ -> Some proof
            | None ->
                if Sys.getenv_opt "MEGALODON_CERT_DEBUG" = Some "1"
                   || Sys.getenv_opt "MEGALODON_CERT_DEBUG_PROP_CHOICE" = Some "1" then
                  begin
                    Printf.printf
                      "Vampire native live prop-choice proof did not check for proposition: %s\n"
                      (tm_to_str proposition);
                    flush stdout
                  end;
                None
            end
      in
      vampire_live_exists_prop_choice_checked_cache := Some result;
      result

let vampire_live_has_checked_prop_choice () =
  match vampire_live_exists_prop_choice_checked_proof () with
  | Some _ -> true
  | None -> false

let check_vampire_live_prop_choice_if_requested () =
  if !vampirechecklivepropchoice then
    begin
      vampire_live_exists_prop_choice_checked_cache := None;
      let proposition = vampire_live_exists_prop_choice_prop () in
      match vampire_live_exists_prop_choice_checked_proof () with
      | Some _ ->
          Printf.printf
            "Vampire native live prop-choice proof checked for proposition: %s\n"
            (tm_to_str proposition);
          flush stdout
      | None ->
          let required_knowns =
            ["xm"; "FalseE"; "prop_ext_2"; "prop_ext"; "iffI"]
          in
          List.iter
            (fun name ->
               Printf.printf
                 "Vampire native live prop-choice dependency %s: %s\n"
                 name
                 (if Hashtbl.mem sigknh name then "present" else "missing"))
            required_knowns;
          Printf.printf
            "Vampire native live prop-choice proof failed for proposition: %s\n"
            (tm_to_str proposition);
          flush stdout;
          raise (Failure "Vampire native live prop-choice proof did not check")
    end

let rec vampire_live_basis_tm_expander = function
  | Ap (TmH "Eps_prop", predicate)
      when vampire_live_has_checked_prop_choice () ->
      vampire_live_prop_choice_witness
        (vampire_live_basis_tm_expander predicate)
  | TpAp (body, tp) -> TpAp (vampire_live_basis_tm_expander body, tp)
  | Ap (left, right) ->
      Ap
        (vampire_live_basis_tm_expander left,
         vampire_live_basis_tm_expander right)
  | Lam (tp, body) -> Lam (tp, vampire_live_basis_tm_expander body)
  | All (tp, body) -> All (tp, vampire_live_basis_tm_expander body)
  | Imp (left, right) ->
      Imp
        (vampire_live_basis_tm_expander left,
         vampire_live_basis_tm_expander right)
  | TmH _ | DB _ | Prim _ as tm -> tm

let vampire_live_basis_expander proof =
  match Hashtbl.find_opt sigknh "xm", Hashtbl.find_opt sigknh "dneg" with
  | None, _ -> proof
  | Some xm_hash, dneg_hash_opt ->
      let rec expand = function
        | PPfAp (PTmAp (Known h, target), dnotnot)
            when h = Vampire_cert_v1.native_core_dneg_hash ->
            let dnotnot = expand dnotnot in
            begin match dneg_hash_opt with
            | Some dneg_hash -> PPfAp (PTmAp (Known dneg_hash, target), dnotnot)
            | None ->
                let not_target = vampire_live_case_not_tm target in
                let native_not_target =
                  PLam
                    (target,
                     vampire_live_false_elim
                       (vampire_live_not_elim target (Hyp 1) (Hyp 0))
                       vampire_native_core_false_tm)
                in
                let false_proof =
                  PPfAp (pfshift 0 1 dnotnot, native_not_target)
                in
                PPfAp
                  (PPfAp
                     (PTmAp (PTmAp (Known xm_hash, target), target),
                      PLam (target, Hyp 0)),
                   PLam (not_target, PTmAp (false_proof, target)))
            end
        | PTpAp (body, tp) -> PTpAp (expand body, tp)
        | PTmAp (body, tm) ->
            PTmAp (expand body, vampire_live_basis_tm_expander tm)
        | PPfAp (left, right) -> PPfAp (expand left, expand right)
        | PLam (prop, body) ->
            PLam (vampire_live_basis_tm_expander prop, expand body)
        | TLam (tp, body) -> TLam (tp, expand body)
        | Known h ->
            begin match vampire_native_core_not_forall_exists_hash_tp h with
            | Some tp ->
                begin match vampire_live_not_forall_exists_proof tp with
                | Some proof -> proof
                | None -> Known h
                end
            | None ->
                if h = Vampire_cert_v1.native_core_exists_choice_hash Set then
                  begin match vampire_live_exists_set_choice_proof () with
                  | Some proof -> proof
                  | None -> Known h
                  end
                else if h = Vampire_cert_v1.native_core_exists_choice_hash Prop then
                  begin match vampire_live_exists_prop_choice_checked_proof () with
                  | Some proof -> proof
                  | None -> Known h
                  end
                else Known h
            end
        | Hyp _ as proof -> proof
      in
      expand proof

let vampire_prop_ext_variants ?delta proof =
  let directional = vampire_directional_prop_ext_expander proof in
  let rec add_unique seen acc = function
    | [] -> List.rev acc
    | proof :: rest ->
        if List.exists ((=) proof) seen then add_unique seen acc rest
        else add_unique (proof :: seen) (proof :: acc) rest
  in
  add_unique
    []
    []
    [
      vampire_loaded_prop_ext_expander ?delta directional;
      vampire_loaded_prop_ext_expander ?delta proof;
      directional;
      proof;
    ]

let vampire_expanded_prop_ext_variants ?delta proof_expander proof =
  vampire_prop_ext_variants ?delta (vampire_live_basis_expander (proof_expander proof))

let vampire_debug_bad_proof_application proof_delta symbol_table cx hyps proof =
  let short_tm tm =
    let text = tm_to_str tm in
    if String.length text <= 500 then text
    else String.sub text 0 500 ^ "..."
  in
  let short_pf pf =
    let text = pf_to_str pf in
    if String.length text <= 500 then text
    else String.sub text 0 500 ^ "..."
  in
  let tm_symbols tm =
    let seen = Hashtbl.create 17 in
    let rec collect = function
      | TmH name ->
          if not (Hashtbl.mem seen name) then Hashtbl.add seen name ()
      | TpAp (body, _) -> collect body
      | Ap (left, right) ->
          collect left;
          collect right
      | Lam (_, body) | All (_, body) -> collect body
      | Imp (left, right) ->
          collect left;
          collect right
      | DB _ | Prim _ -> ()
    in
    collect tm;
    Hashtbl.fold (fun name () acc -> name :: acc) seen []
    |> List.sort String.compare
  in
  let delta_note expected actual dl =
    let names = tm_symbols expected @ tm_symbols actual |> List.sort_uniq String.compare in
    let names =
      if List.length names > 16 then
        let rec take n = function
          | _ when n = 0 -> []
          | [] -> []
          | x :: xs -> x :: take (n - 1) xs
        in
        take 16 names @ ["..."]
      else
        names
    in
    let name_notes =
      List.map
        (fun name ->
           name
           ^ ":delta="
           ^ (if Hashtbl.mem proof_delta name then "yes" else "no")
           ^ ",symbol="
           ^ (if Hashtbl.mem symbol_table name then "yes" else "no"))
        names
      |> String.concat "; "
    in
    let conv0 =
      match conv expected actual proof_delta [] with
      | Some _ -> "yes"
      | None -> "no"
    in
    let convdl =
      match conv expected actual proof_delta dl with
      | Some _ -> "yes"
      | None -> "no"
    in
    "; conv0="
    ^ conv0
    ^ "; convdl="
    ^ convdl
    ^ "; symbols=["
    ^ name_notes
    ^ "]"
  in
  let rec find path cxtm cxpf proof =
    match proof with
    | PPfAp (left, right) ->
        begin match find (path ^ ".left") cxtm cxpf left with
        | Some _ as found -> found
        | None ->
            begin match find (path ^ ".right") cxtm cxpf right with
            | Some _ as found -> found
            | None ->
                begin
                  try
                    let left_prop, dl1 =
                      extr_propofpf proof_delta symbol_table cxtm cxpf left []
                    in
                    match tm_beta_eta_norm left_prop with
                    | Imp (expected, _) ->
                        begin
                          try
                            let right_prop, dl2 =
                              extr_propofpf proof_delta symbol_table cxtm cxpf right dl1
                            in
                            begin match conv expected right_prop proof_delta dl2 with
                            | Some _ -> None
                            | None ->
                                Some
                                  (path
                                   ^ ": implication argument mismatch; expected "
                                   ^ short_tm expected
                                   ^ "; actual "
                                   ^ short_tm right_prop
                                   ^ "; left proof "
                                   ^ short_pf left
                                   ^ "; right proof "
                                   ^ short_pf right
                                   ^ delta_note expected right_prop dl2)
                            end
                          with exn ->
                            Some
                              (path
                               ^ ": could not extract right proposition: "
                               ^ Printexc.to_string exn)
                        end
                    | prop ->
                        Some (path ^ ": left proposition is not implication: " ^ short_tm prop)
                  with exn ->
                    Some
                      (path
                       ^ ": could not extract left proposition: "
                       ^ Printexc.to_string exn
                       ^ "; left proof "
                       ^ short_pf left)
                end
            end
        end
    | PTpAp (body, _) -> find (path ^ ".tp") cxtm cxpf body
    | PTmAp (body, tm) ->
        begin match find (path ^ ".tm") cxtm cxpf body with
        | Some _ as found -> found
        | None ->
            begin
              try
                let body_prop, dl =
                  extr_propofpf proof_delta symbol_table cxtm cxpf body []
                in
                match headnorm body_prop proof_delta dl with
                | All _, _ -> None
                | prop, _ ->
                    Some
                      (path
                       ^ ": term application left proposition is not universal: "
                       ^ short_tm prop
                       ^ "; applied term "
                       ^ short_tm tm
                       ^ "; left proof "
                       ^ short_pf body)
              with exn ->
                Some
                  (path
                   ^ ": could not extract term-application left proposition: "
                   ^ Printexc.to_string exn
                   ^ "; left proof "
                   ^ short_pf body)
            end
        end
    | PLam (prop, body) -> find (path ^ ".plam") cxtm (prop :: cxpf) body
    | TLam (tp, body) ->
        let cxtm = tp :: cxtm in
        let cxpf = List.map (fun prop -> tmshift 0 1 prop) cxpf in
        find (path ^ ".tlam") cxtm cxpf body
    | Hyp _ | Known _ -> None
  in
  find "root" cx hyps proof

let vampire_debug_missing_live_reference proof_delta symbol_table proof =
  let rec tm_ref path = function
    | TmH name when not (Hashtbl.mem symbol_table name) ->
        Some (path ^ ": missing term symbol " ^ name)
    | TmH _ | DB _ | Prim _ -> None
    | TpAp (body, _) -> tm_ref (path ^ ".tp") body
    | Ap (left, right) ->
        begin match tm_ref (path ^ ".left") left with
        | Some _ as result -> result
        | None -> tm_ref (path ^ ".right") right
        end
    | Lam (_, body) | All (_, body) -> tm_ref (path ^ ".body") body
    | Imp (left, right) ->
        begin match tm_ref (path ^ ".left") left with
        | Some _ as result -> result
        | None -> tm_ref (path ^ ".right") right
        end
  in
  let rec pf_ref path = function
    | Known name when not (Hashtbl.mem proof_delta name) ->
        Some (path ^ ": missing proof constant " ^ name)
    | Known _ | Hyp _ -> None
    | PTpAp (proof, _) -> pf_ref (path ^ ".proof") proof
    | PTmAp (proof, tm) ->
        begin match pf_ref (path ^ ".proof") proof with
        | Some _ as result -> result
        | None -> tm_ref (path ^ ".term") tm
        end
    | PPfAp (left, right) ->
        begin match pf_ref (path ^ ".left") left with
        | Some _ as result -> result
        | None -> pf_ref (path ^ ".right") right
        end
    | PLam (prop, proof) ->
        begin match tm_ref (path ^ ".prop") prop with
        | Some _ as result -> result
        | None -> pf_ref (path ^ ".proof") proof
        end
    | TLam (_, proof) -> pf_ref (path ^ ".proof") proof
  in
  pf_ref "root" proof

let vampire_debug_proof_variants prefix proof_delta symbol_table cx hyps expected variants =
  let short_tm tm =
    let text = tm_to_str tm in
    if String.length text <= 500 then text
    else String.sub text 0 500 ^ "..."
  in
  List.iteri
    (fun index proof ->
       try
         let actual, dl =
           extr_propofpf proof_delta symbol_table cx hyps proof []
         in
         let convertible =
           match conv actual expected proof_delta dl with
           | Some _ -> "yes"
           | None -> "no"
         in
         Printf.printf
           "%s variant %d actual: %s; convertible=%s\n"
           prefix
           index
           (short_tm actual)
           convertible
       with exn ->
         Printf.printf
           "%s variant %d rejected: %s\n"
           prefix
           index
           (Printexc.to_string exn);
         begin match
           vampire_debug_bad_proof_application
             proof_delta symbol_table cx hyps proof
         with
         | Some detail ->
             Printf.printf "%s variant %d bad application: %s\n" prefix index detail
         | None -> ()
         end)
    variants

let vampire_check_current_goal_proof ?source_map ?extra_delta ?extra_symbols claimtm cxtm cxpf proof =
  let cx =
    List.filter_map
      (fun (_, (tp, definition)) ->
         match definition with
         | None -> Some tp
         | Some _ -> None)
      cxtm
  in
  let hyps = List.map snd cxpf in
  let proof_delta =
    match source_map with
    | None -> vampire_source_context_delta_with_locals cxtm
    | Some source_map ->
        vampire_source_context_delta_with_source_map ~cxtm source_map
  in
  begin match extra_delta with
  | None -> ()
  | Some _ ->
      Hashtbl.iter
        (fun h v -> Hashtbl.replace proof_delta h v)
        (Vampire_cert_v1.approved_native_sgdelta ())
  end;
  begin match extra_delta with
  | None -> ()
  | Some extra_delta ->
      vampire_merge_reconstruction_delta proof_delta extra_delta
  end;
  let symbol_table =
    match source_map with
    | None -> sigtmof
    | Some source_map -> vampire_source_context_symbol_table_with_source_map source_map
  in
  begin match extra_symbols with
  | None -> ()
  | Some extra_symbols ->
      Hashtbl.iter
        (fun h v ->
           if not (Hashtbl.mem symbol_table h) then Hashtbl.add symbol_table h v)
        extra_symbols
  end;
  let live_delta = vampire_source_context_delta_with_locals cxtm in
  let live_symbol_table =
    match source_map with
    | None -> Hashtbl.copy sigtmof
    | Some source_map -> vampire_source_context_symbol_table_with_source_map source_map
  in
  let empty_extra_delta = Hashtbl.create 1 in
  let certificate_delta =
    match extra_delta with
    | Some extra_delta -> extra_delta
    | None -> empty_extra_delta
  in
  let certificate_hyps =
    List.map
      (vampire_expand_returned_tm ?extra_delta cxtm source_map)
      hyps
  in
  let returned_body_expander tm =
    vampire_live_basis_tm_expander
      (vampire_expand_returned_tm cxtm source_map tm)
  in
  let live_extra_delta =
    match extra_delta, extra_symbols with
    | Some extra_delta, Some extra_symbols ->
        Some
          (vampire_live_safe_extra_delta
             ~body_expander:returned_body_expander
             live_symbol_table
             extra_symbols
             extra_delta)
    | Some extra_delta, None -> Some extra_delta
    | None, _ -> None
  in
  let proof_expander =
    vampire_expand_returned_proof ?extra_delta:live_extra_delta cxtm source_map
  in
  let live_hyps =
    List.map
      (vampire_expand_returned_tm ?extra_delta:live_extra_delta cxtm source_map)
      hyps
  in
  let live_check proof =
    try
      begin match extra_symbols with
      | Some extra_symbols ->
          begin match
            vampire_certificate_only_symbol_in_proof
              live_symbol_table
              certificate_delta
              extra_symbols
              proof
          with
          | Some _ -> None
          | None ->
              let (actual, dl) =
                extr_propofpf live_delta live_symbol_table cx live_hyps proof []
              in
              begin match
                vampire_certificate_only_symbol_in_tm
                  live_symbol_table
                  extra_symbols
                  actual
              with
              | Some _ -> None
              | None ->
              begin match conv actual claimtm live_delta dl with
              | Some _ ->
                  begin match check_propofpf live_delta live_symbol_table cx live_hyps proof claimtm [] with
                  | Some _ -> Some proof
                  | None -> None
                  end
              | None -> None
              end
              end
          end
      | None ->
        let (actual, dl) =
          extr_propofpf live_delta live_symbol_table cx live_hyps proof []
        in
        match conv actual claimtm live_delta dl with
        | Some _ ->
            begin match check_propofpf live_delta live_symbol_table cx live_hyps proof claimtm [] with
            | Some _ -> Some proof
            | None -> None
            end
          | None -> None
      end
    with _ -> None
  in
  let debug = Sys.getenv_opt "MEGALODON_CERT_DEBUG" = Some "1" in
  let rec try_variants = function
    | [] -> None
    | proof_for_check :: rest ->
        try
          let (actual,dl) = extr_propofpf proof_delta symbol_table cx certificate_hyps proof_for_check [] in
          match conv actual claimtm proof_delta dl with
          | Some _ ->
              let expanded_variants =
                vampire_expanded_prop_ext_variants ~delta:live_delta proof_expander proof_for_check
              in
              begin match List.find_map live_check expanded_variants with
              | Some _ as result -> result
              | None ->
                  let expanded =
                    match expanded_variants with
                    | first :: _ -> first
                    | [] -> proof_expander proof_for_check
                  in
                  if debug then
                    begin
                      Printf.printf
                        "Vampire native certificate current-goal proof candidate checked only with certificate delta at line %d char %d; rejecting live proof.\n"
                        !lineno
                        !charno;
                      vampire_debug_proof_variants
                        "Vampire native certificate current-goal live-expanded"
                        live_delta
                        live_symbol_table
                        cx
                        live_hyps
                        claimtm
                        expanded_variants;
                      begin match extra_symbols with
                      | Some extra_symbols ->
                          begin match
                            vampire_debug_certificate_only_symbol_in_proof
                              live_symbol_table
                              certificate_delta
                              extra_symbols
                              expanded
                          with
                          | Some detail ->
                              Printf.printf
                                "Vampire native certificate current-goal live rejection certificate-only proof detail: %s\n"
                                detail
                          | None -> ()
                          end
                      | None -> ()
                      end;
                      begin match
                        vampire_debug_bad_proof_application
                          live_delta live_symbol_table cx live_hyps expanded
                      with
                      | Some detail ->
                          Printf.printf
                            "Vampire native certificate current-goal live bad application: %s\n"
                            detail
                      | None -> ()
                      end;
                      flush stdout
                    end;
                  try_variants rest
              end
          | None ->
              if debug then
                begin
                  Printf.printf
                    "Vampire native certificate current-goal proof candidate has wrong proposition at line %d char %d.\nexpected: %s\nactual: %s\n"
                    !lineno
                    !charno
                    (tm_to_str claimtm)
                    (tm_to_str actual);
                  flush stdout
                end;
              try_variants rest
        with
        | Failure msg ->
            if debug then
              begin
                Printf.printf
                  "Vampire native certificate current-goal proof candidate rejected at line %d char %d: %s.\n"
                  !lineno
                  !charno
                  msg;
                  begin match
                    vampire_debug_bad_proof_application
                    proof_delta symbol_table cx certificate_hyps proof_for_check
                with
                | Some detail ->
                    Printf.printf
                      "Vampire native certificate current-goal bad application: %s\n"
                      detail
                | None -> ()
                end;
                flush stdout
              end;
            try_variants rest
        | _ -> try_variants rest
  in
  try_variants (vampire_prop_ext_variants ~delta:proof_delta proof)

let vampire_check_proof_of_prop ?source_map ?extra_delta ?extra_symbols cxtm cxpf expected proof =
  let cx =
    List.filter_map
      (fun (_, (tp, definition)) ->
         match definition with
         | None -> Some tp
         | Some _ -> None)
      cxtm
  in
  let hyps = List.map snd cxpf in
  let proof_delta =
    match source_map with
    | None -> vampire_source_context_delta_with_locals cxtm
    | Some source_map ->
        vampire_source_context_delta_with_source_map ~cxtm source_map
  in
  begin match extra_delta with
  | None -> ()
  | Some _ ->
      Hashtbl.iter
        (fun h v -> Hashtbl.replace proof_delta h v)
        (Vampire_cert_v1.approved_native_sgdelta ())
  end;
  begin match extra_delta with
  | None -> ()
  | Some extra_delta ->
      vampire_merge_reconstruction_delta proof_delta extra_delta
  end;
  let symbol_table =
    match source_map with
    | None -> sigtmof
    | Some source_map -> vampire_source_context_symbol_table_with_source_map source_map
  in
  begin match extra_symbols with
  | None -> ()
  | Some extra_symbols ->
      Hashtbl.iter
        (fun h v ->
           if not (Hashtbl.mem symbol_table h) then Hashtbl.add symbol_table h v)
        extra_symbols
  end;
  let live_delta = vampire_source_context_delta_with_locals cxtm in
  let live_symbol_table =
    match source_map with
    | None -> Hashtbl.copy sigtmof
    | Some source_map -> vampire_source_context_symbol_table_with_source_map source_map
  in
  let empty_extra_delta = Hashtbl.create 1 in
  let certificate_delta =
    match extra_delta with
    | Some extra_delta -> extra_delta
    | None -> empty_extra_delta
  in
  let certificate_hyps =
    List.map
      (vampire_expand_returned_tm ?extra_delta cxtm source_map)
      hyps
  in
  let returned_body_expander tm =
    vampire_live_basis_tm_expander
      (vampire_expand_returned_tm cxtm source_map tm)
  in
  let live_extra_delta =
    match extra_delta, extra_symbols with
    | Some extra_delta, Some extra_symbols ->
        Some
          (vampire_live_safe_extra_delta
             ~body_expander:returned_body_expander
             live_symbol_table
             extra_symbols
             extra_delta)
    | Some extra_delta, None -> Some extra_delta
    | None, _ -> None
  in
  let proof_expander =
    vampire_expand_returned_proof ?extra_delta:live_extra_delta cxtm source_map
  in
  let live_hyps =
    List.map
      (vampire_expand_returned_tm ?extra_delta:live_extra_delta cxtm source_map)
      hyps
  in
  let live_check expanded =
    match extra_symbols with
    | None -> Some expanded
    | Some extra_symbols ->
        begin match
          vampire_certificate_only_symbol_in_proof
            live_symbol_table
            certificate_delta
            extra_symbols
            expanded
        with
        | Some _ -> None
        | None ->
            try
              let (actual, dl) =
                extr_propofpf live_delta live_symbol_table cx live_hyps expanded []
              in
              begin match
                vampire_certificate_only_symbol_in_tm
                  live_symbol_table
                  extra_symbols
                  actual
              with
              | Some _ -> None
              | None ->
                  begin match conv actual expected live_delta dl with
                  | Some _ ->
                      begin match check_propofpf live_delta live_symbol_table cx live_hyps expanded expected [] with
                      | Some _ -> Some expanded
                      | None -> None
                      end
                  | None -> None
                  end
              end
            with _ -> None
        end
  in
  let debug = Sys.getenv_opt "MEGALODON_CERT_DEBUG" = Some "1" in
  let rec try_variants = function
    | [] -> None
    | proof_for_check :: rest ->
        try
          let (actual,dl) = extr_propofpf proof_delta symbol_table cx certificate_hyps proof_for_check [] in
          match conv actual expected proof_delta dl with
          | Some _ ->
              let expanded_variants =
                vampire_expanded_prop_ext_variants ~delta:live_delta proof_expander proof_for_check
              in
              begin match List.find_map live_check expanded_variants with
              | Some _ as result -> result
              | None ->
                  let expanded =
                    match expanded_variants with
                    | first :: _ -> first
                    | [] -> proof_expander proof_for_check
                  in
                  if debug then
                    begin
                      Printf.printf
                        "Vampire native proof-of-prop candidate checked only with certificate delta at line %d char %d; rejecting live proof.\n"
                        !lineno
                        !charno;
                      vampire_debug_proof_variants
                        "Vampire native proof-of-prop live-expanded"
                        live_delta
                        live_symbol_table
                        cx
                        live_hyps
                        expected
                        expanded_variants;
                      begin match extra_symbols with
                      | Some extra_symbols ->
                          begin match
                            vampire_debug_certificate_only_symbol_in_proof
                              live_symbol_table
                              certificate_delta
                              extra_symbols
                              expanded
                          with
                          | Some detail ->
                              Printf.printf
                                "Vampire native proof-of-prop live rejection certificate-only proof detail: %s\n"
                                detail
                          | None -> ()
                          end
                      | None -> ()
                      end;
                      begin match
                        vampire_debug_bad_proof_application
                          live_delta live_symbol_table cx live_hyps expanded
                      with
                      | Some detail ->
                          Printf.printf
                            "Vampire native proof-of-prop live bad application: %s\n"
                            detail
                      | None -> ()
                      end;
                      flush stdout
                    end;
                  try_variants rest
              end
          | None ->
              if debug then
                begin
                  Printf.printf
                    "Vampire native proof-of-prop candidate has wrong proposition at line %d char %d.\nexpected: %s\nactual: %s\n"
                    !lineno
                    !charno
                    (tm_to_str expected)
                    (tm_to_str actual);
                  flush stdout
                end;
              try_variants rest
        with
        | Failure msg ->
            if debug then
              begin
                Printf.printf
                  "Vampire native proof-of-prop candidate rejected at line %d char %d: %s.\n"
                  !lineno
                  !charno
                  msg;
                begin match
                  vampire_debug_bad_proof_application
                    proof_delta symbol_table cx certificate_hyps proof_for_check
                with
                | Some detail ->
                    Printf.printf
                      "Vampire native proof-of-prop bad application: %s\n"
                      detail
                | None -> ()
                end;
                flush stdout
              end;
            try_variants rest
        | _ -> try_variants rest
  in
  try_variants (vampire_prop_ext_variants ~delta:proof_delta proof)

let vampire_actual_prop_of_proof ?source_map ?extra_delta ?extra_symbols cxtm cxpf proof =
  let cx =
    List.filter_map
      (fun (_, (tp, definition)) ->
         match definition with
         | None -> Some tp
         | Some _ -> None)
      cxtm
  in
  let hyps = List.map snd cxpf in
  let proof_delta =
    match source_map with
    | None -> vampire_source_context_delta_with_locals cxtm
    | Some source_map ->
        vampire_source_context_delta_with_source_map ~cxtm source_map
  in
  begin match extra_delta with
  | None -> ()
  | Some _ ->
      Hashtbl.iter
        (fun h v -> Hashtbl.replace proof_delta h v)
        (Vampire_cert_v1.approved_native_sgdelta ())
  end;
  begin match extra_delta with
  | None -> ()
  | Some extra_delta ->
      vampire_merge_reconstruction_delta proof_delta extra_delta
  end;
  let symbol_table =
    match source_map with
    | None -> sigtmof
    | Some source_map -> vampire_source_context_symbol_table_with_source_map source_map
  in
  begin match extra_symbols with
  | None -> ()
  | Some extra_symbols ->
      Hashtbl.iter
        (fun h v ->
           if not (Hashtbl.mem symbol_table h) then Hashtbl.add symbol_table h v)
        extra_symbols
  end;
  let hyps =
    List.map
      (vampire_expand_returned_tm ?extra_delta cxtm source_map)
      hyps
  in
  let rec try_variants = function
    | [] -> None
    | proof_for_check :: rest ->
        try
          let actual, _ = extr_propofpf proof_delta symbol_table cx hyps proof_for_check [] in
          Some (vampire_expand_returned_tm ?extra_delta cxtm source_map actual)
        with
        | Failure _ -> try_variants rest
        | _ -> try_variants rest
  in
  try_variants (vampire_prop_ext_variants ~delta:proof_delta proof)

let vampire_xm_double_negation_elim_to ?source_map ?extra_delta ?extra_symbols target cxtm cxpf dnotnot =
  let debug = Sys.getenv_opt "MEGALODON_CERT_DEBUG" = Some "1" in
  let check candidate =
    vampire_check_proof_of_prop ?source_map ?extra_delta ?extra_symbols cxtm cxpf target candidate
  in
  let false_elim proof target =
    match vampire_available_known "FalseE" with
    | Some false_elim_hash -> PTmAp (PPfAp (Known false_elim_hash, proof), target)
    | None -> PTmAp (proof, target)
  in
  let native_false_to proof target =
    PTmAp (proof, target)
  in
  let not_claim = Imp(target,TmH(!fal)) in
  let native_not_from_live_not =
    PLam
      (target,
       false_elim (PPfAp (Hyp 1, Hyp 0)) vampire_native_core_false_tm)
  in
  let native_false_from_live_not dnotnot =
    PPfAp (pfshift 0 1 dnotnot, native_not_from_live_not)
  in
  let live_notnot_from_native_notnot =
    PLam
      (not_claim,
       native_false_to
         (native_false_from_live_not dnotnot)
         (TmH(!fal)))
  in
  let try_dneg () =
    begin match
      check
        (PPfAp (PTmAp (Known Vampire_cert_v1.native_core_dneg_hash, target), dnotnot))
    with
    | Some _ as result -> result
    | None ->
        match Hashtbl.find_opt sigknh "dneg" with
        | Some dneg_hash ->
            begin match check (PPfAp (PTmAp (Known dneg_hash, target), dnotnot)) with
            | Some _ as result -> result
            | None ->
                check
                  (PPfAp
                     (PTmAp (Known dneg_hash, target),
                      live_notnot_from_native_notnot))
            end
        | None -> None
    end
  in
  match Hashtbl.find_opt sigknh "xm" with
  | None ->
      begin match try_dneg () with
      | Some _ as result -> result
      | None ->
          if debug then
            begin
              Printf.printf
                "Vampire native certificate double-negation elimination has no xm/dneg proof for target: %s\n"
                (tm_to_str target);
              flush stdout
            end;
          None
      end
  | Some xm_hash ->
      let dfalse = PPfAp(pfshift 0 1 dnotnot,Hyp(0)) in
      let candidate =
        PPfAp
          (PPfAp
             (PTmAp(PTmAp(Known(xm_hash),target),target),
              PLam(target,Hyp(0))),
           PLam(not_claim,PTmAp(dfalse,target)))
      in
      let converted_false_candidate =
        PPfAp
          (PPfAp
             (PTmAp(PTmAp(Known(xm_hash),target),target),
              PLam(target,Hyp(0))),
           PLam
             (not_claim,
              native_false_to
                (native_false_from_live_not dnotnot)
                target))
      in
      let result =
        match check converted_false_candidate with
        | Some _ as result -> result
        | None -> check candidate
      in
      if result = None && debug then
        begin
          Printf.printf
            "Vampire native certificate double-negation elimination candidate rejected for target: %s\n"
            (tm_to_str target);
          flush stdout
        end;
      begin match result with
      | Some _ -> result
      | None ->
          begin match try_dneg () with
          | Some _ as dneg_result -> dneg_result
          | None -> None
          end
      end

let vampire_xm_double_negation_elim ?source_map ?extra_delta ?extra_symbols claimtm cxtm cxpf dnotnot =
  match vampire_xm_double_negation_elim_to ?source_map ?extra_delta ?extra_symbols claimtm cxtm cxpf dnotnot with
  | Some proof -> vampire_check_current_goal_proof ?source_map ?extra_delta ?extra_symbols claimtm cxtm cxpf proof
  | None -> None

let vampire_false_like tm =
  match conv tm vampire_native_core_false_tm sigdelta [] with
  | Some _ -> true
  | None ->
      begin match conv tm (TmH(!fal)) sigdelta [] with
      | Some _ -> true
      | None -> false
      end

let rec vampire_double_negation_target = function
  | Imp (Imp (target, false_left), false_right)
      when vampire_false_like false_left && vampire_false_like false_right ->
      Some target
  | All (tp, body) ->
      begin match vampire_double_negation_target body with
      | Some target ->
          if free_in_tm_p target 0 then Some (All (tp, target))
          else
            begin
              try Some (tmshift 0 (-1) target)
              with NegDB -> None
            end
      | None -> None
      end
  | _ -> None

let rec vampire_native_negation_target = function
  | All (Prop, Imp (target, DB 0)) -> Some target
  | All (Prop, Imp (target, false_tm)) when vampire_false_like false_tm -> Some target
  | Imp (target, false_tm) when vampire_false_like false_tm -> Some target
  | All (tp, body) ->
      begin match vampire_native_negation_target body with
      | Some target ->
          if free_in_tm_p target 0 then Some (All (tp, target))
          else Some (tmshift 0 (-1) target)
      | None -> None
      end
  | _ -> None

let vampire_native_refutation_target = function
  | All (Prop, Imp (native_negation, DB 0)) ->
      vampire_native_negation_target native_negation
  | Imp (native_negation, target) ->
      begin match vampire_native_negation_target native_negation with
      | Some native_target when native_target = target -> Some target
      | _ -> None
      end
  | _ -> None

let vampire_cps_target = function
  | All (Prop, Imp (Imp (target, DB 0), DB 0)) ->
      if free_in_tm_p target 0 then None
      else
        begin
          try Some (tmshift 0 (-1) target)
          with NegDB -> None
        end
  | _ -> None

let vampire_xm_cps_elim_to ?source_map ?extra_delta ?extra_symbols target cxtm cxpf proof proposition =
  let proof_delta =
    match source_map with
    | None -> vampire_source_context_delta_with_locals cxtm
    | Some source_map ->
        vampire_source_context_delta_with_source_map ~cxtm source_map
  in
  begin match extra_delta with
  | None -> ()
  | Some extra_delta ->
      vampire_merge_reconstruction_delta proof_delta extra_delta
  end;
  match vampire_cps_target proposition with
  | Some cps_target ->
      begin match conv cps_target target proof_delta [] with
      | Some _ ->
          let candidate =
            PPfAp
              (PTmAp (proof, target),
               PLam (target, Hyp 0))
          in
          let result =
            vampire_check_proof_of_prop
              ?source_map
              ?extra_delta
              ?extra_symbols
              cxtm
              cxpf
              target
              candidate
          in
          if result = None && Sys.getenv_opt "MEGALODON_CERT_DEBUG" = Some "1" then
            begin
              Printf.printf
                "Vampire native certificate CPS elimination candidate rejected.\ntarget: %s\ncps target: %s\n"
                (tm_to_str target)
                (tm_to_str cps_target);
              flush stdout
            end;
          result
      | None -> None
      end
  | None -> None

let vampire_xm_native_refutation_elim_to
    ?source_map
    ?extra_delta
    ?extra_symbols
    target
    cxtm
    cxpf
    proof
    proposition =
  let debug = Sys.getenv_opt "MEGALODON_CERT_DEBUG" = Some "1" in
  let check candidate =
    vampire_check_proof_of_prop ?source_map ?extra_delta ?extra_symbols cxtm cxpf target candidate
  in
  let false_elim proof target =
    match vampire_available_known "FalseE" with
    | Some false_elim_hash -> PTmAp (PPfAp (Known false_elim_hash, proof), target)
    | None -> PTmAp (proof, target)
  in
  let proof_delta =
    match source_map with
    | None -> vampire_source_context_delta_with_locals cxtm
    | Some source_map ->
        vampire_source_context_delta_with_source_map ~cxtm source_map
  in
  begin match extra_delta with
  | None -> ()
  | Some extra_delta ->
      vampire_merge_reconstruction_delta proof_delta extra_delta
  end;
  let convertible left right =
    match conv left right proof_delta [] with
    | Some _ -> true
    | None -> false
  in
  let native_negation_from_live_not native_negation =
    match native_negation with
    | All (Prop, Imp (native_target, DB 0))
        when convertible native_target target ->
        TLam
          (Prop,
           PLam
             (tmshift 0 1 target,
              false_elim (PPfAp (Hyp 1, Hyp 0)) (DB 0)))
    | All (Prop, Imp (native_target, false_tm))
        when convertible native_target target && vampire_false_like false_tm ->
        TLam
          (Prop,
           PLam
             (tmshift 0 1 target,
              PPfAp (Hyp 1, Hyp 0)))
    | Imp (native_target, false_tm)
        when convertible native_target target && vampire_false_like false_tm ->
        PLam
          (target,
           PPfAp (Hyp 1, Hyp 0))
    | _ ->
        TLam
          (Prop,
           PLam
             (tmshift 0 1 target,
              false_elim (PPfAp (Hyp 1, Hyp 0)) (DB 0)))
  in
  let refutation_for_target =
    match proposition with
    | All (Prop, Imp (native_negation, DB 0)) ->
        begin match vampire_native_negation_target native_negation with
        | Some native_target when convertible native_target target ->
            Some (PTmAp (proof, target), native_negation, false)
        | _ -> None
        end
    | All (Prop, Imp (native_negation, false_result))
        when vampire_false_like false_result ->
        begin match vampire_native_negation_target native_negation with
        | Some native_target when convertible native_target target ->
            Some (PTmAp (proof, vampire_native_core_false_tm), native_negation, true)
        | _ -> None
        end
    | All (Prop, body) ->
        let instantiated = tmsubst body 0 target in
        if debug then
          begin
            Printf.printf
              "Vampire native certificate trying native-refutation detection after target instantiation.\ninstantiated: %s\ntarget: %s\n"
              (tm_to_str instantiated)
              (tm_to_str target);
            flush stdout
          end;
        begin match instantiated with
        | Imp (native_negation, result)
            when convertible result target ->
            begin match vampire_native_negation_target native_negation with
            | Some native_target when convertible native_target target ->
                Some (PTmAp (proof, target), native_negation, false)
            | _ -> None
            end
        | _ ->
            let instantiated_false = tmsubst body 0 vampire_native_core_false_tm in
            if debug then
              begin
                Printf.printf
                  "Vampire native certificate trying native-refutation detection after native-false instantiation.\ninstantiated: %s\n"
                  (tm_to_str instantiated_false);
                flush stdout
              end;
            begin match instantiated_false with
            | Imp (native_negation, false_result)
                when vampire_false_like false_result ->
                begin match vampire_native_negation_target native_negation with
                | Some native_target when convertible native_target target ->
                    Some (PTmAp (proof, vampire_native_core_false_tm), native_negation, true)
                | _ -> None
                end
            | _ -> None
            end
        end
    | Imp (native_negation, result)
        when convertible result target ->
        begin match vampire_native_negation_target native_negation with
        | Some native_target when convertible native_target target ->
            Some (proof, native_negation, false)
        | _ -> None
        end
    | _ -> None
  in
  match refutation_for_target, Hashtbl.find_opt sigknh "xm" with
  | Some (refutes_native_negation, native_negation, returns_native_false), Some xm_hash ->
      if debug then
        begin
          Printf.printf
            "Vampire native certificate found native refutation for target.\ntarget: %s\nnative negation: %s\nreturns native false: %s\n"
            (tm_to_str target)
            (tm_to_str native_negation)
            (if returns_native_false then "yes" else "no");
          flush stdout
        end;
      let live_not_target = Imp (target, TmH (!fal)) in
      let native_negation_from_live_not =
        native_negation_from_live_not native_negation
      in
      let candidate =
        PPfAp
          (PPfAp
             (PTmAp (PTmAp (Known xm_hash, target), target),
              PLam (target, Hyp 0)),
           PLam
             (live_not_target,
              let contradiction =
                PPfAp
                  (pfshift 0 1 refutes_native_negation,
                   native_negation_from_live_not)
              in
              if returns_native_false then PTmAp (contradiction, target)
              else contradiction))
      in
      let result = check candidate in
      if result = None && debug then
        begin
          Printf.printf
            "Vampire native certificate native-refutation elimination candidate rejected for target: %s\n"
            (tm_to_str target);
          flush stdout
        end;
      result
  | Some _, _ ->
      if debug then
        begin
          Printf.printf
            "Vampire native certificate native-refutation elimination has no xm proof for target: %s\n"
            (tm_to_str target);
          flush stdout
        end;
      None
  | None, _ -> None

let vampire_expanded_equality_sides = function
  | All (Ar (left_tp, Ar (right_tp, Prop)),
         Imp (Ap (Ap (DB 0, left_a), right_a),
              Ap (Ap (DB 0, right_b), left_b)))
    when left_tp = right_tp && left_a = left_b && right_a = right_b ->
      begin
        try
          let left = tmshift 0 (-1) left_a in
          let right = tmshift 0 (-1) right_a in
          Some (left_tp, left, right)
        with NegDB -> None
      end
  | _ -> None

let vampire_megalodon_eq_poly_hash =
  "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a"

let vampire_eq_poly_head h =
  h = !eqPoly || h = vampire_megalodon_eq_poly_hash || h = "eq" || h = "="

let vampire_equality_sides = function
  | Ap (Ap (TpAp (TmH h, tp), left), right) when vampire_eq_poly_head h ->
      Some (tp, left, right)
  | Ap (Ap (TmH h, left), right) when h = "eq" || h = "=" ->
      Some (Set, left, right)
  | tm -> vampire_expanded_equality_sides tm

let vampire_add_audited_definition_delta source_bindings source_audit delta =
  let binding_names step fallback_names =
    match
      List.find_opt
        (fun binding ->
           binding.Vampire_cert_v1.core_native_source_step = step)
        source_bindings
    with
    | None -> fallback_names
    | Some binding ->
        [
          binding.Vampire_cert_v1.core_native_source_name;
          binding.Vampire_cert_v1.core_native_tptp_name;
          binding.Vampire_cert_v1.core_native_source_hash;
        ] @ fallback_names
  in
  let add_definition names body =
    List.iter
      (fun name ->
         if name <> "" then
           Hashtbl.replace delta name (0, tm_beta_eta_norm body))
      (List.sort_uniq String.compare names)
  in
  List.iter
    (function
      | step, Vampire_source_context.Definitional (proposition, _) ->
          begin match vampire_equality_sides proposition with
          | Some (_, TmH name, body) ->
              add_definition (binding_names step [name]) body
          | Some (_, body, TmH name) ->
              add_definition (binding_names step [name]) body
          | _ -> ()
          end
      | _ -> ())
    source_audit.Vampire_source_context.resolved

let vampire_positive_equality_symmetry_proof tp left right proof =
  let predicate_sort = Ar (tp, Ar (tp, Prop)) in
  let premise =
    Ap (Ap (DB 0, tmshift 0 1 right), tmshift 0 1 left)
  in
  let motive =
    Lam (tp, Lam (tp, Ap (Ap (DB 2, DB 0), DB 1)))
  in
  TLam
    (predicate_sort,
     PLam
       (premise,
        PPfAp
          (PTmAp (pfshift 0 1 (pftmshift 0 1 proof), motive),
           Hyp 0)))

let vampire_reconstruct_goal_from_proved_prop ?source_map ?extra_delta ?extra_symbols claimtm cxtm cxpf proof proposition =
  match vampire_check_current_goal_proof ?source_map ?extra_delta ?extra_symbols claimtm cxtm cxpf proof with
  | Some _ as result -> result
  | None ->
      let proof_delta =
        match source_map with
        | None -> vampire_source_context_delta_with_locals cxtm
        | Some source_map ->
            vampire_source_context_delta_with_source_map ~cxtm source_map
      in
      begin match extra_delta with
      | None -> ()
      | Some extra_delta ->
          vampire_merge_reconstruction_delta proof_delta extra_delta
      end;
      let props_convert left right =
        tm_beta_eta_norm left = tm_beta_eta_norm right
        || (conv left right proof_delta [] <> None
            && conv right left proof_delta [] <> None)
      in
      let rec structural_transport source target proof =
        if props_convert source target then
          Some proof
        else
          match tm_beta_eta_norm source, tm_beta_eta_norm target with
          | All (source_tp, source_body), All (target_tp, target_body)
              when source_tp = target_tp ->
              begin match
                structural_transport
                  source_body
                  target_body
                  (PTmAp (pftmshift 0 1 proof, DB 0))
              with
              | Some body -> Some (TLam (target_tp, body))
              | None -> None
              end
          | Imp (source_arg, source_body), Imp (target_arg, target_body)
              when props_convert source_arg target_arg ->
              begin match
                structural_transport
                  source_body
                  target_body
                  (PPfAp (pfshift 0 1 proof, Hyp 0))
              with
              | Some body -> Some (PLam (target_arg, body))
              | None -> None
              end
          | _ ->
              begin match vampire_equality_sides source, vampire_equality_sides target with
              | Some (source_tp, source_left, source_right),
                Some (target_tp, target_left, target_right)
                  when source_tp = target_tp
                       && props_convert source_left target_right
                       && props_convert source_right target_left ->
                  Some
                    (vampire_positive_equality_symmetry_proof
                       source_tp source_left source_right proof)
              | _ -> None
              end
      in
      let proposition_sides = vampire_equality_sides proposition in
      let claim_sides = vampire_equality_sides claimtm in
      begin match proposition_sides, claim_sides with
      | Some (source_tp, source_left, source_right),
        Some (goal_tp, goal_left, goal_right)
          when source_tp = goal_tp ->
          begin match
            conv source_left goal_right proof_delta [],
            conv source_right goal_left proof_delta []
          with
          | Some _, Some _ ->
              if Sys.getenv_opt "MEGALODON_CERT_DEBUG" = Some "1" then
                begin
                  Printf.printf
                    "Vampire native certificate trying equality-symmetry goal transport from %s to %s.\n"
                    (tm_to_str proposition)
                    (tm_to_str claimtm);
                  flush stdout
                end;
              let candidate =
                vampire_positive_equality_symmetry_proof
                  source_tp source_left source_right proof
              in
              let result = vampire_check_current_goal_proof ?source_map ?extra_delta ?extra_symbols claimtm cxtm cxpf candidate in
              if result = None && Sys.getenv_opt "MEGALODON_CERT_DEBUG" = Some "1" then
                begin
                  Printf.printf
                    "Vampire native certificate equality-symmetry goal transport rejected.\n";
                  flush stdout
                end;
              result
          | _ -> None
          end
      | _ ->
          begin match structural_transport proposition claimtm proof with
          | Some candidate ->
              if Sys.getenv_opt "MEGALODON_CERT_DEBUG" = Some "1" then
                begin
                  Printf.printf
                    "Vampire native certificate trying structural goal transport from %s to %s.\n"
                    (tm_to_str proposition)
                    (tm_to_str claimtm);
                  flush stdout
                end;
              let result =
                vampire_check_current_goal_proof
                  ?source_map
                  ?extra_delta
                  ?extra_symbols
                  claimtm
                  cxtm
                  cxpf
                  candidate
              in
              if result = None && Sys.getenv_opt "MEGALODON_CERT_DEBUG" = Some "1" then
                begin
                  Printf.printf
                    "Vampire native certificate structural goal transport rejected.\n";
                  flush stdout
                end;
              result
          | None ->
          if Sys.getenv_opt "MEGALODON_CERT_DEBUG" = Some "1" then
            begin
              Printf.printf
                "Vampire native certificate equality goal transport not applicable at line %d char %d; proposition_sides=%s claim_sides=%s.\nproposition: %s\nclaim: %s\n"
                !lineno
                !charno
                (match proposition_sides with Some _ -> "yes" | None -> "no")
                (match claim_sides with Some _ -> "yes" | None -> "no")
                (tm_to_str proposition)
                (tm_to_str claimtm);
              flush stdout
            end;
          None
          end
      end

let vampire_context_terms_of_type cxtm target_tp =
  let rec scan i = function
    | [] -> []
    | (_, (_, Some _)) :: rest ->
        scan i rest
    | (_, (tp, None)) :: rest ->
        let rest = scan (i + 1) rest in
        if tp = target_tp then DB(i) :: rest else rest
  in
  let candidates = scan 0 cxtm in
  match target_tp with
  | Prop ->
      List.sort_uniq compare
        (candidates @ [TmH(!fal); vampire_native_core_false_tm])
  | _ -> candidates

let vampire_ordered_unique terms =
  let rec add seen acc = function
    | [] -> List.rev acc
    | tm :: rest ->
        if List.exists ((=) tm) seen then add seen acc rest
        else add (tm :: seen) (tm :: acc) rest
  in
  add [] [] terms

let rec vampire_default_term_of_type = function
  | Prop -> Some vampire_native_core_false_tm
  | Set ->
      begin match Hashtbl.find_opt sigtmh "Empty" with
      | Some empty_hash -> Some (TmH empty_hash)
      | None -> None
      end
  | Ar (domain, codomain) ->
      begin match vampire_default_term_of_type codomain with
      | Some body -> Some (Lam (domain, tmshift 0 1 body))
      | None -> None
      end
  | TpVar _ -> None

let vampire_context_terms_with_default cxtm target_tp =
  let terms = vampire_context_terms_of_type cxtm target_tp in
  match vampire_default_term_of_type target_tp with
  | Some default -> vampire_ordered_unique (terms @ [default])
  | None -> terms

let vampire_source_map_local_terms_of_type cxtm source_map target_tp =
  let rec local_terms proof_index = function
    | [] -> []
    | (_, (_, Some _)) :: rest -> local_terms proof_index rest
    | (name, (tp, None)) :: rest ->
        (name, proof_index, tp) :: local_terms (proof_index + 1) rest
  in
  let local_terms = local_terms 0 cxtm in
  source_map
  |> List.filter_map
       (fun entry ->
          if entry.Vampire_cert_v1.source_map_kind = "local_type" then
            match
              List.find_opt
                (fun (local_name, _, tp) ->
                   local_name = entry.Vampire_cert_v1.source_map_source_name
                   && tp = target_tp)
                local_terms
            with
            | Some (_, index, _) -> Some (DB index)
            | None -> None
          else
            None)
  |> vampire_ordered_unique

let vampire_ordered_context_terms_of_type cxtm target_tp =
  let rec scan i = function
    | [] -> []
    | (_, (_, Some _)) :: rest ->
        scan i rest
    | (_, (tp, None)) :: rest ->
        let rest = scan (i + 1) rest in
        if tp = target_tp then DB(i) :: rest else rest
  in
  let candidates = scan 0 cxtm in
  match target_tp with
  | Prop ->
      vampire_ordered_unique
        (List.rev candidates
         @ candidates
         @ [TmH(!fal); vampire_native_core_false_tm])
  | _ -> candidates

let vampire_ordered_context_terms_with_default cxtm target_tp =
  let terms = vampire_ordered_context_terms_of_type cxtm target_tp in
  match vampire_default_term_of_type target_tp with
  | Some default -> vampire_ordered_unique (terms @ [default])
  | None -> terms

let vampire_ordered_local_terms_of_type cxtm target_tp =
  let rec scan i = function
    | [] -> []
    | (_, (_, Some _)) :: rest ->
        scan i rest
    | (_, (tp, None)) :: rest ->
        let rest = scan (i + 1) rest in
        if tp = target_tp then DB(i) :: rest else rest
  in
  scan 0 cxtm |> List.rev |> vampire_ordered_unique

let vampire_symbol_table ?extra_symbols source_map =
  let symbol_table = vampire_source_context_symbol_table_with_source_map source_map in
  begin match extra_symbols with
  | None -> ()
  | Some extra_symbols ->
      Hashtbl.iter
        (fun h v ->
           if not (Hashtbl.mem symbol_table h) then Hashtbl.add symbol_table h v)
        extra_symbols
  end;
  symbol_table

let vampire_candidate_terms_from_props ?extra_symbols cxtm source_map props target_tp =
  let rec term_size = function
    | DB _ | TmH _ | Prim _ -> 1
    | TpAp (body, _) -> 1 + term_size body
    | Ap (fn, arg) -> 1 + term_size fn + term_size arg
    | Lam (_, body) | All (_, body) -> 1 + term_size body
    | Imp (left, right) -> 1 + term_size left + term_size right
  in
  let cx =
    List.filter_map
      (fun (_, (tp, definition)) ->
         match definition with
         | None -> Some tp
         | Some _ -> None)
      cxtm
  in
  let symbol_table = vampire_symbol_table ?extra_symbols source_map in
  let add tm terms =
    try
      if extr_tpoftm symbol_table cx tm = target_tp then tm :: terms else terms
    with _ -> terms
  in
  let rec scan tm terms =
    let terms = add tm terms in
    match tm with
    | TpAp (body, _) -> scan body terms
    | Ap (fn, arg) -> scan arg (scan fn terms)
    | Imp (left, right) -> scan right (scan left terms)
    | Lam _ | All _ -> terms
    | DB _ | TmH _ | Prim _ -> terms
  in
  props
  |> List.fold_left (fun terms prop -> scan prop terms) []
  |> List.rev_append (vampire_context_terms_of_type cxtm target_tp)
  |> List.sort_uniq compare
  |> List.sort (fun left right -> compare (term_size left) (term_size right))

let vampire_candidate_terms_from_closed_subterms ?extra_symbols cxtm source_map props target_tp =
  let rec term_size = function
    | DB _ | TmH _ | Prim _ -> 1
    | TpAp (body, _) -> 1 + term_size body
    | Ap (fn, arg) -> 1 + term_size fn + term_size arg
    | Lam (_, body) | All (_, body) -> 1 + term_size body
    | Imp (left, right) -> 1 + term_size left + term_size right
  in
  let cx =
    List.filter_map
      (fun (_, (tp, definition)) ->
         match definition with
         | None -> Some tp
         | Some _ -> None)
      cxtm
  in
  let symbol_table = vampire_symbol_table ?extra_symbols source_map in
  let bound_free depth tm =
    let rec check i =
      i >= depth || ((not (free_in_tm_p tm i)) && check (i + 1))
    in
    check 0
  in
  let add depth tm terms =
    if not (bound_free depth tm) then terms
    else
      try
        let candidate =
          if depth = 0 then tm
          else tmshift 0 (-depth) tm
        in
        if extr_tpoftm symbol_table cx candidate = target_tp then
          candidate :: terms
        else terms
      with _ -> terms
  in
  let rec scan depth tm terms =
    let terms = add depth tm terms in
    match tm with
    | TpAp (body, _) -> scan depth body terms
    | Ap (fn, arg) -> scan depth arg (scan depth fn terms)
    | Imp (left, right) -> scan depth right (scan depth left terms)
    | Lam (_, body) | All (_, body) -> scan (depth + 1) body terms
    | DB _ | TmH _ | Prim _ -> terms
  in
  props
  |> List.fold_left (fun terms prop -> scan 0 prop terms) []
  |> List.rev_append (vampire_context_terms_of_type cxtm target_tp)
  |> vampire_ordered_unique
  |> List.sort_uniq compare
  |> List.sort (fun left right -> compare (term_size left) (term_size right))

let vampire_constructive_goal_search
    ?source_map
    ?extra_delta
    ?extra_symbols
    ?(external_proofs=[])
    claimtm
    cxtm
    cxpf =
  let proof_delta =
    match source_map with
    | None -> vampire_source_context_delta_with_locals cxtm
    | Some source_map ->
        vampire_source_context_delta_with_source_map ~cxtm source_map
  in
  begin match extra_delta with
  | None -> ()
  | Some extra_delta -> vampire_merge_reconstruction_delta proof_delta extra_delta
  end;
  let debug_constructive =
    Sys.getenv_opt "MEGALODON_CERT_DEBUG_CONSTRUCTIVE_SEARCH" = Some "1"
  in
  let convertible left right =
    match conv left right proof_delta [] with
    | Some _ -> true
    | None -> false
  in
  let expose tm =
    try fst (headnorm tm proof_delta [])
    with _ -> tm
  in
  let rec ordered_hypotheses index = function
    | [] -> []
    | proposition :: rest ->
        (Hyp index, proposition)
        :: ordered_hypotheses (index + 1) rest
  in
  let candidate_terms cxtm goal tp =
    match tp with
    | Prop ->
        vampire_ordered_unique
          (goal :: vampire_ordered_context_terms_of_type cxtm Prop)
    | _ -> vampire_ordered_context_terms_with_default cxtm tp
  in
  let rec prove depth cxtm cxpf external_proofs goal =
    if depth <= 0 then None
    else
      let church_or_branches proposition =
        match expose proposition with
        | All (Prop, Imp (Imp (left, DB 0), Imp (Imp (right, DB 0), DB 0))) ->
            Some (tmsubst left 0 goal, tmsubst right 0 goal)
        | _ -> None
      in
      let church_or_branches_for_target target proposition =
        match expose proposition with
        | All (Prop, Imp (Imp (left, DB 0), Imp (Imp (right, DB 0), DB 0))) ->
            Some (tmsubst left 0 target, tmsubst right 0 target)
        | _ -> None
      in
      let rec church_or_leaves_for_target target proposition =
        match church_or_branches_for_target target proposition with
        | None -> [proposition]
        | Some (left, right) ->
            church_or_leaves_for_target target left
            @ church_or_leaves_for_target target right
      in
      let church_or_elimination_body branches body =
        let rec collect branches body =
          match branches, expose body with
          | [], final when convertible final (DB 0) -> Some []
          | branch :: rest, Imp (Imp (actual_branch, DB 0), tail)
              when convertible branch actual_branch ->
              begin match collect rest tail with
              | None -> None
              | Some tail -> Some (actual_branch :: tail)
              end
          | _ -> None
        in
        match expose body with
        | All (Prop, body) -> collect branches body
        | _ -> None
      in
      let church_or_elimination_proof disjunction conclusion =
        let target = DB 0 in
        let shifted_disjunction = tmshift 0 1 disjunction in
        let leaves = church_or_leaves_for_target target shifted_disjunction in
        match leaves with
        | [] | [_] -> None
        | _ ->
            begin match church_or_elimination_body leaves conclusion with
            | None -> None
            | Some branches ->
                let branch_count = List.length branches in
                let rec branch_index proposition index = function
                  | [] -> None
                  | branch :: rest ->
                      if convertible proposition branch then Some index
                      else branch_index proposition (index + 1) rest
                in
                let rec build offset proof proposition =
                  match church_or_branches_for_target target proposition with
                  | None ->
                      begin match branch_index proposition 0 branches with
                      | None -> None
                      | Some index ->
                          Some
                            (PPfAp
                               (Hyp (offset + branch_count - 1 - index),
                                proof))
                      end
                  | Some (left, right) ->
                      begin match
                        build (offset + 1) (Hyp 0) left,
                        build (offset + 1) (Hyp 0) right
                      with
                      | Some left_proof, Some right_proof ->
                          Some
                            (PPfAp
                               (PPfAp
                                  (PTmAp (proof, target),
                                   PLam (left, left_proof)),
                                PLam (right, right_proof)))
                      | _ -> None
                      end
                in
                begin match build 0 (Hyp branch_count) shifted_disjunction with
                | None -> None
                | Some body ->
                    let branch_body =
                      List.fold_right
                        (fun branch body -> PLam (Imp (branch, target), body))
                        branches
                        body
                    in
                    Some (PLam (disjunction, TLam (Prop, branch_body)))
                end
            end
      in
      let church_and_pair proposition =
        match expose proposition with
        | All (Prop, Imp (Imp (left, Imp (right, DB 0)), DB 0)) ->
            Some (left, right)
        | _ -> None
      in
      let church_and_intro_from_hyps hyps goal =
        let debug_church_and =
          debug_constructive
          && Sys.getenv_opt "MEGALODON_CERT_DEBUG_CHURCH_AND" = Some "1"
        in
        let rec add_prop_binders count context =
          if count <= 0 then context
          else add_prop_binders (count - 1) (("", (Prop, None)) :: context)
        in
        let rec hypothesis_proof term_offset proof_offset leaf index = function
          | [] -> None
          | proposition :: rest ->
              if convertible leaf (tmshift 0 term_offset proposition) then
                Some (Hyp (proof_offset + index))
              else
                hypothesis_proof term_offset proof_offset leaf (index + 1) rest
        in
        let derived_leaf_proof term_offset proof_offset leaf =
          let shifted_hyps =
            List.map (fun proposition -> tmshift 0 term_offset proposition) hyps
          in
          match
            prove
              (depth - 1)
              (add_prop_binders term_offset cxtm)
              shifted_hyps
              external_proofs
              leaf
          with
          | None -> None
          | Some proof -> Some (pfshift 0 proof_offset proof)
        in
        let rec build term_offset proof_offset proposition =
          match church_and_pair proposition with
          | None ->
              let result =
                match hypothesis_proof term_offset proof_offset proposition 0 hyps with
                | Some _ as result -> result
                | None -> derived_leaf_proof term_offset proof_offset proposition
              in
              if result = None && debug_church_and then
                begin
                  Printf.printf
                    "Vampire native Church-and intro leaf miss at line %d char %d: term_offset=%d proof_offset=%d leaf=%s hyps=[%s].\n"
                    !lineno
                    !charno
                    term_offset
                    proof_offset
                    (tm_to_str proposition)
                    (String.concat "; " (List.map tm_to_str hyps));
                  flush stdout
                end;
              result
          | Some (left, right) ->
              begin match
                build (term_offset + 1) (proof_offset + 1) left,
                build (term_offset + 1) (proof_offset + 1) right
              with
              | Some left_proof, Some right_proof ->
                  Some
                    (TLam
                       (Prop,
                        PLam
                          (Imp (left, Imp (right, DB 0)),
                           PPfAp (PPfAp (Hyp 0, left_proof), right_proof))))
              | _ -> None
              end
        in
        build 0 0 goal
      in
      let church_and_intro_chain_proof goal =
        let rec split assumptions tm =
          match expose tm with
          | Imp (assumption, conclusion) ->
              split (assumption :: assumptions) conclusion
          | conclusion -> (List.rev assumptions, conclusion)
        in
        match cxpf, split [] goal with
        | _, ([], _) -> None
        | _ :: _, _ -> None
        | [], (_, conclusion) when church_and_pair conclusion = None -> None
        | [], (assumptions, conclusion) ->
            let body_hyps = List.rev assumptions @ cxpf in
            begin match church_and_intro_from_hyps body_hyps conclusion with
            | None -> None
            | Some proof ->
                Some
                  (List.fold_right
                     (fun assumption proof -> PLam (assumption, proof))
                     assumptions
                     proof)
            end
      in
      let equality_term tp left right =
        Ap (Ap (TpAp (TmH !eqPoly, tp), left), right)
      in
      let equality_hypothesis_proof tp left right =
        let rec find index = function
          | [] -> None
          | proposition :: rest ->
              if convertible proposition (equality_term tp left right) then
                Some (Hyp index)
              else
                find (index + 1) rest
        in
        find 0 cxpf
      in
      let equality_symmetry_proof goal =
        match vampire_equality_sides (expose goal) with
        | None -> None
        | Some (tp, left, right) ->
            begin match equality_hypothesis_proof tp right left with
            | None -> None
            | Some proof ->
                Some (vampire_positive_equality_symmetry_proof tp right left proof)
            end
      in
      let equality_transitivity_proof goal =
        match vampire_equality_sides (expose goal) with
        | None -> None
        | Some (tp, left, right) ->
            let rec try_middle index = function
              | [] -> None
              | (_, (middle_tp, _)) :: rest ->
                  if middle_tp = tp then
                    let middle = DB index in
                    begin match
                      equality_hypothesis_proof tp left middle,
                      equality_hypothesis_proof tp middle right
                    with
                    | Some left_to_middle, Some middle_to_right ->
                        let left1 = tmshift 0 1 left in
                        let right1 = tmshift 0 1 right in
                        let right3 = tmshift 0 2 right1 in
                        let left_to_middle =
                          pfshift 0 1 (pftmshift 0 1 left_to_middle)
                        in
                        let middle_to_right =
                          pfshift 0 1 (pftmshift 0 1 middle_to_right)
                        in
                        let q_left_right = Ap (Ap (DB 0, left1), right1) in
                        let q_u_right =
                          Lam (tp, Lam (tp, Ap (Ap (DB 2, DB 1), right3)))
                        in
                        let q_right_v =
                          Lam (tp, Lam (tp, Ap (Ap (DB 2, right3), DB 0)))
                        in
                        let q_middle_right =
                          PPfAp (PTmAp (left_to_middle, q_u_right), Hyp 0)
                        in
                        let q_right_middle =
                          PPfAp (PTmAp (middle_to_right, DB 0), q_middle_right)
                        in
                        Some
                          (TLam
                             (Ar (tp, Ar (tp, Prop)),
                              PLam
                                (q_left_right,
                                 PPfAp
                                   (PTmAp (left_to_middle, q_right_v),
                                    q_right_middle))))
                    | _ -> try_middle (index + 1) rest
                    end
                  else
                    try_middle (index + 1) rest
            in
            try_middle 0 cxtm
      in
      let prove_by_hypothesis () =
        let rec try_hypotheses = function
          | [] -> None
          | (proof, proposition) :: rest ->
              if church_or_branches proposition <> None then
                try_hypotheses rest
              else begin match prove_from depth cxtm cxpf external_proofs proof proposition goal with
              | Some _ as result -> result
              | None -> try_hypotheses rest
              end
        in
        try_hypotheses (ordered_hypotheses 0 cxpf @ external_proofs)
      in
      let prove_by_church_or_hypothesis () =
        let rec try_hypotheses = function
          | [] -> None
          | (proof, proposition) :: rest ->
              begin match church_or_branches proposition with
              | None -> try_hypotheses rest
              | Some (left, right) ->
                  let shifted_external_proofs =
                    List.map
                      (fun (proof, prop) -> (pfshift 0 1 proof, prop))
                      external_proofs
                  in
                  begin match
                    prove (depth - 1) cxtm (left :: cxpf) shifted_external_proofs goal,
                    prove (depth - 1) cxtm (right :: cxpf) shifted_external_proofs goal
                  with
                  | Some left_proof, Some right_proof ->
                      Some
                        (PPfAp
                           (PPfAp
                              (PTmAp (proof, goal),
                               PLam (left, left_proof)),
                            PLam (right, right_proof)))
                  | _ -> try_hypotheses rest
                  end
              end
        in
        try_hypotheses (ordered_hypotheses 0 cxpf @ external_proofs)
      in
      let prove_by_context () =
        match prove_by_hypothesis () with
        | Some _ as result -> result
        | None ->
            begin match equality_symmetry_proof goal with
            | Some _ as result -> result
            | None ->
                begin match equality_transitivity_proof goal with
                | Some _ as result -> result
                | None -> prove_by_church_or_hypothesis ()
                end
            end
      in
      let goal_view = expose goal in
      match goal_view with
      | Imp (assumption, conclusion) ->
          begin match church_and_intro_chain_proof goal with
          | Some _ as result -> result
          | None ->
          begin match church_or_elimination_proof assumption conclusion with
          | Some _ as result -> result
          | None ->
          let shifted_external_proofs =
            List.map
              (fun (proof, prop) -> (pfshift 0 1 proof, prop))
              external_proofs
          in
          begin match prove (depth - 1) cxtm (assumption :: cxpf) shifted_external_proofs conclusion with
          | Some proof -> Some (PLam (assumption, proof))
          | None -> prove_by_context ()
          end
          end
          end
      | All (tp, body) ->
          let shifted_cxpf = List.map (fun prop -> tmshift 0 1 prop) cxpf in
          let shifted_external_proofs =
            List.map
              (fun (proof, prop) -> (pftmshift 0 1 proof, tmshift 0 1 prop))
              external_proofs
          in
          begin match
            prove
              (depth - 1)
              (("", (tp, None)) :: cxtm)
              shifted_cxpf
              shifted_external_proofs
              body
          with
          | Some proof -> Some (TLam (tp, proof))
          | None -> prove_by_context ()
          end
      | _ -> prove_by_context ()
  and prove_from depth cxtm cxpf external_proofs proof proposition goal =
    if convertible proposition goal then
      Some proof
    else if depth <= 0 then
      None
    else
      let proposition_view = expose proposition in
      match proposition_view with
      | Imp (assumption, conclusion) ->
          begin match prove (depth - 1) cxtm cxpf external_proofs assumption with
          | Some assumption_proof ->
              prove_from
                (depth - 1)
                cxtm
                cxpf
                external_proofs
                (PPfAp (proof, assumption_proof))
                conclusion
                goal
          | None -> None
          end
      | All (tp, body) ->
          let rec try_terms = function
            | [] -> None
            | tm :: rest ->
                begin match
                  prove_from
                    (depth - 1)
                    cxtm
                    cxpf
                    external_proofs
                    (PTmAp (proof, tm))
                    (tmsubst body 0 tm)
                    goal
                with
                | Some _ as result -> result
                | None -> try_terms rest
                end
          in
          try_terms (candidate_terms cxtm goal tp)
      | _ -> None
  in
  let proof_hyps = List.map snd cxpf in
  match prove 20 cxtm proof_hyps external_proofs claimtm with
  | None ->
      if debug_constructive then
        begin
          Printf.printf
            "Vampire native constructive source-goal search found no candidate at line %d char %d for %s.\n"
            !lineno
            !charno
            (tm_to_str claimtm);
          flush stdout
        end;
      None
  | Some proof ->
      if debug_constructive then
        begin
          Printf.printf
            "Vampire native constructive source-goal search candidate at line %d char %d: %s\n"
            !lineno
            !charno
            (pf_to_str proof);
          flush stdout
        end;
      let result =
        vampire_check_current_goal_proof
          ?source_map
          ?extra_delta
          ?extra_symbols
          claimtm
          cxtm
          cxpf
          proof
      in
      if result = None
         && Sys.getenv_opt "MEGALODON_CERT_DEBUG_SOURCE_APPLY" = Some "1" then
        begin
          Printf.printf
            "Vampire native constructive source-goal search produced a candidate but final checking rejected it at line %d char %d.\n"
            !lineno
            !charno;
          flush stdout
        end;
      result

let vampire_reconstruct_current_goal_from_refutation ?source_map ?extra_delta ?extra_symbols claimtm cxtm cxpf proof proposition =
  let native_false_goal =
    if vampire_false_like proposition then
      match vampire_available_known "FalseE" with
      | Some false_elim_hash ->
          vampire_check_current_goal_proof
            ?source_map ?extra_delta ?extra_symbols
            claimtm cxtm cxpf
            (PTmAp (PPfAp (Known false_elim_hash, proof), claimtm))
      | None ->
          vampire_check_current_goal_proof
            ?source_map ?extra_delta ?extra_symbols
            claimtm cxtm cxpf
            (PTmAp (proof, claimtm))
    else None
  in
  match native_false_goal with
  | Some _ as result -> result
  | None ->
  let rec try_proof depth proof proposition =
    match vampire_actual_prop_of_proof ?source_map ?extra_delta ?extra_symbols cxtm cxpf proof with
    | None -> None
    | Some actual_proposition ->
    let proposition = actual_proposition in
    match vampire_check_current_goal_proof ?source_map ?extra_delta ?extra_symbols claimtm cxtm cxpf proof with
    | Some _ as result -> result
    | None ->
        begin match
          vampire_reconstruct_goal_from_proved_prop
            ?source_map ?extra_delta ?extra_symbols
            claimtm cxtm cxpf proof proposition
        with
        | Some _ as result -> result
        | None ->
        begin
          match vampire_xm_native_refutation_elim_to
                  ?source_map ?extra_delta ?extra_symbols
                  claimtm cxtm cxpf proof proposition with
          | Some _ as result -> result
          | None ->
              begin
                match vampire_xm_cps_elim_to ?source_map ?extra_delta ?extra_symbols claimtm cxtm cxpf proof proposition with
                | Some _ as result -> result
                | None ->
              begin
                match vampire_xm_double_negation_elim ?source_map ?extra_delta ?extra_symbols claimtm cxtm cxpf proof with
                | Some _ as result -> result
                | None ->
                    begin match vampire_double_negation_target proposition with
                    | Some target ->
                        if Sys.getenv_opt "MEGALODON_CERT_DEBUG" = Some "1" then
                          begin
                            Printf.printf
                              "Vampire native certificate found double-negated target for current goal: %s\n"
                              (tm_to_str target);
                            flush stdout
                          end;
                        begin match vampire_xm_double_negation_elim_to ?source_map ?extra_delta ?extra_symbols target cxtm cxpf proof with
                        | Some target_proof ->
                            begin match
                              vampire_reconstruct_goal_from_proved_prop
                                ?source_map
                                ?extra_delta
                                ?extra_symbols
                                claimtm cxtm cxpf target_proof target
                            with
                            | Some _ as result -> result
                            | None -> None
                            end
                        | None -> None
                        end
                    | None ->
                        if depth <= 0 then None
                        else
                          match proposition with
                          | All(tp,body) ->
                              let rec try_terms = function
                                | [] -> None
                                | tm :: rest ->
                                    begin
                                      match
                                        try_proof
                                          (depth - 1)
                                          (PTmAp(proof,tm))
                                          (tmsubst body 0 tm)
                                      with
                                      | Some _ as result -> result
                                      | None -> try_terms rest
                                    end
                              in
                              let terms =
                                match tp with
                                | Prop ->
                                    List.sort_uniq compare
                                      (claimtm :: vampire_context_terms_of_type cxtm tp)
                                | _ -> vampire_context_terms_of_type cxtm tp
                              in
                              try_terms terms
                          | _ -> None
                    end
              end
              end
        end
        end
  in
  match try_proof 8 proof proposition with
  | Some _ as result -> result
  | None ->
      if !vampireabyqualifying then None
      else
        vampire_constructive_goal_search
          ?source_map
          ?extra_delta
          ?extra_symbols
          claimtm
          cxtm
          cxpf

let vampire_reconstruct_goal_from_supplied_refutation
    ?source_map
    ?extra_delta
    ?extra_symbols
    ?preferred_prop_terms
    ?(unchecked_final=false)
    claimtm
    cxtm
    cxpf
    source_target
    proof
    proposition =
  let proof_delta =
    match source_map with
    | None -> vampire_source_context_delta_with_locals cxtm
    | Some source_map ->
        vampire_source_context_delta_with_source_map ~cxtm source_map
  in
  begin match extra_delta with
  | None -> ()
  | Some extra_delta ->
      vampire_merge_reconstruction_delta proof_delta extra_delta
  end;
  match conv source_target claimtm proof_delta [] with
  | None -> None
  | Some _ ->
      let initial_preferred_prop_terms =
        match preferred_prop_terms with
        | Some terms -> terms
        | None -> []
      in
      let remove_term tm terms =
        List.filter (fun candidate -> candidate <> tm) terms
      in
      let finish target_proof target =
        vampire_reconstruct_goal_from_proved_prop
          ?source_map
          ?extra_delta
          ?extra_symbols
          claimtm
          cxtm
          cxpf
          target_proof
          target
      in
      let unchecked_timing_start = Unix.gettimeofday () in
      let unchecked_timing_last = ref unchecked_timing_start in
      let unchecked_timing stage =
        if Sys.getenv_opt "MEGALODON_CERT_DEBUG_TIMING" = Some "1" then
          begin
            let now = Unix.gettimeofday () in
            Printf.printf
              "Vampire native supplied-refutation unchecked finish timing %s at line %d char %d: +%.3fs total %.3fs.\n"
              stage
              !lineno
              !charno
              (now -. !unchecked_timing_last)
              (now -. unchecked_timing_start);
            unchecked_timing_last := now;
            flush stdout
          end
      in
      let unchecked_finish target_proof target =
        if !vampireabyqualifying then
          begin
            unchecked_timing "disabled_by_qualifying_mode";
            None
          end
        else if not unchecked_final then None
        else
          let _ = unchecked_timing "conv:start" in
          match conv target claimtm proof_delta [] with
          | Some _ ->
              unchecked_timing "conv:done";
              let live_symbol_table =
                match source_map with
                | None -> Hashtbl.copy sigtmof
                | Some source_map ->
                    vampire_source_context_symbol_table_with_source_map source_map
              in
              let returned_body_expander tm =
                vampire_live_basis_tm_expander
                  (vampire_expand_returned_tm cxtm source_map tm)
              in
              let live_extra_delta =
                match extra_delta, extra_symbols with
                | Some extra_delta, Some extra_symbols ->
                    Some
                      (vampire_live_safe_extra_delta
                         ~body_expander:returned_body_expander
                         live_symbol_table
                         extra_symbols
                         extra_delta)
                | Some extra_delta, None -> Some extra_delta
                | None, _ -> None
              in
              unchecked_timing "expand_returned:start";
              let compact_delta =
                Sys.getenv_opt "MEGALODON_CERT_COMPACT_QED_DELTA" <> Some "0"
                && not !vampireabyqualifying
              in
              let expanded =
                if compact_delta then
                  begin
                    begin match live_extra_delta, extra_symbols with
                    | Some live_extra_delta, Some extra_symbols ->
                        vampire_register_reconstruction_delta_for_qed
                          extra_symbols
                          live_extra_delta
                    | _ -> ()
                    end;
                    vampire_expand_returned_proof cxtm source_map target_proof
                  end
                else
                  vampire_expand_returned_proof
                    ?extra_delta:live_extra_delta
                    cxtm
                    source_map
                    target_proof
              in
              unchecked_timing "expand_returned:done";
              unchecked_timing "live_basis:start";
              let expanded =
                vampire_live_basis_expander expanded
              in
              unchecked_timing "live_basis:done";
              unchecked_timing "prop_ext:start";
              let candidate =
                vampire_loaded_prop_ext_expander
                  (vampire_directional_prop_ext_expander expanded)
              in
              unchecked_timing "prop_ext:done";
              let certificate_only_unsafe_prop_symbol =
                match extra_symbols with
                | None -> None
                  | Some extra_symbols ->
                    vampire_certificate_only_unsafe_prop_symbol_in_proof
                      ?extra_delta:live_extra_delta
                      live_symbol_table
                      extra_symbols
                      candidate
              in
              begin match certificate_only_unsafe_prop_symbol with
              | Some symbol ->
                  unchecked_timing "certificate_only_unsafe_prop_reject";
                  if Sys.getenv_opt "MEGALODON_CERT_DEBUG_SOURCE_APPLY" = Some "1" then
                    begin
                      let detail =
                        match extra_symbols with
                        | None -> symbol
                        | Some extra_symbols ->
                            let empty_extra_delta = Hashtbl.create 1 in
                            let certificate_delta =
                              match live_extra_delta with
                              | Some live_extra_delta -> live_extra_delta
                              | None -> empty_extra_delta
                            in
                            match
                              vampire_debug_certificate_only_symbol_in_proof
                                live_symbol_table
                                certificate_delta
                                extra_symbols
                                candidate
                            with
                            | Some detail -> detail
                            | None -> symbol
                      in
                      Printf.printf
                        "Vampire native supplied-refutation unchecked finish rejected unsafe proposition certificate-local candidate at line %d char %d: %s\n"
                        !lineno
                        !charno
                        detail;
                      flush stdout
                    end;
                  None
              | None ->
                  unchecked_timing "local_check:start";
                  let local_cx =
                    List.map (fun (_, (tp, _)) -> tp) cxtm
                  in
                  let local_hyps = List.map snd cxpf in
                  begin
                    try
                      match
                        check_propofpf
                          sigdelta
                          sigtmof
                          local_cx
                          local_hyps
                          candidate
                          claimtm
                          []
                      with
                      | Some _ ->
                          unchecked_timing "local_check:done";
                          Some candidate
                      | None ->
                          unchecked_timing "local_check:none";
                          if Sys.getenv_opt "MEGALODON_CERT_DEBUG_SOURCE_APPLY" = Some "1" then
                            begin
                              Printf.printf
                                "Vampire native supplied-refutation unchecked finish candidate did not check locally at line %d char %d.\n"
                                !lineno
                                !charno;
                              flush stdout
                            end;
                          None
                    with exn ->
                      unchecked_timing "local_check:failure";
                      if Sys.getenv_opt "MEGALODON_CERT_DEBUG_SOURCE_APPLY" = Some "1" then
                        begin
                          Printf.printf
                            "Vampire native supplied-refutation unchecked finish candidate failed local checking at line %d char %d: %s.\n"
                            !lineno
                            !charno
                            (Printexc.to_string exn);
                          flush stdout
                        end;
                      None
                  end
              end
          | None ->
              unchecked_timing "conv:none";
              None
      in
      let unchecked_double_negation_candidate target dnotnot =
        Some
          (PPfAp
             (PTmAp (Known Vampire_cert_v1.native_core_dneg_hash, target),
              dnotnot))
      in
      let rec prepare_double_negation_proof target proof proposition =
        match proposition with
        | All (Prop, body) ->
            let tm = vampire_native_core_false_tm in
            let body = tmsubst body 0 tm in
            begin match vampire_double_negation_target body with
            | Some body_target ->
                begin match conv body_target target proof_delta [] with
                | Some _ ->
                    prepare_double_negation_proof
                      target
                      (PTmAp (proof, tm))
                      body
                | None -> (proof, proposition)
                end
            | None -> (proof, proposition)
            end
        | _ -> (proof, proposition)
      in
      let rec try_proposition depth preferred_prop_terms proof proposition =
        let debug_timing =
          Sys.getenv_opt "MEGALODON_CERT_DEBUG_TIMING" = Some "1"
        in
        let timing_start = Unix.gettimeofday () in
        let timing_last = ref timing_start in
        let timing stage =
          if debug_timing then
            begin
              let now = Unix.gettimeofday () in
              Printf.printf
                "Vampire native supplied-refutation timing %s at line %d char %d depth=%d: +%.3fs total %.3fs.\n"
                stage
                !lineno
                !charno
                depth
                (now -. !timing_last)
                (now -. timing_start);
              timing_last := now;
              flush stdout
            end
        in
        if Sys.getenv_opt "MEGALODON_CERT_DEBUG_SUPPLIED" = Some "1" then
          begin
            Printf.printf
              "Vampire native supplied-refutation search depth=%d target=%s proposition=%s\n"
              depth
              (tm_to_str source_target)
              (tm_to_str proposition);
            flush stdout
          end;
        timing "native_refutation:start";
        match
          vampire_xm_native_refutation_elim_to
            ?source_map
            ?extra_delta
            ?extra_symbols
            source_target
            cxtm
            cxpf
            proof
            proposition
        with
        | Some source_target_proof ->
            timing "native_refutation:success";
            finish source_target_proof source_target
        | None ->
            timing "native_refutation:none";
            timing "cps:start";
            begin match
              vampire_xm_cps_elim_to
                ?source_map
                ?extra_delta
                ?extra_symbols
                source_target
                cxtm
                cxpf
                proof
                proposition
            with
            | Some source_target_proof ->
                timing "cps:success";
                finish source_target_proof source_target
            | None ->
                timing "cps:none";
                let rec try_quantified () =
                  if depth <= 0 then None
                  else
                    begin match proposition with
                    | All (tp, body) ->
                        let terms =
                      match tp with
                      | Prop ->
                          vampire_ordered_unique
                            (preferred_prop_terms
                             @ vampire_ordered_context_terms_of_type cxtm Prop
                                 @ [claimtm;
                                    source_target;
                                    TmH (!fal);
                                    vampire_native_core_false_tm])
                          | _ -> vampire_context_terms_with_default cxtm tp
                        in
                        let rec try_terms = function
                        | [] -> None
                        | tm :: rest ->
                            let next_preferred_prop_terms =
                              match tp with
                              | Prop -> remove_term tm preferred_prop_terms
                              | _ -> preferred_prop_terms
                            in
                            begin match
                              try_proposition
                                (depth - 1)
                                next_preferred_prop_terms
                                (PTmAp (proof, tm))
                                (tmsubst body 0 tm)
                            with
                              | Some _ as result -> result
                              | None -> try_terms rest
                              end
                        in
                        try_terms terms
                    | _ -> None
                    end
                in
                timing "double_negation_target:start";
                let double_negation_target =
                  vampire_double_negation_target proposition
                in
                timing "double_negation_target:done";
                begin match double_negation_target with
                | Some target ->
                    timing "double_negation_conv:start";
                    let target_matches =
                      conv target source_target proof_delta []
                    in
                    timing "double_negation_conv:done";
                    begin match target_matches with
                    | Some _ ->
                        timing "double_negation_prepare:start";
                        let proof, target =
                          let proof, proposition =
                            prepare_double_negation_proof target proof proposition
                          in
                          if Sys.getenv_opt "MEGALODON_CERT_DEBUG_SUPPLIED" = Some "1" then
                            begin
                              Printf.printf
                                "Vampire native supplied-refutation prepared double-negation target=%s proposition=%s\n"
                                (tm_to_str target)
                                (tm_to_str proposition);
                              flush stdout
                            end;
                          match vampire_double_negation_target proposition with
                          | Some prepared_target -> (proof, prepared_target)
                          | None -> (proof, target)
                        in
                        timing "double_negation_prepare:done";
                        begin match
                          unchecked_double_negation_candidate target proof
                        with
                        | Some target_proof ->
                            begin match unchecked_finish target_proof target with
                            | Some _ as result ->
                                timing "double_negation_unchecked_candidate:return";
                                result
                            | None ->
                                timing "double_negation_unchecked_candidate:skip";
                                None
                            end
                        | None ->
                            timing "double_negation_unchecked_candidate:none";
                            None
                        end
                        |> (function
                              | Some _ as result -> result
                              | None ->
                        timing "double_negation_elim:start";
                        begin match
                          vampire_xm_double_negation_elim_to
                            ?source_map
                            ?extra_delta
                            ?extra_symbols
                            target
                            cxtm
                            cxpf
                            proof
                        with
                        | Some target_proof ->
                            timing "double_negation_elim:success";
                            finish target_proof target
                        | None -> None
                        end
                           )
                    | None -> try_quantified ()
                    end
                | None -> try_quantified ()
                end
            end
      in
      try_proposition 6 initial_preferred_prop_terms proof proposition

let vampire_instantiate_source_binding binding tm =
  {
    binding with
    Vampire_cert_v1.core_native_source_proposition =
      tmsubst binding.Vampire_cert_v1.core_native_source_proposition 0 tm;
  }

let vampire_instantiate_source_binding_if_quantified binding tp tm =
  match binding.Vampire_cert_v1.core_native_source_proposition with
  | All (binding_tp, body) when binding_tp = tp ->
      {
        binding with
        Vampire_cert_v1.core_native_source_proposition =
          tmsubst body 0 tm;
      }
  | _ -> binding

let vampire_source_binding_is_negated_conjecture binding =
  binding.Vampire_cert_v1.core_native_certificate_source_kind = "negated_conjecture"
  || binding.Vampire_cert_v1.core_native_source_map_kind = "negated_conjecture"
  || binding.Vampire_cert_v1.core_native_source_map_kind = "conjecture"

let vampire_definition_transport_proofs source_audit expected actual actual_proof =
  let debug = Sys.getenv_opt "MEGALODON_CERT_DEBUG" = Some "1" in
  let shifted_actual = tmshift 0 1 actual in
  let transport_from_definition definition_prop definition_proof =
    match definition_prop with
    | All (Ar (tp_left, Ar (tp_right, Prop)),
           Imp (Ap (Ap (DB 0, left), right),
                Ap (Ap (DB 0, right_again), left_again)))
        when tp_left = tp_right
             && left = left_again
             && right = right_again ->
        if shifted_actual = right then
          let motive = Lam (tp_left, Lam (tp_left, DB 0)) in
          if debug then
            prerr_endline
              ("source-context local definition transport right-to-left expected="
               ^ tm_to_str expected
               ^ " actual="
               ^ tm_to_str actual);
          [PPfAp (PTmAp (definition_proof, motive), actual_proof)]
        else if shifted_actual = left then
          let motive = Lam (tp_left, Lam (tp_left, DB 1)) in
          if debug then
            prerr_endline
              ("source-context local definition transport left-to-right expected="
               ^ tm_to_str expected
               ^ " actual="
               ^ tm_to_str actual);
          [PPfAp (PTmAp (definition_proof, motive), actual_proof)]
        else
          []
    | _ -> []
  in
  source_audit.Vampire_source_context.resolved
  |> List.concat_map
       (function
         | _, Vampire_source_context.Definitional (definition_prop, definition_proof) ->
             transport_from_definition definition_prop definition_proof
         | _ -> [])

let vampire_take n xs =
  let rec take i acc = function
    | _ when i <= 0 -> List.rev acc
    | [] -> List.rev acc
    | x :: rest -> take (i - 1) (x :: acc) rest
  in
  take n [] xs

let vampire_instantiated_refutation_candidates ?source_map ?extra_symbols ?(candidate_props=[]) cxtm proof proposition source_bindings =
  let terms_for_type tp =
    match tp, source_map with
    | Prop, _ -> vampire_context_terms_of_type cxtm tp
    | _, None -> vampire_context_terms_of_type cxtm tp
    | _, Some source_map ->
        let local_terms =
          vampire_ordered_unique
            (vampire_source_map_local_terms_of_type cxtm source_map tp
             @ vampire_context_terms_of_type cxtm tp)
        in
        if local_terms <> [] then local_terms
        else []
  in
  let rec collect depth proof proposition source_bindings =
    let current = [(proof,proposition,source_bindings)] in
    if depth <= 0 then current
    else
      match proposition with
      | All(tp,body) ->
          current @
          List.concat
            (List.map
               (fun tm ->
                  collect
                    (depth - 1)
                    (PTmAp(proof,tm))
                    (tmsubst body 0 tm)
                    (List.map
                       (fun binding ->
                          vampire_instantiate_source_binding_if_quantified binding tp tm)
                       source_bindings))
               (terms_for_type tp))
      | _ -> current
  in
  collect 8 proof proposition source_bindings

let vampire_negated_conjecture_target binding =
  let rec prenex_negation_target = function
    | Imp(target,false_tm) when vampire_false_like false_tm -> Some target
    | All(tp,body) ->
        begin match prenex_negation_target body with
        | Some target ->
            if free_in_tm_p target 0 then Some (All(tp,target))
            else Some (tmshift 0 (-1) target)
        | None -> None
        end
    | native_negation -> vampire_native_negation_target native_negation
  in
  if vampire_source_binding_is_negated_conjecture binding then
    prenex_negation_target binding.Vampire_cert_v1.core_native_source_proposition
  else None

let vampire_guided_negated_conjecture_reconstruction
    ?source_map
    ?extra_delta
    ?extra_symbols
    ?(unchecked_final=false)
    claimtm
    cxtm
    cxpf
    proof
    proposition
    binding =
  let proof_delta =
    match source_map with
    | None -> vampire_source_context_delta_with_locals cxtm
    | Some source_map ->
        vampire_source_context_delta_with_source_map ~cxtm source_map
  in
  begin match extra_delta with
  | None -> ()
  | Some extra_delta ->
      vampire_merge_reconstruction_delta proof_delta extra_delta
  end;
  let debug = Sys.getenv_opt "MEGALODON_CERT_DEBUG_GUIDED" = Some "1" in
  let debug_focus =
    Sys.getenv_opt "MEGALODON_CERT_DEBUG_GUIDED_FOCUS" = Some "1"
  in
  let guided_supplied_refutation_attempt_limit =
    match Sys.getenv_opt "MEGALODON_CERT_GUIDED_SUPPLIED_REFUTATION_LIMIT" with
    | Some value ->
        begin
          try int_of_string value with Failure _ -> 8
        end
    | None -> 8
  in
  let guided_supplied_refutation_attempts = ref 0 in
  let guided_depth_limit =
    match Sys.getenv_opt "MEGALODON_CERT_GUIDED_DEPTH_LIMIT" with
    | Some value ->
        begin
          try int_of_string value with Failure _ -> 3
        end
    | None -> 3
  in
  let guided_limit_exhausted () =
    guided_supplied_refutation_attempt_limit >= 0
    && !guided_supplied_refutation_attempts >= guided_supplied_refutation_attempt_limit
  in
  let try_supplied_refutation
      ?(preferred_prop_terms=[])
      source_target
      proof
      proposition =
    if guided_limit_exhausted () then
      begin
        if debug then
          begin
            Printf.printf
              "Vampire native guided negated-conjecture supplied-refutation attempt limit reached at line %d char %d.\n"
              !lineno
              !charno;
            flush stdout
          end;
        None
      end
    else
      begin
        incr guided_supplied_refutation_attempts;
        vampire_reconstruct_goal_from_supplied_refutation
          ?source_map
          ?extra_delta
          ?extra_symbols
          ~preferred_prop_terms
          ~unchecked_final
          claimtm
          cxtm
          cxpf
          source_target
          proof
          proposition
      end
  in
  let target_matches_goal target =
    match conv target claimtm proof_delta [] with
    | Some _ -> true
    | None -> false
  in
  let proposition_ready_for_target target proposition =
    let convertible left right =
      match conv left right proof_delta [] with
      | Some _ -> true
      | None -> false
    in
    match vampire_native_refutation_target proposition with
    | Some native_target when convertible native_target target -> true
    | _ ->
        begin match vampire_cps_target proposition with
        | Some cps_target when convertible cps_target target -> true
        | _ ->
            begin match vampire_double_negation_target proposition with
            | Some dneg_target when convertible dneg_target target -> true
            | _ -> false
            end
        end
  in
  let remove_term tm terms =
    List.filter (fun candidate -> candidate <> tm) terms
  in
  let local_prefix = vampire_ordered_local_terms_of_type cxtm Prop in
  let rec try_guided_proposition_suffix
      source_target
      preferred_locals
      proof
      proposition =
    begin match
      try_supplied_refutation
        ~preferred_prop_terms:preferred_locals
        source_target
        proof
        proposition
    with
    | Some _ as result -> result
    | None ->
        begin match preferred_locals, proposition with
        | tm :: rest, All (_, body) ->
            let next_proposition = tmsubst body 0 tm in
            let next_proof = PTmAp (proof, tm) in
            if debug then
              begin
                Printf.printf
                  "Vampire native guided proposition suffix applying %s; ready=%s.\n"
                  (tm_to_str tm)
                  (if proposition_ready_for_target source_target next_proposition then "yes" else "no");
                flush stdout
              end;
            begin match
              if proposition_ready_for_target source_target next_proposition then
                try_supplied_refutation
                  source_target
                  next_proof
                  next_proposition
              else None
            with
            | Some _ as result -> result
            | None ->
                try_guided_proposition_suffix
                  source_target
                  rest
                  next_proof
                  next_proposition
            end
        | _ -> None
        end
    end
  in
  if Sys.getenv_opt "MEGALODON_CERT_DEBUG_GUIDED_PREFIX" = Some "1" then
    begin
      let rec apply_prefix proof proposition binding = function
        | [] -> ()
        | tm :: rest ->
            let proof = PTmAp (proof, tm) in
            let binding, proposition =
              match proposition with
              | All (tp, body) ->
                  (vampire_instantiate_source_binding_if_quantified binding tp tm,
                   tmsubst body 0 tm)
              | _ -> (binding, proposition)
            in
            let target_info =
              match vampire_negated_conjecture_target binding with
              | Some target ->
                  Printf.sprintf
                    "target=%s target_matches_goal=%s proposition_ready=%s"
                    (tm_to_str target)
                    (if target_matches_goal target then "yes" else "no")
                    (if proposition_ready_for_target target proposition then "yes" else "no")
              | None -> "target=<none>"
            in
            Printf.printf
              "Vampire native guided prefix applied %s: %s proposition=%s\n"
              (tm_to_str tm)
              target_info
              (tm_to_str proposition);
            flush stdout;
            begin match vampire_negated_conjecture_target binding with
            | Some target when target_matches_goal target ->
                let rec apply_suffix proposition = function
                  | [] -> ()
                  | suffix_tm :: suffix_rest ->
                      let proposition =
                        match proposition with
                        | All (_, body) -> tmsubst body 0 suffix_tm
                        | _ -> proposition
                      in
                      Printf.printf
                        "Vampire native guided proposition suffix applied %s: proposition_ready=%s proposition=%s\n"
                        (tm_to_str suffix_tm)
                        (if proposition_ready_for_target target proposition then "yes" else "no")
                        (tm_to_str proposition);
                      flush stdout;
                      apply_suffix proposition suffix_rest
                in
                apply_suffix proposition rest
            | _ -> ()
            end;
            apply_prefix proof proposition binding rest
      in
      apply_prefix proof proposition binding local_prefix
    end;
  let rec try_state depth preferred_locals proof proposition binding =
    let try_quantified matched_target_terms =
      if depth <= 0 then None
      else
        begin match proposition with
        | All (tp, body) ->
            let terms =
              match tp with
              | Prop ->
                  vampire_ordered_unique
                    (preferred_locals
                     @ matched_target_terms
                     @ [TmH (!fal); vampire_native_core_false_tm; claimtm])
              | _ -> vampire_ordered_context_terms_with_default cxtm tp
            in
            let rec try_terms = function
              | [] -> None
              | tm :: rest ->
                  let next_binding =
                    vampire_instantiate_source_binding_if_quantified binding tp tm
                  in
                  let next_preferred_locals =
                    match tp with
                    | Prop -> remove_term tm preferred_locals
                    | _ -> preferred_locals
                  in
                  if debug then
                    begin
                      Printf.printf
                        "Vampire native guided negated-conjecture instantiating depth %d with %s.\n"
                        depth
                        (tm_to_str tm);
                      flush stdout
                    end;
                  if debug_focus then
                    begin match vampire_negated_conjecture_target next_binding with
                    | Some source_target when target_matches_goal source_target ->
                        let next_proposition = tmsubst body 0 tm in
                        let interesting =
                          List.exists
                            (fun candidate ->
                               match conv tm candidate proof_delta [] with
                               | Some _ -> true
                               | None -> false)
                            (source_target :: claimtm :: matched_target_terms
                             @ [TmH (!fal); vampire_native_core_false_tm])
                        in
                        if interesting then
                          begin
                            Printf.printf
                              "Vampire native guided focus instantiation depth=%d term=%s ready=%s proposition=%s\n"
                              depth
                              (tm_to_str tm)
                              (if proposition_ready_for_target
                                    source_target
                                    next_proposition
                               then "yes"
                               else "no")
                              (tm_to_str next_proposition);
                            flush stdout
                          end
                    | _ -> ()
                    end;
                  begin match
                    try_state
                      (depth - 1)
                      next_preferred_locals
                      (PTmAp (proof, tm))
                      (tmsubst body 0 tm)
                      next_binding
                  with
                  | Some _ as result -> result
                  | None -> try_terms rest
                  end
            in
            try_terms terms
        | _ -> None
        end
    in
    begin match vampire_negated_conjecture_target binding with
    | Some source_target
        when target_matches_goal source_target
             && proposition_ready_for_target source_target proposition ->
        if debug then
          begin
            Printf.printf
              "Vampire native guided negated-conjecture target matched current goal at depth %d.\ntarget: %s\nproposition: %s\n"
              depth
              (tm_to_str source_target)
              (tm_to_str proposition);
            flush stdout
          end;
        try_supplied_refutation
          source_target
          proof
          proposition
    | Some source_target when target_matches_goal source_target ->
        begin match
          try_guided_proposition_suffix
            source_target
            preferred_locals
            proof
            proposition
        with
        | Some _ as result -> result
        | None -> try_quantified [source_target; claimtm]
        end
    | _ ->
        try_quantified []
    end
  in
  try_state guided_depth_limit local_prefix proof proposition binding

let vampire_reconstruct_final_conjecture_from_native_core source_map source_proofs native_core =
  match
    vampire_remaining_source_bindings_for_proofs
      source_proofs
      native_core.Vampire_cert_v1.core_native_source_assumption_bindings
  with
  | [binding] ->
      begin match vampire_negated_conjecture_target binding with
      | Some target ->
            vampire_reconstruct_current_goal_from_refutation
              ~source_map
              ~extra_delta:native_core.Vampire_cert_v1.core_native_delta_table
              ~extra_symbols:native_core.Vampire_cert_v1.core_native_symbol_table
              target
              []
              []
            native_core.Vampire_cert_v1.core_native_proof
            native_core.Vampire_cert_v1.core_native_proposition
      | None -> None
      end
  | _ -> None

let vampire_source_application_proofs cxtm cxpf source_map expected source_proofs =
  let cx =
    List.filter_map
      (fun (_, (tp, definition)) ->
         match definition with
         | None -> Some tp
         | Some _ -> None)
      cxtm
  in
  let hyps = List.map snd cxpf in
  let proof_delta = vampire_source_context_delta_with_source_map ~cxtm source_map in
  let symbol_table = vampire_source_context_symbol_table_with_source_map source_map in
  let debug = Sys.getenv_opt "MEGALODON_CERT_DEBUG" = Some "1" in
  let debug_source_apply = Sys.getenv_opt "MEGALODON_CERT_DEBUG_SOURCE_APPLY" = Some "1" in
  if debug_source_apply then
    begin
      Printf.printf
        "Vampire native source application expected at line %d char %d: %s\n"
        !lineno
        !charno
        (tm_to_str expected);
      List.iteri
        (fun index tp ->
           Printf.printf
             "Vampire native source application cxtm[%d]: %s\n"
             index
             (tp_to_str tp))
        cx;
      List.iteri
        (fun index prop ->
           Printf.printf
             "Vampire native source application cxpf[%d]: %s\n"
             index
             (tm_to_str prop))
        hyps;
      flush stdout
    end;
  List.filter
    (fun source_proof ->
       try
         let (actual, dl) = extr_propofpf proof_delta symbol_table cx hyps source_proof [] in
         match conv actual expected proof_delta dl with
         | Some _ -> true
         | None ->
             if debug || debug_source_apply then
               begin
                 Printf.printf
                   "Vampire native source proof candidate rejected at line %d char %d: expected %s actual %s.\n"
                   !lineno
                   !charno
                   (tm_to_str expected)
                   (tm_to_str actual);
                 if debug_source_apply then
                   Printf.printf
                     "Vampire native source proof candidate term: %s\n"
                     (pf_to_str source_proof);
                 flush stdout
               end;
             false
       with Failure msg ->
         if debug then
           begin
             Printf.printf
               "Vampire native source proof candidate ill-formed at line %d char %d: %s.\n"
               !lineno
               !charno
               msg;
             flush stdout
           end;
         false
       | _ -> false)
    source_proofs

let vampire_apply_available_source_bindings ?extra_delta ?extra_symbols cxtm cxpf source_map source_audit proof proposition bindings =
  let debug_source_apply = Sys.getenv_opt "MEGALODON_CERT_DEBUG_SOURCE_APPLY" = Some "1" in
  let rec apply proof proposition remaining =
    if debug_source_apply then
      begin
        Printf.printf
          "Vampire native apply source bindings state at line %d char %d: remaining=%d proposition=%s\n"
          !lineno
          !charno
          (List.length remaining)
          (tm_to_str proposition);
        flush stdout
      end;
    match remaining with
    | [] -> [(proof,proposition,[])]
    | binding :: rest ->
        let skipped =
          List.map
            (fun (proof, proposition, remaining) ->
               (proof, proposition, binding :: remaining))
            (apply proof proposition rest)
        in
        let applied =
          match vampire_source_proof source_audit binding.Vampire_cert_v1.core_native_source_step,
                proposition
          with
          | Some source_proof, Imp(expected_prop,target_prop) ->
              let actual_prop = binding.Vampire_cert_v1.core_native_source_proposition in
              if debug_source_apply then
                begin
                  Printf.printf
                    "Vampire native considering source binding %s kind=%s expected=%s actual=%s target=%s\n"
                    binding.Vampire_cert_v1.core_native_source_step
                    binding.Vampire_cert_v1.core_native_source_map_kind
                    (tm_to_str expected_prop)
                    (tm_to_str actual_prop)
                    (tm_to_str target_prop);
                  flush stdout
                end;
              let transport_proofs =
                vampire_definition_transport_proofs
                  source_audit
                  expected_prop
                  actual_prop
                  source_proof
              in
              let source_proofs =
                if expected_prop = actual_prop then source_proof :: transport_proofs
                else transport_proofs @ [source_proof]
              in
              List.concat
                (List.map
                   (fun source_proof ->
                      let next_proof = PPfAp(proof,source_proof) in
                      match
                        vampire_actual_prop_of_proof
                          ~source_map
                          ?extra_delta
                          ?extra_symbols
                          cxtm
                          cxpf
                          next_proof
                      with
                      | Some actual_target_prop ->
                          apply next_proof actual_target_prop rest
                      | None -> [])
                  (vampire_source_application_proofs
                     cxtm
                      cxpf
                      source_map
                      expected_prop
                      source_proofs))
          | Some _, _ ->
              if debug_source_apply then
                begin
                  Printf.printf
                    "Vampire native cannot apply source binding %s because current proposition is not an implication: %s\n"
                    binding.Vampire_cert_v1.core_native_source_step
                    (tm_to_str proposition);
                  flush stdout
                end;
              []
          | None, _ ->
              if debug_source_apply then
                begin
                  Printf.printf
                    "Vampire native has no source proof for binding %s kind=%s.\n"
                    binding.Vampire_cert_v1.core_native_source_step
                    binding.Vampire_cert_v1.core_native_source_map_kind;
                  flush stdout
                end;
              []
        in
        applied @ skipped
  in
  apply proof proposition bindings

let vampire_source_proof_props ?extra_symbols cxtm cxpf source_map source_audit =
  let cx =
    List.filter_map
      (fun (_, (tp, definition)) ->
         match definition with
         | None -> Some tp
         | Some _ -> None)
      cxtm
  in
  let hyps = List.map snd cxpf in
  let proof_delta = vampire_source_context_delta_with_source_map ~cxtm source_map in
  let symbol_table = vampire_symbol_table ?extra_symbols source_map in
  let prop_of_proof proof =
    let rec try_variants = function
      | [] -> None
      | proof :: rest ->
          try
            let (prop, _) =
              extr_propofpf proof_delta symbol_table cx hyps proof []
            in
            Some (proof, prop)
          with _ -> try_variants rest
    in
    try_variants (vampire_prop_ext_variants ~delta:proof_delta proof)
  in
  let add_unique proof_prop proof_props =
    if List.exists (fun existing -> existing = proof_prop) proof_props then
      proof_props
    else
      proof_prop :: proof_props
  in
  let audit_proofs =
    List.filter_map
      (fun (_, proof) -> prop_of_proof proof)
      source_audit.Vampire_source_context.source_proofs
  in
  let known_hash_candidates entry =
    let add hash hashes =
      if hash = "" || List.mem hash hashes then hashes else hash :: hashes
    in
    let add_name name hashes =
      if name = "" then hashes
      else
        match Hashtbl.find_opt sigknh name with
        | Some hash -> add hash hashes
        | None -> hashes
    in
    []
    |> add entry.Vampire_cert_v1.source_map_hash
    |> add_name entry.Vampire_cert_v1.source_map_source_name
    |> add_name entry.Vampire_cert_v1.source_map_tptp_name
    |> List.rev
  in
  let source_map_known_proofs =
    source_map
    |> List.filter
         (fun entry ->
            entry.Vampire_cert_v1.source_map_kind = "known"
            || entry.Vampire_cert_v1.source_map_kind = "axiom")
    |> List.filter_map
         (fun entry ->
            known_hash_candidates entry
            |> List.find_map (fun hash -> prop_of_proof (Known hash)))
  in
  List.rev
    (List.fold_left
       (fun proof_props proof_prop -> add_unique proof_prop proof_props)
       []
       (audit_proofs @ source_map_known_proofs))

let vampire_reconstruct_goal_from_source_audit
    ?extra_delta
    ?extra_symbols
    claimtm
    cxtm
    cxpf
    source_map
    source_audit =
  let source_proofs =
    vampire_source_proof_props ?extra_symbols cxtm cxpf source_map source_audit
  in
  let source_props = claimtm :: List.map snd source_proofs in
  let term_candidates tp =
    match tp with
    | Prop ->
        vampire_candidate_terms_from_props ?extra_symbols cxtm source_map source_props tp
    | _ ->
        let local_terms =
          vampire_ordered_unique
            (vampire_source_map_local_terms_of_type cxtm source_map tp
             @ vampire_context_terms_of_type cxtm tp)
        in
        if local_terms <> [] then local_terms
        else vampire_candidate_terms_from_props ?extra_symbols cxtm source_map source_props tp
  in
  let source_proofs_for expected =
    source_proofs
    |> List.filter_map
         (fun (proof, _) ->
            vampire_check_proof_of_prop
              ?source_map:(Some source_map)
              ?extra_delta
              ?extra_symbols
              cxtm
              cxpf
              expected
              proof)
  in
  let rec try_proof depth proof proposition =
    match
      vampire_check_current_goal_proof
        ?source_map:(Some source_map)
        ?extra_delta
        ?extra_symbols
        claimtm
        cxtm
        cxpf
        proof
    with
    | Some _ as result -> result
    | None ->
        begin match
          vampire_reconstruct_goal_from_proved_prop
            ~source_map
            ?extra_delta
            ?extra_symbols
            claimtm
            cxtm
            cxpf
            proof
            proposition
        with
        | Some _ as result -> result
        | None ->
        if depth <= 0 then None
        else
          begin match proposition with
          | All (tp, body) ->
              let rec try_terms = function
                | [] -> None
                | tm :: rest ->
                    begin match
                      try_proof
                        (depth - 1)
                        (PTmAp (proof, tm))
                        (tmsubst body 0 tm)
                    with
                    | Some _ as result -> result
                    | None -> try_terms rest
                    end
              in
              try_terms (term_candidates tp)
          | Imp (expected, target) ->
              let rec try_source_proofs = function
                | [] -> None
                | source_proof :: rest ->
                    begin match
                      try_proof
                        (depth - 1)
                        (PPfAp (proof, source_proof))
                        target
                    with
                    | Some _ as result -> result
                    | None -> try_source_proofs rest
                    end
              in
              try_source_proofs (source_proofs_for expected)
          | _ -> None
          end
        end
  in
  let rec try_sources = function
    | [] -> None
    | (proof, proposition) :: rest ->
        begin match try_proof 12 proof proposition with
        | Some _ as result -> result
        | None -> try_sources rest
        end
  in
  let result = try_sources source_proofs in
  let result =
    match result with
    | Some _ as result -> result
    | None ->
        if !vampireabyqualifying then None
        else
          vampire_constructive_goal_search
            ~source_map
            ?extra_delta
            ?extra_symbols
            ~external_proofs:source_proofs
            claimtm
            cxtm
            cxpf
  in
  if result = None && Sys.getenv_opt "MEGALODON_CERT_DEBUG" = Some "1" then
    begin
      Printf.printf
        "Vampire native source-context direct goal reconstruction did not find a proof.\n";
      flush stdout
    end;
  result

let vampire_certificate_reconstruct_aby_goal claimtm cxtm cxpf cert source_map source_audit =
  let debug_timing = Sys.getenv_opt "MEGALODON_CERT_DEBUG_TIMING" = Some "1" in
  let timing_start = Unix.gettimeofday () in
  let timing_last = ref timing_start in
  let timing stage =
    if debug_timing then
      begin
        let now = Unix.gettimeofday () in
        Printf.printf
          "Vampire native reconstruct-goal timing %s at line %d char %d: +%.3fs total %.3fs.\n"
          stage
          !lineno
          !charno
          (now -. !timing_last)
          (now -. timing_start);
        timing_last := now;
        flush stdout
      end
  in
  let source_proofs_for_core = vampire_core_source_proofs source_audit in
  let external_definition_names =
    vampire_source_context_external_definition_names cxtm source_map
  in
  timing "elaborate_preprocess_refutation_native:start";
  let native_core =
    Vampire_cert_v1.elaborate_preprocess_refutation_native
      ~source_map
      ~source_proofs:source_proofs_for_core
      ~external_hypotheses:
        (vampire_core_external_hypotheses cert cxtm source_map source_audit cxpf)
      ~external_delta_table:
        (vampire_source_context_delta_with_source_map ~cxtm source_map)
      ~external_symbol_table:
        (vampire_source_context_symbol_table_with_source_map source_map)
      ~external_definition_names
      cert
  in
  timing "elaborate_preprocess_refutation_native:done";
  let reconstruction_delta =
    Hashtbl.copy native_core.Vampire_cert_v1.core_native_delta_table
  in
  timing "reconstruction_delta:start";
  vampire_add_audited_definition_delta
    native_core.Vampire_cert_v1.core_native_source_bindings
    source_audit
    reconstruction_delta;
  timing "reconstruction_delta:done";
  timing "remaining_bindings:start";
  let remaining_bindings =
    vampire_remaining_source_bindings_for_proofs
      source_proofs_for_core
      native_core.Vampire_cert_v1.core_native_source_assumption_bindings
  in
  timing "remaining_bindings:done";
  let expand_returned_tm =
    vampire_expand_returned_tm
      ~extra_delta:reconstruction_delta
      cxtm
      (Some source_map)
  in
  timing "core_actual_prop:start";
  let core_proposition =
    match
      vampire_actual_prop_of_proof
        ~source_map
        ~extra_delta:native_core.Vampire_cert_v1.core_native_delta_table
        ~extra_symbols:native_core.Vampire_cert_v1.core_native_symbol_table
        cxtm
        cxpf
        native_core.Vampire_cert_v1.core_native_proof
    with
    | Some actual -> actual
    | None -> expand_returned_tm native_core.Vampire_cert_v1.core_native_proposition
  in
  timing "core_actual_prop:done";
  timing "remaining_bindings_expand:start";
  let remaining_bindings =
    List.map
      (fun binding ->
         {
           binding with
           Vampire_cert_v1.core_native_source_proposition =
             expand_returned_tm
               binding.Vampire_cert_v1.core_native_source_proposition;
         })
      remaining_bindings
  in
  timing "remaining_bindings_expand:done";
  if Sys.getenv_opt "MEGALODON_CERT_DEBUG" = Some "1" then
    begin
      Printf.printf
        "Vampire native core proposition after source composition: %s\n"
        (tm_to_str core_proposition);
      Printf.printf
        "Vampire native core actual proof proposition: %s\n"
        (tm_to_str core_proposition);
      flush stdout
    end;
  List.iter
    (vampire_debug_source_binding "Vampire native core source")
    native_core.Vampire_cert_v1.core_native_source_bindings;
  List.iter
    (vampire_debug_source_binding "Vampire native remaining source")
    remaining_bindings;
  let pure_prop_schema_goal = vampire_pure_prop_schema_context cxtm cxpf in
  let reconstruct_pure_prop_schema () =
    if pure_prop_schema_goal
       && not !vampireabyqualifying
       && Sys.getenv_opt "MEGALODON_CERT_DISABLE_PURE_PROP_SHORTCUT" <> Some "1" then
      begin
        timing "pure_prop_constructive:start";
        let result =
          vampire_constructive_goal_search
            ~source_map
            ~extra_delta:reconstruction_delta
            ~extra_symbols:native_core.Vampire_cert_v1.core_native_symbol_table
            claimtm
            cxtm
            cxpf
        in
        timing "pure_prop_constructive:done";
        result
      end
    else
      None
  in
  let rec reconstruct_from_refutation () =
    timing "reconstruct_from_refutation:start";
    let debug_source_apply = Sys.getenv_opt "MEGALODON_CERT_DEBUG_SOURCE_APPLY" = Some "1" in
    if debug_source_apply then
      begin
        Printf.printf
          "Vampire native reconstruction entry at line %d char %d: remaining_bindings=%d core_prop=%s\n"
          !lineno
          !charno
          (List.length remaining_bindings)
          (tm_to_str core_proposition);
        List.iteri
          (fun index (name, (tp, definition)) ->
             Printf.printf
               "Vampire native reconstruction cxtm[%d] %s : %s%s\n"
               index
               name
               (tp_to_str tp)
               (match definition with None -> "" | Some tm -> " := " ^ tm_to_str tm))
          cxtm;
        List.iteri
          (fun index (name, prop) ->
             Printf.printf
               "Vampire native reconstruction cxpf[%d] %s : %s\n"
               index
               name
               (tm_to_str prop))
          cxpf;
        List.iter
          (fun binding ->
             Printf.printf
               "Vampire native reconstruction remaining binding %s kind=%s cert_kind=%s proposition=%s\n"
               binding.Vampire_cert_v1.core_native_source_step
               binding.Vampire_cert_v1.core_native_source_map_kind
               binding.Vampire_cert_v1.core_native_certificate_source_kind
               (tm_to_str binding.Vampire_cert_v1.core_native_source_proposition);
             begin match vampire_negated_conjecture_target binding with
             | Some target ->
                 Printf.printf
                   "Vampire native reconstruction remaining binding %s target=%s\n"
                   binding.Vampire_cert_v1.core_native_source_step
                   (tm_to_str target)
             | None -> ()
             end)
          remaining_bindings;
        flush stdout
      end;
    timing "guided_negated_conjecture:start";
    let guided_result =
      match
        List.filter
          vampire_source_binding_is_negated_conjecture
          remaining_bindings
      with
      | [binding] when List.length remaining_bindings = 1 ->
          vampire_guided_negated_conjecture_reconstruction
            ~source_map
            ~extra_delta:reconstruction_delta
            ~extra_symbols:native_core.Vampire_cert_v1.core_native_symbol_table
            ~unchecked_final:true
            claimtm
            cxtm
            cxpf
            native_core.Vampire_cert_v1.core_native_proof
            core_proposition
            binding
      | _ -> None
    in
    timing "guided_negated_conjecture:done";
    match guided_result with
    | Some _ as result ->
        timing "reconstruct_from_refutation:guided_success";
        if debug_source_apply then
          begin
            Printf.printf
              "Vampire native guided negated-conjecture reconstruction succeeded at line %d char %d.\n"
              !lineno
              !charno;
            flush stdout
          end;
        result
    | None ->
    timing "candidate_refutation_fallback:start";
    if debug_source_apply then
      begin
        Printf.printf
          "Vampire native guided negated-conjecture reconstruction failed at line %d char %d; trying source binding applications.\n"
          !lineno
          !charno;
        flush stdout
      end;
    let source_binding_applications_possible =
      match remaining_bindings with
      | [binding]
          when vampire_source_binding_is_negated_conjecture binding
               && vampire_source_proof
                    source_audit
                    binding.Vampire_cert_v1.core_native_source_step = None ->
          false
      | _ -> true
    in
    if not source_binding_applications_possible then
      None
    else
    let rec try_candidates = function
      | [] -> None
      | (proof,proposition,candidate_remaining_bindings) :: rest ->
        begin
          let negated_goal_native = Imp(claimtm,vampire_native_core_false_tm) in
          let negated_goal_context = Imp(claimtm,TmH(!fal)) in
          let rec try_applied = function
            | [] -> try_candidates rest
            | (proof, proposition, [binding]) :: applied_rest
                when binding.Vampire_cert_v1.core_native_certificate_source_kind = "negated_conjecture" ->
                begin
                  let direct_negated_goal =
                    match
                      conv
                        binding.Vampire_cert_v1.core_native_source_proposition
                        negated_goal_native
                        sigdelta
                        [],
                      conv
                        binding.Vampire_cert_v1.core_native_source_proposition
                        negated_goal_context
                        sigdelta
                        []
                    with
                    | Some _, _ | _, Some _ -> true
                    | None, None -> false
                  in
                  if (not direct_negated_goal)
                     && Sys.getenv_opt "MEGALODON_CERT_DEBUG" = Some "1" then
                    begin
                      Printf.printf
                        "Vampire native negated conjecture is not definitionally the current goal negation; trying checked goal transport.\nsource: %s\ngoal negation: %s\n"
                        (tm_to_str binding.Vampire_cert_v1.core_native_source_proposition)
                        (tm_to_str negated_goal_native);
                      flush stdout
                    end;
                  match
                          vampire_reconstruct_current_goal_from_refutation
                            ~source_map
                            ~extra_delta:reconstruction_delta
                            ~extra_symbols:native_core.Vampire_cert_v1.core_native_symbol_table
                            claimtm
                            cxtm
                            cxpf
                      proof
                      proposition
                  with
                  | Some _ as result -> result
                  | None ->
                      begin match vampire_negated_conjecture_target binding with
                      | Some source_target ->
                          begin match
                            vampire_reconstruct_goal_from_supplied_refutation
                              ~source_map
                              ~extra_delta:reconstruction_delta
                              ~extra_symbols:native_core.Vampire_cert_v1.core_native_symbol_table
                              claimtm
                              cxtm
                              cxpf
                              source_target
                              proof
                              proposition
                          with
                          | Some _ as result -> result
                          | None ->
                          begin match
                            vampire_reconstruct_current_goal_from_refutation
                              ~source_map
                              ~extra_delta:reconstruction_delta
                              ~extra_symbols:native_core.Vampire_cert_v1.core_native_symbol_table
                              source_target
                              cxtm
                              cxpf
                              proof
                              proposition
                          with
                          | Some source_target_proof ->
                              begin match
                                vampire_reconstruct_goal_from_proved_prop
                                  ~source_map
                                  ~extra_delta:reconstruction_delta
                                  ~extra_symbols:native_core.Vampire_cert_v1.core_native_symbol_table
                                  claimtm
                                  cxtm
                                  cxpf
                                  source_target_proof
                                  source_target
                              with
                              | Some _ as result -> result
                              | None -> try_applied applied_rest
                              end
                          | None -> try_applied applied_rest
                          end
                          end
                      | None -> try_applied applied_rest
                      end
                end
            | _ :: applied_rest -> try_applied applied_rest
          in
          try_applied
            (vampire_apply_available_source_bindings
               ~extra_delta:reconstruction_delta
               ~extra_symbols:native_core.Vampire_cert_v1.core_native_symbol_table
               cxtm
               cxpf
               source_map
               source_audit
               proof
               proposition
               candidate_remaining_bindings)
        end
    in
    let candidates =
      vampire_instantiated_refutation_candidates
        ~source_map
        ~extra_symbols:native_core.Vampire_cert_v1.core_native_symbol_table
        ~candidate_props:[claimtm]
        cxtm
        native_core.Vampire_cert_v1.core_native_proof
        core_proposition
        remaining_bindings
    in
    timing "candidate_refutation_fallback:candidates_done";
    let result = try_candidates candidates in
    timing "candidate_refutation_fallback:done";
    result
  in
  match
    if !vampireabyqualifying then None
    else reconstruct_pure_prop_schema ()
  with
  | Some _ as result ->
      timing "pure_prop_constructive:success";
      result
  | None ->
      timing "reconstruct_from_refutation_call:start";
      begin match reconstruct_from_refutation () with
      | Some _ as result ->
          timing "reconstruct_from_refutation_call:success";
          result
      | None ->
          if !vampireabyqualifying then
            begin
              timing "fallbacks_disabled_by_qualifying_mode";
              None
            end
          else
            begin
              timing "constructive_fallback:start";
              begin match
                vampire_constructive_goal_search
                  ~source_map
                  ~extra_delta:reconstruction_delta
                  ~extra_symbols:native_core.Vampire_cert_v1.core_native_symbol_table
                  claimtm
                  cxtm
                  cxpf
              with
              | Some _ as result ->
                  timing "constructive_fallback:success";
                  result
              | None ->
                  timing "source_audit_fallback:start";
                  vampire_reconstruct_goal_from_source_audit
                    ~extra_delta:reconstruction_delta
                    ~extra_symbols:native_core.Vampire_cert_v1.core_native_symbol_table
                    claimtm
                    cxtm
                    cxpf
                    source_map
                    source_audit
              end
            end
      end

let check_vampire_aby_native_certificate ?claimtm ?(cxtm=[]) ?(cxpf=[]) ?(proof_command_label="aby") content output proof_file =
  if !vampireabyproof = "megalodon" then
    match native_certificate_payload output with
    | None ->
        raise
          (Failure
             (Printf.sprintf
                "Vampire megalodon proof output %s has no native certificate block"
                proof_file))
    | Some payload ->
        try
          let debug_timing =
            Sys.getenv_opt "MEGALODON_CERT_DEBUG_TIMING" = Some "1"
          in
          let timing_start = Unix.gettimeofday () in
          let timing_last = ref timing_start in
          let timing stage =
            if debug_timing then
              begin
                let now = Unix.gettimeofday () in
                Printf.printf
                  "Vampire native certificate timing %s at line %d char %d: +%.3fs total %.3fs.\n"
                  stage
                  !lineno
                  !charno
                  (now -. !timing_last)
                  (now -. timing_start);
                timing_last := now;
                flush stdout
              end
          in
          timing "payload";
          let cert = Vampire_cert_v1.parse_certificate payload in
          timing "parse_certificate";
          let checked = Vampire_cert_v1.check_certificate_strict cert in
          timing "check_certificate_strict";
          let source_map = Vampire_cert_v1.parse_source_map content in
          timing "parse_source_map";
          timing "validate_certificate_sources:start";
          let source_count =
            Vampire_cert_v1.validate_certificate_sources
              ~require_formula_match:true
              source_map
              cert
          in
          timing "validate_certificate_sources:done";
          let constructive_fallback claimtm =
            if !vampireabyqualifying then
              begin
                timing "constructive_source_goal:disabled_by_qualifying_mode";
                None
              end
            else
              begin
                timing "constructive_source_goal:start";
                let result =
                  vampire_constructive_goal_search
                    ~source_map
                    claimtm
                    cxtm
                    cxpf
                in
                timing "constructive_source_goal:done";
                result
              end
          in
          let build_source_audit () =
            timing "source_bindings:start";
            let source_bindings =
              Vampire_cert_v1.native_certificate_source_bindings
                ~source_map
                ~external_definition_names:
                  (vampire_source_context_external_definition_names cxtm source_map)
                cert
            in
            timing "source_bindings:done";
            let source_context = vampire_aby_source_context cxtm cxpf in
            let source_context =
              {
                source_context with
                Vampire_source_context.proof_delta =
                  vampire_source_context_delta_with_source_map ~cxtm source_map;
                symbol_table =
                  vampire_source_context_symbol_table_with_source_map source_map;
              }
            in
            timing "source_context_resolve:start";
            let audit =
              Vampire_source_context.resolve
                ~strict:(!vampireabynativestrict && cxpf <> [])
                source_context
                source_bindings
            in
            timing "source_context_resolve:done";
            audit
          in
          let source_audit_fallback claimtm audit =
            if !vampireabyqualifying then
              begin
                timing "source_audit_fallback:disabled_by_qualifying_mode";
                None
              end
            else
              begin
                timing "source_audit_fallback:start";
                let result =
                  vampire_reconstruct_goal_from_source_audit
                    claimtm
                    cxtm
                    cxpf
                    source_map
                    audit
                in
                timing "source_audit_fallback:done";
                result
              end
          in
          let source_audit = ref None in
          let replay_from_certificate claimtm =
            if vampire_pure_prop_schema_context cxtm cxpf
               && not !vampireabyqualifying
               && Sys.getenv_opt "MEGALODON_CERT_DISABLE_PURE_PROP_SHORTCUT" <> Some "1" then
              begin
                timing "pure_prop_certificate_shortcut:start";
                let result = constructive_fallback claimtm in
                timing "pure_prop_certificate_shortcut:done";
                match result with
                | Some _ as result -> result
                | None ->
                    let audit = build_source_audit () in
                    source_audit := Some audit;
                    try
                      timing "refutation_replay:start";
                      let result =
                        vampire_certificate_reconstruct_aby_goal
                          claimtm cxtm cxpf cert source_map audit
                      in
                      timing "refutation_replay:done";
                      result
                    with
                    | Vampire_cert_v1.Error msg ->
                        timing "refutation_replay:error";
                        if !verbosity > 8 then
                          begin
                            Printf.printf
                              "Vampire native certificate did not reconstruct current %s goal at line %d char %d: %s.\n"
                              proof_command_label
                              !lineno
                              !charno
                              msg;
                            flush stdout
                          end;
                        begin match constructive_fallback claimtm with
                        | Some _ as result -> result
                        | None -> source_audit_fallback claimtm audit
                        end
                    | Failure msg ->
                        timing "refutation_replay:failure";
                        if !verbosity > 8 then
                          begin
                            Printf.printf
                              "Vampire native certificate proof candidate did not check for current %s goal at line %d char %d: %s.\n"
                              proof_command_label
                              !lineno
                              !charno
                              msg;
                            flush stdout
                          end;
                        begin match constructive_fallback claimtm with
                        | Some _ as result -> result
                        | None -> source_audit_fallback claimtm audit
                        end
              end
            else
              let audit = build_source_audit () in
              source_audit := Some audit;
              try
              timing "refutation_replay:start";
              let result =
                vampire_certificate_reconstruct_aby_goal
                  claimtm cxtm cxpf cert source_map audit
              in
              timing "refutation_replay:done";
              result
            with
            | Vampire_cert_v1.Error msg ->
                timing "refutation_replay:error";
                if !verbosity > 8 then
                  begin
                    Printf.printf
                      "Vampire native certificate did not reconstruct current %s goal at line %d char %d: %s.\n"
                      proof_command_label
                      !lineno
                      !charno
                      msg;
                    flush stdout
                  end;
                begin match constructive_fallback claimtm with
                | Some _ as result -> result
                | None -> source_audit_fallback claimtm audit
                end
            | Failure msg ->
                timing "refutation_replay:failure";
                if !verbosity > 8 then
                  begin
                    Printf.printf
                      "Vampire native certificate proof candidate did not check for current %s goal at line %d char %d: %s.\n"
                      proof_command_label
                      !lineno
                      !charno
                      msg;
                    flush stdout
                  end;
                begin match constructive_fallback claimtm with
                | Some _ as result -> result
                | None -> source_audit_fallback claimtm audit
                end
          in
          let reconstructed =
            match claimtm with
            | None -> None
            | Some claimtm ->
                if proof_command_label = "vampire" || !vampireabynativestrict then
                  replay_from_certificate claimtm
                else
                  begin match constructive_fallback claimtm with
                  | Some _ as result -> result
                  | None -> replay_from_certificate claimtm
                  end
          in
          if !verbosity > 8 then
            begin
              match !source_audit with
              | Some source_audit ->
                  Printf.printf
                    "Vampire native certificate checked %d step%s and %d source%s at line %d char %d; source_context known=%d local=%d local_definition=%d conjecture=%d unresolved=%d.\n"
                    (List.length checked)
                    (if List.length checked = 1 then "" else "s")
                    source_count
                    (if source_count = 1 then "" else "s")
                    !lineno
                    !charno
                    source_audit.Vampire_source_context.known_checked
                    source_audit.Vampire_source_context.local_checked
                    source_audit.Vampire_source_context.local_definition_matched
                    source_audit.Vampire_source_context.conjecture_checked
                    source_audit.Vampire_source_context.unresolved
              | None ->
                  Printf.printf
                    "Vampire native certificate checked %d step%s and %d source%s at line %d char %d; source_context audit skipped after direct source-goal proof.\n"
                    (List.length checked)
                    (if List.length checked = 1 then "" else "s")
                    source_count
                    (if source_count = 1 then "" else "s")
                    !lineno
                    !charno;
              flush stdout
            end
          else
            ();
          begin
            match reconstructed with
            | Some _ when !verbosity > 2 ->
                Printf.printf
                  "Vampire native certificate built local %s proof candidate at line %d char %d.\n"
                  proof_command_label
                  !lineno
                  !charno;
                flush stdout
            | _ -> ()
          end;
          reconstructed
        with Vampire_cert_v1.Error msg ->
          raise
            (Failure
               (Printf.sprintf
                  "Vampire megalodon proof output %s failed native certificate check: %s"
                  proof_file
                  msg))
  else
    None

let run_vampire_aby_certificate ?claimtm ?(cxtm=[]) ?(cxpf=[]) ?(proof_command_label="aby") content =
  match !vampireaby with
  | None -> None
  | Some(vampire) ->
     if !vampireabyqualifying then
       begin
         if !vampireabyproof <> "megalodon" then
           raise (Failure("Qualifying Vampire reconstruction requires -vampireabyproof megalodon"));
         if !vampireabytimeout > 10 then
           raise (Failure("Qualifying Vampire reconstruction requires -vampireabytimeout <= 10"))
       end;
     ensure_directory !vampireabyoutdir;
     let digest = Hash.hashval_hexstring (Hash.sha256 content) in
     let short_digest = String.sub digest 0 16 in
     let base = Printf.sprintf "%s.%d.%d.%s" proof_command_label !lineno !charno short_digest in
     let problem_file = Filename.concat !vampireabyoutdir (base ^ ".thf.p") in
     let proof_file = Filename.concat !vampireabyoutdir (base ^ "." ^ !vampireabyproof ^ ".out") in
     let ch = open_out problem_file in
     Printf.fprintf ch "%s" content;
     close_out ch;
     let cmd =
       Printf.sprintf "%s --input_syntax tptp --mode portfolio --schedule %s -t %d --proof %s %s %s 2>&1"
         (Filename.quote vampire)
         (Filename.quote !vampireabyschedule)
         !vampireabytimeout
         (Filename.quote !vampireabyproof)
         ("--output_axiom_names on " ^ vampire_proof_options !vampireabyproof)
         (Filename.quote problem_file)
     in
     let (out,status) = run_command_capture cmd in
     let ch = open_out proof_file in
     Printf.fprintf ch "%s" out;
     close_out ch;
     if (vampire_output_proved out
         || (!vampireabyproof = "megalodon" && vampire_output_has_native_certificate out))
        && vampire_output_has_proof_payload out then
       begin
         let reconstructed =
           check_vampire_aby_native_certificate ?claimtm ~cxtm ~cxpf ~proof_command_label content out proof_file
         in
         vampire_assert_no_qed_reconstruction_state "Vampire certificate reconstruction";
         if !verbosity > 2 then
           Printf.printf "Vampire produced %s proof payload at line %d char %d (%s)\n" proof_command_label !lineno !charno digest;
         flush stdout;
         reconstructed
       end
     else
       raise
         (Failure
            (Printf.sprintf
               "Vampire failed to certify %s at line %d char %d (%s, proof output %s)"
               proof_command_label !lineno !charno (status_to_string status) proof_file))

let rec th0_aby_head_expand m =
  let m0 = tm_beta_eta_norm m in
  match m0 with
  | Ap(Ap(TpAp(TmH(h),_),_),_) when h = !eqPoly -> m0
  | _ ->
     let (m1,_) = headnorm m0 sigdelta [] in
     match m1 with
     | All(a,q) -> All(a,th0_aby_head_expand q)
     | Imp(p,q) -> Imp(th0_aby_head_expand p,th0_aby_head_expand q)
     | _ -> m0

let tptp_source_map_quote s =
  "\"" ^ String.escaped s ^ "\""

let tptp_source_map_comment kind tptp_name source_name source_hash =
  Printf.sprintf "%% megalodon_source_map (%s %s %s %s)\n"
    kind
    (tptp_source_map_quote tptp_name)
    (tptp_source_map_quote source_name)
    (tptp_source_map_quote source_hash)

let tptp_origin_comment kind =
  match !current_input_file with
  | None -> ""
  | Some file ->
      Printf.sprintf
        "%% megalodon_origin ((file %s) (line \"%d\") (char \"%d\") (kind %s))\n"
        (tptp_source_map_quote file)
        !lineno
        !charno
        (tptp_source_map_quote kind)

let stable_aby_obligation_name () =
  let base =
    match !current_input_file with
    | Some file -> Filename.basename file
    | None -> "megalodon"
  in
  let stem =
    try Filename.remove_extension base
    with Invalid_argument _ -> base
  in
  Printf.sprintf "%s_line%d_char%d" stem !lineno !charno

let th0_aby_problem_content ?(origin_kind="aby") claimtm cxtm cxpf xl conjn =
  Buffer.clear sb;
  Buffer.add_string sb (tptp_origin_comment origin_kind);
  let used_source_formula_names = Hashtbl.create 101 in
  let fresh_source_formula_name base =
    let rec try_index i =
      let candidate =
        if i = 0 then base
        else base ^ "_src" ^ string_of_int (i + 1)
      in
      if Hashtbl.mem used_source_formula_names candidate then try_index (i + 1)
      else
        begin
          Hashtbl.add used_source_formula_names candidate ();
          candidate
        end
    in
    try_index 0
  in
  List.iter
    (fun (cl,h,x,a) ->
      if cl = "type" || cl = "def" && not (Hashtbl.mem sigdelta_opaque h) then
        begin
          let tptp_name =
            if cl = "def" then tptpize_name x ^ "_def"
            else tptpize_name x
          in
          Hashtbl.replace used_source_formula_names tptp_name ();
          Buffer.add_string sb (tptp_source_map_comment cl tptp_name x h);
          Printf.bprintf sb "%s\n" a
        end
      else if cl = "known" && (List.mem x xl || xl = ["-"]) then
        begin
          try
            let (_,p) = Hashtbl.find sigdelta h in
            let tptp_name = tptpize_name x in
            Hashtbl.replace used_source_formula_names tptp_name ();
            Buffer.add_string sb (tptp_source_map_comment "known" tptp_name x h);
            Printf.bprintf sb "thf(%s,axiom,%s). %% %s\n" tptp_name (th0_str (th0_aby_head_expand p) []) h
          with Not_found ->
            let tptp_name = tptpize_name x in
            Hashtbl.replace used_source_formula_names tptp_name ();
            Buffer.add_string sb (tptp_source_map_comment "known" tptp_name x h);
            Printf.bprintf sb "%s\n" a
        end)
    (List.rev !th0sg);
  let rec th0_cx cxtm =
    match cxtm with
    | [] -> ()
    | (x,(a,d))::cxtmr ->
       th0_cx cxtmr;
       let x_tptp = tptpize_name x in
       let type_tptp_name = fresh_source_formula_name (x_tptp ^ "_tp") in
       Buffer.add_string sb (tptp_source_map_comment "local_type" type_tptp_name x "");
       Printf.bprintf sb "thf(%s,type,(%s : %s)).\n" type_tptp_name x_tptp (th0_stp_str a);
       match d with
       | Some(d) ->
          let def_tptp_name = fresh_source_formula_name (x_tptp ^ "_def") in
          Buffer.add_string sb (tptp_source_map_comment "local_definition" def_tptp_name x "");
          Printf.bprintf sb "thf(%s,definition,(%s = %s)).\n" def_tptp_name x_tptp (th0_str d (tptpizecxtm cxtmr))
       | None -> ()
  in
  th0_cx cxtm;
  List.iter
    (fun (x,p) ->
      if List.mem x xl then
        let a = th0_str (th0_aby_head_expand p) (tptpizecxtm cxtm) in
        let fact_tptp_name = fresh_source_formula_name (tptpize_name x) in
        Buffer.add_string sb (tptp_source_map_comment "local_fact" fact_tptp_name x "");
        Printf.bprintf sb "thf(%s,axiom,%s).\n" fact_tptp_name a)
    cxpf;
  let conjecture_tptp_name = fresh_source_formula_name ("conj_" ^ tptpize_name conjn) in
  Buffer.add_string sb (tptp_source_map_comment "conjecture" conjecture_tptp_name conjn "");
  Printf.bprintf sb "thf(%s,conjecture,%s).\n" conjecture_tptp_name (th0_str (th0_aby_head_expand claimtm) (tptpizecxtm cxtm));
  Buffer.contents sb

let rec find_hyp_proving sgdelta hyps goal i =
  match hyps with
  | p::r ->
     begin
       match p,goal with
       | Imp(_,_), Imp(_,_)
       | All(_,_), All(_)
       | DB(_), DB(_)
       | TmH(_), TmH(_)
       | Prim(_), Prim(_)
       | TpAp(_,_), TpAp(_,_)
       | Ap(_,_), Ap(_,_)
       | Lam(_,_), Lam(_,_) ->
          begin
            match conv p goal sgdelta [] with
            | Some(_) -> Some(Hyp(i))
            | None -> find_hyp_proving sgdelta r goal (i+1)
          end
       | _ -> find_hyp_proving sgdelta r goal (i+1)
     end
  | [] -> None

let rec find_false_hyp sgdelta hyps i =
  match hyps with
  | p::r ->
     begin
       match p with
       | All(_,_) | TmH(_) ->
          begin
            match conv p (All(Prop,DB(0))) sgdelta [] with
            | Some(_) -> Some(Hyp(i))
            | None -> find_false_hyp sgdelta r (i+1)
          end
       | _ -> find_false_hyp sgdelta r (i+1)
     end
  | [] -> None

let egal_and_id = "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738"
let egal_and_intro_id = "7f6246d08629eeb16eab93529ffe4f929f43344833ab88c7786393693520e82b"
let egal_or_id = "cfe97741543f37f0262568fe55abbab5772999079ff734a49f37ed123e4363d7"
let egal_or_intro_left_id = "d5fdb4f6cfb82cab64716bee0629544da9b7530752eb0873529def98362fd6b4"
let egal_or_intro_right_id = "5ee4a4103f04cabe781fcdc73566d7dd74b33cb621a83145e1fcff8855469827"

let rec has_or_hyp hyps =
  match hyps with
  | Ap(Ap(TmH(h),_),_)::_ when h = egal_or_id -> true
  | _::r -> has_or_hyp r
  | [] -> false

let egal_false_id = "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87"
let egal_not_id = "058f630dd89cad5a22daa56e097e3bdf85ce16ebd3dbf7994e404e2a98800f7f"
let egal_ex_id = "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099"
let egal_iff_id = "9c60bab687728bc4482e12da2b08b8dbc10f5d71f5cab91acec3c00a79b335a3"
let egal_neq_id = "7966a66a9bb198103c2a540ccd5ebebdff33c10843cc10eebfc98715e142989c"

let native_aby_knowns : (tm * pf) list ref = ref []

let eq_tm a l r = Ap(Ap(TpAp(TmH(!eqPoly),a),l),r)

let is_eq_tm m =
  match m with
  | Ap(Ap(TpAp(TmH(h),a),l),r) when h = !eqPoly -> Some(a,l,r)
  | _ -> None

let rec find_eq_hyp sgdelta hyps a l r i =
  match hyps with
  | p::tl ->
     begin
       match is_eq_tm p with
       | Some(_,_,_) ->
          begin
            match conv p (eq_tm a l r) sgdelta [] with
            | Some(_) -> Some(Hyp(i))
            | None -> find_eq_hyp sgdelta tl a l r (i+1)
          end
       | None -> find_eq_hyp sgdelta tl a l r (i+1)
     end
  | [] -> None

let native_aby_add_inst_term cx a m acc =
  try
    if extr_tpoftm sigtmof cx m = a && not (List.exists (fun n -> n = m) acc) then
      m::acc
    else
      acc
  with _ -> acc

let rec native_aby_collect_inst_terms cx a m acc =
  let acc = native_aby_add_inst_term cx a m acc in
  match m with
  | Ap(m1,m2) ->
     native_aby_collect_inst_terms cx a m2 (native_aby_collect_inst_terms cx a m1 acc)
  | TpAp(m1,_) -> native_aby_collect_inst_terms cx a m1 acc
  | Imp(m1,m2) ->
     native_aby_collect_inst_terms cx a m2 (native_aby_collect_inst_terms cx a m1 acc)
  | _ -> acc

let native_aby_inst_terms cx hyps goal a =
  let rec add_vars scancx i acc =
    match scancx with
    | b::r ->
       let acc = if b = a then native_aby_add_inst_term cx a (DB(i)) acc else acc in
       add_vars r (i+1) acc
    | [] -> acc
  in
  List.rev
    (List.fold_left
       (fun acc m -> native_aby_collect_inst_terms cx a m acc)
       (add_vars cx 0 [])
       (goal::hyps))

let native_aby_dneg_apply goal dnotnot =
  let notnot_goal = Imp(Imp(goal,TmH(egal_false_id)),TmH(egal_false_id)) in
  let rec native_aby_dneg_apply_rec knowns =
    match knowns with
    | (All(Prop,body),d)::r ->
       begin
         match tmsubst body 0 goal with
         | Imp(a,b) ->
            begin
              match conv b goal sigdelta [], conv a notnot_goal sigdelta [] with
              | Some(_), Some(_) -> Some(PPfAp(PTmAp(d,goal),dnotnot))
              | _ -> native_aby_dneg_apply_rec r
            end
         | _ -> native_aby_dneg_apply_rec r
       end
    | _::r -> native_aby_dneg_apply_rec r
    | [] -> None
  in
  native_aby_dneg_apply_rec !native_aby_knowns

let native_aby_known_xm p =
  let rec native_aby_known_xm_rec knowns =
    match knowns with
    | (All(Prop,body),d)::r ->
       begin
         match tmsubst body 0 p with
         | Ap(Ap(TmH(h),a),b) when h = egal_or_id ->
            let not_p = Imp(p,TmH(egal_false_id)) in
            begin
              match conv a p sigdelta [], conv b not_p sigdelta [] with
              | Some(_), Some(_) -> Some(PTmAp(d,p))
              | _ -> native_aby_known_xm_rec r
            end
         | _ -> native_aby_known_xm_rec r
       end
    | _::r -> native_aby_known_xm_rec r
    | [] -> None
  in
  native_aby_known_xm_rec !native_aby_knowns

let rec and_elim_proof sgdelta d p goal =
  match conv p goal sgdelta [] with
  | Some(_) -> Some(d)
  | None ->
     match p with
     | Ap(Ap(TmH(h),a),b) when h = egal_and_id ->
        begin
          match and_elim_proof sgdelta (Hyp(1)) a goal with
          | Some(da) -> Some(PPfAp(PTmAp(d,goal),PLam(a,PLam(b,da))))
          | None ->
             match and_elim_proof sgdelta (Hyp(0)) b goal with
             | Some(db) -> Some(PPfAp(PTmAp(d,goal),PLam(a,PLam(b,db))))
             | None -> None
        end
     | _ -> None

let rec find_and_elim_hyp sgdelta hyps goal i =
  match hyps with
  | (Ap(Ap(TmH(h),_),_) as p)::r when h = egal_and_id ->
     begin
       match and_elim_proof sgdelta (Hyp(i)) p goal with
       | Some(d) -> Some(d)
       | None -> find_and_elim_hyp sgdelta r goal (i+1)
     end
  | Ap(Ap(TmH(h),a),b)::r when h = egal_iff_id ->
     let p_as_and = Ap(Ap(TmH(egal_and_id),Imp(a,b)),Imp(b,a)) in
     begin
       match and_elim_proof sgdelta (Hyp(i)) p_as_and goal with
       | Some(d) -> Some(d)
       | None -> find_and_elim_hyp sgdelta r goal (i+1)
     end
  | _::r -> find_and_elim_hyp sgdelta r goal (i+1)
  | [] -> None

let rec native_aby_direct_depth allow_imp allow_or depth cx hyps goal =
  if depth <= 0 then raise SearchBacktrack;
  match goal with
  | Imp(p,q) -> PLam(p,native_aby_direct_depth allow_imp allow_or depth cx (p::hyps) q)
  | Ap(TmH(h),p) when h = egal_not_id -> PLam(p,native_aby_direct_depth allow_imp allow_or depth cx (p::hyps) (TmH(egal_false_id)))
  | Ap(Ap(TpAp(TmH(h),a),x),y) when h = egal_neq_id -> PLam(eq_tm a x y,native_aby_direct_depth allow_imp allow_or depth cx (eq_tm a x y::hyps) (TmH(egal_false_id)))
  | All(a,q) -> TLam(a,native_aby_direct_depth allow_imp allow_or depth (a::cx) (List.map (tmshift 0 1) hyps) q)
  | Ap(TpAp(TmH(h),a),q) when h = egal_ex_id ->
     begin
       let try_elim () =
         if allow_imp then
           begin
             match find_imp_elim_hyp allow_or depth cx hyps goal 0 with
             | Some(d) -> Some(d)
             | None -> find_known_elim allow_or depth cx hyps goal
           end
         else
           None
       in
       match try_elim () with
       | Some(d) -> d
       | None ->
          match find_ex_intro depth cx hyps a q 0 with
          | Some(d) -> d
          | None ->
             match native_aby_classical_ex depth cx hyps goal with
             | Some(d) -> d
             | None -> raise SearchBacktrack
     end
  | Ap(Ap(TmH(h),a),b) when h = egal_iff_id ->
     native_aby_direct_depth allow_imp allow_or (depth-1) cx hyps (Ap(Ap(TmH(egal_and_id),Imp(a,b)),Imp(b,a)))
  | Ap(Ap(TmH(h),a),b) when h = egal_and_id ->
     let da = native_aby_direct_depth allow_imp allow_or (depth-1) cx hyps a in
     let db = native_aby_direct_depth allow_imp allow_or (depth-1) cx hyps b in
     if Hashtbl.mem sigdelta egal_and_intro_id then
       PPfAp(PPfAp(PTmAp(PTmAp(Known(egal_and_intro_id),a),b),da),db)
     else
       let da = pfshift 0 1 (pftmshift 0 1 da) in
       let db = pfshift 0 1 (pftmshift 0 1 db) in
       TLam(Prop,PLam(Imp(tmshift 0 1 a,Imp(tmshift 0 1 b,DB(0))),PPfAp(PPfAp(Hyp(0),da),db)))
  | Ap(Ap(TmH(h),a),b) when h = egal_or_id ->
     let try_left () =
       let da = native_aby_direct_depth false false (depth-1) cx hyps a in
       if Hashtbl.mem sigdelta egal_or_intro_left_id then
         PPfAp(PTmAp(PTmAp(Known(egal_or_intro_left_id),a),b),da)
       else
         let da = pfshift 0 2 (pftmshift 0 1 da) in
         TLam(Prop,PLam(Imp(tmshift 0 1 a,DB(0)),PLam(Imp(tmshift 0 1 b,DB(0)),PPfAp(Hyp(1),da))))
     in
     let try_right () =
       let db = native_aby_direct_depth false false (depth-1) cx hyps b in
       if Hashtbl.mem sigdelta egal_or_intro_right_id then
         PPfAp(PTmAp(PTmAp(Known(egal_or_intro_right_id),a),b),db)
       else
         let db = pfshift 0 2 (pftmshift 0 1 db) in
         TLam(Prop,PLam(Imp(tmshift 0 1 a,DB(0)),PLam(Imp(tmshift 0 1 b,DB(0)),PPfAp(Hyp(0),db))))
     in
     begin
       let try_intro () =
         try Some(try_left ()) with
         | SearchBacktrack ->
            begin
              try Some(try_right ()) with
              | SearchBacktrack -> None
              | Failure(_) -> None
            end
         | Failure(_) ->
            begin
              try Some(try_right ()) with
              | SearchBacktrack -> None
              | Failure(_) -> None
            end
       in
       match try_intro () with
       | Some(d) -> d
       | None ->
          match native_aby_binunion_elim depth cx hyps goal a b with
          | Some(d) -> d
          | None ->
             match native_aby_upair_elim depth cx hyps goal a b with
             | Some(d) -> d
             | None ->
                match native_aby_xm_or_cases depth cx hyps goal a b with
                | Some(d) -> d
                | None ->
                   match native_aby_if_correct depth cx hyps goal a b with
                   | Some(d) -> d
                   | None ->
                      match native_aby_nand_or depth cx hyps goal a b with
                      | Some(d) -> d
                      | None ->
                         if allow_imp then
                           begin
                             match find_or_elim_hyp depth cx hyps goal 0 with
                             | Some(d) -> d
                             | None ->
                                match find_imp_elim_hyp allow_or depth cx hyps goal 0 with
                                | Some(d) -> d
                                | None ->
                                   match find_known_elim allow_or depth cx hyps goal with
                                   | Some(d) -> d
                                   | None -> raise SearchBacktrack
                           end
                         else
                           raise SearchBacktrack
     end
  | _ ->
     begin
       let direct_fallback () =
       match find_hyp_proving sigdelta hyps goal 0 with
       | Some(d) -> d
       | None ->
          match find_and_elim_hyp sigdelta hyps goal 0 with
          | Some(d) -> d
          | None ->
          match find_false_hyp sigdelta hyps 0 with
          | Some(d) -> PTmAp(d,goal)
          | None ->
             let try_remaining () =
               match find_ex_elim_hyp depth cx hyps goal 0 with
               | Some(d) -> d
               | None ->
                  if allow_or && has_or_hyp hyps then
                    match find_or_elim_hyp depth cx hyps goal 0 with
                    | Some(d) -> d
                    | None -> raise SearchBacktrack
                  else
                    if allow_imp then
                      match find_imp_elim_hyp allow_or depth cx hyps goal 0 with
                      | Some(d) -> d
                      | None ->
                         match find_known_elim allow_or depth cx hyps goal with
                         | Some(d) -> d
                         | None -> raise SearchBacktrack
                    else
                      raise SearchBacktrack
             in
             match is_eq_tm goal with
             | Some(a,x,z) ->
                begin
                  match native_aby_binunion_eq_proof depth cx hyps a x z with
                  | Some(d) -> d
                  | None ->
                  match eq_prop_ext_proof depth cx hyps a x z with
                  | Some(d) -> d
                  | None ->
                     match eq_repl_empty_proof depth cx hyps a x z with
                     | Some(d) -> d
                     | None ->
                        match eq_repl_inv_proof depth cx hyps a x z with
                        | Some(d) -> d
                        | None ->
                        match eq_refl_proof depth cx hyps a x z with
                        | Some(d) -> d
                        | None ->
                           match eq_sym_proof depth cx hyps a x z with
                           | Some(d) -> d
                           | None ->
                              match eq_trans_proof depth cx hyps a x z with
                              | Some(d) -> d
                              | None ->
                                 match eq_func_ext_proof depth cx hyps a x z with
                                 | Some(d) -> d
                                 | None ->
                                    match eq_pred_rewrite_proof depth cx hyps goal with
                                    | Some(d) -> d
                                    | None -> try_remaining ()
                end
             | None ->
                match native_aby_binunion_sub_proof depth cx hyps goal with
                | Some(d) -> d
                | None ->
                   match native_aby_binunion_intro depth cx hyps goal with
                   | Some(d) -> d
                   | None ->
                      match native_aby_upair_intro depth cx hyps goal with
                      | Some(d) -> d
                      | None ->
                         match repl_ext_sub_proof depth cx hyps goal with
                         | Some(d) -> d
                         | None ->
                            match eq_in_elem_rewrite_proof depth cx hyps goal with
                            | Some(d) -> d
                            | None ->
                               match eq_pred_rewrite_proof depth cx hyps goal with
                               | Some(d) -> d
                               | None -> try_remaining ()
       in
       match is_eq_tm goal with
       | Some(_) -> direct_fallback ()
       | None ->
          match native_aby_binunion_sub_proof depth cx hyps goal with
          | Some(d) -> d
          | None ->
             match native_aby_binunion_intro depth cx hyps goal with
             | Some(d) -> d
             | None ->
                match native_aby_upair_intro depth cx hyps goal with
                | Some(d) -> d
                | None ->
                   match repl_ext_sub_proof depth cx hyps goal with
                   | Some(d) -> d
                   | None ->
                      let goal_hn = fst (headnorm goal sigdelta []) in
                      if goal_hn <> tm_beta_eta_norm goal then
                        native_aby_direct_depth allow_imp allow_or (depth-1) cx hyps goal_hn
                      else
                        direct_fallback ()
     end
and native_aby_classical_ex depth cx hyps goal =
  if depth <= 0 then None else
  match goal with
  | Ap(TpAp(TmH(h),a),q) when h = egal_ex_id ->
     let qx = tm_beta_eta_norm (Ap(tmshift 0 1 q,DB(0))) in
     let px_opt =
       match qx with
       | Ap(TmH(h),p) when h = egal_not_id -> Some(p)
       | Imp(p,TmH(h)) when h = egal_false_id -> Some(p)
       | _ -> None
     in
     begin
       match px_opt with
       | Some(px) ->
          let all_px = All(a,px) in
          let not_all_px = Imp(all_px,TmH(egal_false_id)) in
          let rec find_not_all scanhyps i =
            match scanhyps with
            | p::r ->
               begin
                 match conv p not_all_px sigdelta [] with
                 | Some(_) -> Some(i)
                 | None -> find_not_all r (i+1)
               end
            | [] -> None
          in
          begin
            match find_not_all hyps 0 with
            | Some(i) ->
               let not_goal = Imp(goal,TmH(egal_false_id)) in
               let shifted_goal = tmshift 0 1 goal in
               let shifted_not_goal = tmshift 0 1 not_goal in
               begin
                 try
                   let dex =
                     native_aby_direct_depth
                       false false (depth-1)
                       (a::cx)
                       (Imp(px,TmH(egal_false_id))::shifted_not_goal::List.map (tmshift 0 1) hyps)
                       shifted_goal
                   in
                   let dfalse_px = PPfAp(Hyp(1),dex) in
                   match native_aby_dneg_apply px (PLam(Imp(px,TmH(egal_false_id)),dfalse_px)) with
                   | Some(dpx) ->
                      let dall = TLam(a,dpx) in
                      let dfalse_goal = PPfAp(Hyp(i+1),dall) in
                      native_aby_dneg_apply goal (PLam(not_goal,dfalse_goal))
                   | None -> None
                 with
                 | SearchBacktrack -> None
                 | Failure(_) -> None
               end
            | None -> None
          end
       | None -> None
     end
  | _ -> None
and native_aby_nand_or depth cx hyps goal a b =
  if depth <= 0 then None else
  let not_a = Imp(a,TmH(egal_false_id)) in
  let not_b = Imp(b,TmH(egal_false_id)) in
  let nand_ab = Imp(Ap(Ap(TmH(egal_and_id),not_a),not_b),TmH(egal_false_id)) in
  let rec find_nand scanhyps =
    match scanhyps with
    | p::r ->
       begin
         match conv p nand_ab sigdelta [] with
         | Some(_) -> true
         | None -> find_nand r
       end
    | [] -> false
  in
  if not (find_nand hyps) then None else
  match native_aby_known_xm a, native_aby_known_xm b with
  | Some(dxa), Some(dxb) ->
     begin
       try
         let da = native_aby_direct_depth false false (depth-1) cx (a::hyps) goal in
         let db = native_aby_direct_depth false false (depth-1) cx (b::not_a::hyps) goal in
         let dfalse = native_aby_direct_depth true false (depth-1) cx (not_b::not_a::hyps) (TmH(egal_false_id)) in
         let dnotb = PTmAp(dfalse,goal) in
         let dnot_a_case = PPfAp(PPfAp(PTmAp(dxb,goal),PLam(b,db)),PLam(not_b,dnotb)) in
         Some(PPfAp(PPfAp(PTmAp(dxa,goal),PLam(a,da)),PLam(not_a,dnot_a_case)))
       with
       | SearchBacktrack -> None
       | Failure(_) -> None
     end
  | _ -> None
and native_aby_or_intro_left a b da =
  if Hashtbl.mem sigdelta egal_or_intro_left_id then
    PPfAp(PTmAp(PTmAp(Known(egal_or_intro_left_id),a),b),da)
  else
    let da = pfshift 0 2 (pftmshift 0 1 da) in
    TLam(Prop,PLam(Imp(tmshift 0 1 a,DB(0)),PLam(Imp(tmshift 0 1 b,DB(0)),PPfAp(Hyp(1),da))))
and native_aby_or_intro_right a b db =
  if Hashtbl.mem sigdelta egal_or_intro_right_id then
    PPfAp(PTmAp(PTmAp(Known(egal_or_intro_right_id),a),b),db)
  else
    let db = pfshift 0 2 (pftmshift 0 1 db) in
    TLam(Prop,PLam(Imp(tmshift 0 1 a,DB(0)),PLam(Imp(tmshift 0 1 b,DB(0)),PPfAp(Hyp(0),db))))
and native_aby_xm_or_cases depth cx hyps goal a b =
  if depth <= 0 then None else
  let rec try_props props =
    match props with
    | p::r ->
       begin
         match native_aby_known_xm p with
         | Some(dxm) ->
            let notp = Imp(p,TmH(egal_false_id)) in
            begin
              try
                let da = native_aby_direct_depth true true (depth-1) cx (p::hyps) a in
                let db = native_aby_direct_depth true true (depth-1) cx (notp::hyps) b in
                let dleft = native_aby_or_intro_left a b da in
                let dright = native_aby_or_intro_right a b db in
                Some(PPfAp(PPfAp(PTmAp(dxm,goal),PLam(p,dleft)),PLam(notp,dright)))
              with
              | SearchBacktrack -> try_props r
              | Failure(_) -> try_props r
            end
         | None -> try_props r
       end
    | [] -> None
  in
  try_props (native_aby_inst_terms cx hyps goal Prop)
and native_aby_upair_elim depth cx hyps goal a b =
  if depth <= 0 then None else
  try
    let empty_h = Hashtbl.find sigtmh "Empty" in
    let power_h = Hashtbl.find sigtmh "Power" in
    let in_h = Hashtbl.find sigtmh "In" in
    let if_h = Hashtbl.find sigtmh "If_i" in
    let upair_h = Hashtbl.find sigtmh "UPair" in
    let if_or_h = Hashtbl.find sigknh "If_i_or" in
    let replE_impred_h = Hashtbl.find sigknh "ReplE_impred" in
    let domain = Ap(TmH(power_h),Ap(TmH(power_h),TmH(empty_h))) in
    let in_tm x y = Ap(Ap(TmH(in_h),x),y) in
    let f y z =
      Lam(Set,
          Ap(Ap(Ap(TmH(if_h),in_tm (TmH(empty_h)) (DB(0))),
                tmshift 0 1 y),
             tmshift 0 1 z))
    in
    let rec scan scanhyps i =
      match scanhyps with
      | h::r ->
         begin
           match is_eq_tm a, is_eq_tm b, h with
           | Some(Set,x,y), Some(Set,x2,z), Ap(Ap(TmH(ih),xh),Ap(Ap(TmH(uh),yh),zh))
                when ih = in_h && uh = upair_h ->
              begin
                match conv x x2 sigdelta [], conv x xh sigdelta [], conv y yh sigdelta [], conv z zh sigdelta [] with
                | Some(_), Some(_), Some(_), Some(_) ->
                   let f_yz = f y z in
                   let shifted_hyps = List.map (tmshift 0 1) hyps in
                   let x1 = tmshift 0 1 x in
                   let y1 = tmshift 0 1 y in
                   let z1 = tmshift 0 1 z in
                   let f1 = tmshift 0 1 f_yz in
                   let w = DB(0) in
                   let fw = Ap(f1,w) in
                   let p = in_tm (TmH(empty_h)) w in
                   let w_in_domain = in_tm w (tmshift 0 1 domain) in
                   let x_eq_fw = eq_tm Set x1 fw in
                   let branch_goal = tmshift 0 1 goal in
                   let if_or_prop =
                     Ap(Ap(TmH(egal_or_id),eq_tm Set fw y1),eq_tm Set fw z1)
                   in
                   let dif =
                     PTmAp(PTmAp(PTmAp(Known(if_or_h),p),y1),z1)
                   in
                   begin
                     match or_elim_proof
                             (depth-1)
                             (Set::cx)
                             (x_eq_fw::w_in_domain::shifted_hyps)
                             dif
                             if_or_prop
                             branch_goal with
                     | Some(body) ->
                        let branch = TLam(Set,PLam(w_in_domain,PLam(x_eq_fw,body))) in
                        Some
                          (PPfAp
                             (PTmAp
                                (PPfAp
                                   (PTmAp(PTmAp(PTmAp(Known(replE_impred_h),domain),f_yz),x),
                                    Hyp(i)),
                                 goal),
                              branch))
                     | None -> scan r (i+1)
                   end
                | _ -> scan r (i+1)
              end
           | _ -> scan r (i+1)
         end
      | [] -> None
    in
    scan hyps 0
  with
  | Not_found -> None
  | SearchBacktrack -> None
  | Failure(_) -> None
and native_aby_upair_intro depth cx hyps goal =
  if depth <= 0 then None else
  try
    let empty_h = Hashtbl.find sigtmh "Empty" in
    let power_h = Hashtbl.find sigtmh "Power" in
    let in_h = Hashtbl.find sigtmh "In" in
    let if_h = Hashtbl.find sigtmh "If_i" in
    let upair_h = Hashtbl.find sigtmh "UPair" in
    let empty_in_power_h = Hashtbl.find sigknh "Empty_In_Power" in
    let emptyE_h = Hashtbl.find sigknh "EmptyE" in
    let self_in_power_h = Hashtbl.find sigknh "Self_In_Power" in
    let replI_h = Hashtbl.find sigknh "ReplI" in
    let if_i_0_h = Hashtbl.find sigknh "If_i_0" in
    let if_i_1_h = Hashtbl.find sigknh "If_i_1" in
    let empty = TmH(empty_h) in
    let power_empty = Ap(TmH(power_h),empty) in
    let domain = Ap(TmH(power_h),power_empty) in
    let in_tm x y = Ap(Ap(TmH(in_h),x),y) in
    let f y z =
      Lam(Set,
          Ap(Ap(Ap(TmH(if_h),in_tm empty (DB(0))),
                tmshift 0 1 y),
             tmshift 0 1 z))
    in
    let rewrite_elem deq dsource target =
      PPfAp
        (PTmAp(deq,Lam(Set,Lam(Set,in_tm (DB(1)) (tmshift 0 2 target)))),
         dsource)
    in
    match goal with
    | Ap(Ap(TmH(ih),elem),Ap(Ap(TmH(uh),y),z)) when ih = in_h && uh = upair_h ->
       let target = Ap(Ap(TmH(upair_h),y),z) in
       let f_yz = f y z in
       let build w dw_domain deq =
         let dsource =
           PPfAp
             (PTmAp(PTmAp(PTmAp(Known(replI_h),domain),f_yz),w),
              dw_domain)
         in
         rewrite_elem deq dsource target
       in
       let try_left () =
         match conv elem y sigdelta [] with
         | Some(_) ->
            let w = power_empty in
            let p = in_tm empty w in
            let dw_domain = PTmAp(Known(self_in_power_h),w) in
            let dp = PTmAp(Known(empty_in_power_h),empty) in
            let deq =
              PPfAp(PTmAp(PTmAp(PTmAp(Known(if_i_1_h),p),y),z),dp)
            in
            Some(build w dw_domain deq)
         | None -> None
       in
       let try_right () =
         match conv elem z sigdelta [] with
         | Some(_) ->
            let w = empty in
            let p = in_tm empty w in
            let dw_domain = PTmAp(Known(empty_in_power_h),power_empty) in
            let dnotp = PTmAp(Known(emptyE_h),empty) in
            let deq =
              PPfAp(PTmAp(PTmAp(PTmAp(Known(if_i_0_h),p),y),z),dnotp)
            in
            Some(build w dw_domain deq)
         | None -> None
       in
       begin
         match try_left () with
         | Some(d) -> Some(d)
         | None -> try_right ()
       end
    | _ -> None
  with
  | Not_found -> None
  | SearchBacktrack -> None
  | Failure(_) -> None
and native_aby_binunion_intro depth cx hyps goal =
  if depth <= 0 then None else
  try
    let in_h = Hashtbl.find sigtmh "In" in
    let union_h = Hashtbl.find sigtmh "Union" in
    let upair_h = Hashtbl.find sigtmh "UPair" in
    let binunion_h = Hashtbl.find sigtmh "binunion" in
    let unionI_h = Hashtbl.find sigknh "UnionI" in
    let upairI1_h = Hashtbl.find sigknh "UPairI1" in
    let upairI2_h = Hashtbl.find sigknh "UPairI2" in
    let in_tm x y = Ap(Ap(TmH(in_h),x),y) in
    let build container elem member dmem dmember =
      PPfAp
        (PPfAp
           (PTmAp(PTmAp(PTmAp(Known(unionI_h),container),elem),member),
            dmem),
         dmember)
    in
    let try_sources elem left right container =
      let try_left () =
        try
          let dmem = native_aby_direct_depth true true (depth-1) cx hyps (in_tm elem left) in
          let dleft = PTmAp(PTmAp(Known(upairI1_h),left),right) in
          Some(build container elem left dmem dleft)
        with
        | SearchBacktrack -> None
        | Failure(_) -> None
      in
      let try_right () =
        try
          let dmem = native_aby_direct_depth true true (depth-1) cx hyps (in_tm elem right) in
          let dright = PTmAp(PTmAp(Known(upairI2_h),left),right) in
          Some(build container elem right dmem dright)
        with
        | SearchBacktrack -> None
        | Failure(_) -> None
      in
      match try_left () with
      | Some(d) -> Some(d)
      | None -> try_right ()
    in
    match goal with
    | Ap(Ap(TmH(ih),elem),target) when ih = in_h ->
       begin
         match target with
         | Ap(Ap(TmH(bh),left),right) when bh = binunion_h ->
            let container = Ap(Ap(TmH(upair_h),left),right) in
            try_sources elem left right container
         | Ap(TmH(uh),Ap(Ap(TmH(ph),left),right)) when uh = union_h && ph = upair_h ->
            try_sources elem left right target
         | _ -> None
       end
    | _ -> None
  with
  | Not_found -> None
  | SearchBacktrack -> None
  | Failure(_) -> None
and native_aby_binunion_elim depth cx hyps goal a b =
  if depth <= 0 then None else
  try
    let in_h = Hashtbl.find sigtmh "In" in
    let upair_h = Hashtbl.find sigtmh "UPair" in
    let binunion_h = Hashtbl.find sigtmh "binunion" in
    let unionE_impred_h = Hashtbl.find sigknh "UnionE_impred" in
    let upairE_h = Hashtbl.find sigknh "UPairE" in
    let in_tm x y = Ap(Ap(TmH(in_h),x),y) in
    match a,b with
    | Ap(Ap(TmH(ih1),elem),left), Ap(Ap(TmH(ih2),elem2),right)
         when ih1 = in_h && ih2 = in_h ->
       begin
         match conv elem elem2 sigdelta [] with
         | Some(_) ->
            let union_target = Ap(Ap(TmH(binunion_h),left),right) in
            let expected_hyp = in_tm elem union_target in
            let container = Ap(Ap(TmH(upair_h),left),right) in
            let rec scan scanhyps i =
              match scanhyps with
              | h::r ->
                 begin
                   match conv h expected_hyp sigdelta [] with
                   | Some(_) ->
                      let left1 = tmshift 0 1 left in
                      let right1 = tmshift 0 1 right in
                      let elem1 = tmshift 0 1 elem in
                      let container1 = tmshift 0 1 container in
                      let w = DB(0) in
                      let elem_in_w = in_tm elem1 w in
                      let w_in_container = in_tm w container1 in
                      let shifted_hyps = List.map (tmshift 0 1) hyps in
                      let branch_goal = tmshift 0 1 goal in
                      let eq_w_left = eq_tm Set w left1 in
                      let eq_w_right = eq_tm Set w right1 in
                      let pair_or = Ap(Ap(TmH(egal_or_id),eq_w_left),eq_w_right) in
                      let dpair =
                        PPfAp
                          (PTmAp(PTmAp(PTmAp(Known(upairE_h),w),left1),right1),
                           Hyp(0))
                      in
                      begin
                        match or_elim_proof
                                (depth-1)
                                (Set::cx)
                                (w_in_container::elem_in_w::shifted_hyps)
                                dpair
                                pair_or
                                branch_goal with
                        | Some(body) ->
                           let branch = TLam(Set,PLam(elem_in_w,PLam(w_in_container,body))) in
                           Some
                             (PPfAp
                                (PTmAp
                                   (PPfAp
                                      (PTmAp(PTmAp(Known(unionE_impred_h),container),elem),
                                       Hyp(i)),
                                    goal),
                                 branch))
                        | None -> scan r (i+1)
                      end
                   | None -> scan r (i+1)
                 end
              | [] -> None
            in
            scan hyps 0
         | None -> None
       end
    | _ -> None
  with
  | Not_found -> None
  | SearchBacktrack -> None
  | Failure(_) -> None
and native_aby_binunion_shape binunion_h union_h upair_h m =
  match m with
  | Ap(Ap(TmH(h),left),right) when h = binunion_h -> Some(left,right)
  | Ap(TmH(uh),Ap(Ap(TmH(ph),left),right)) when uh = union_h && ph = upair_h -> Some(left,right)
  | _ -> None
and native_aby_binunion_contains binunion_h union_h upair_h m =
  match native_aby_binunion_shape binunion_h union_h upair_h m with
  | Some(_) -> true
  | None ->
  match m with
  | Ap(m,n) -> native_aby_binunion_contains binunion_h union_h upair_h m || native_aby_binunion_contains binunion_h union_h upair_h n
  | TpAp(m,_) -> native_aby_binunion_contains binunion_h union_h upair_h m
  | Lam(_,m) | All(_,m) -> native_aby_binunion_contains binunion_h union_h upair_h m
  | Imp(m,n) -> native_aby_binunion_contains binunion_h union_h upair_h m || native_aby_binunion_contains binunion_h union_h upair_h n
  | _ -> false
and native_aby_binunion_membership depth cx hyps elem target =
  if depth <= 0 then raise SearchBacktrack else
  let in_h = Hashtbl.find sigtmh "In" in
  let subq_h = Hashtbl.find sigtmh "Subq" in
  let empty_h = Hashtbl.find sigtmh "Empty" in
  let union_h = Hashtbl.find sigtmh "Union" in
  let upair_h = Hashtbl.find sigtmh "UPair" in
  let binunion_h = Hashtbl.find sigtmh "binunion" in
  let unionI_h = Hashtbl.find sigknh "UnionI" in
  let binunionE_h = Hashtbl.find sigknh "binunionE" in
  let upairI1_h = Hashtbl.find sigknh "UPairI1" in
  let upairI2_h = Hashtbl.find sigknh "UPairI2" in
  let emptyE_h = Hashtbl.find sigknh "EmptyE" in
  let in_tm x y = Ap(Ap(TmH(in_h),x),y) in
  let goal = in_tm elem target in
  let build_intro container member dmem dmember =
    PPfAp
      (PPfAp
         (PTmAp(PTmAp(PTmAp(Known(unionI_h),container),elem),member),
          dmem),
       dmember)
  in
  let find_empty_elim () =
    let rec scan scanhyps i =
      match scanhyps with
      | Ap(Ap(TmH(ih),e),TmH(eh))::r when ih = in_h && eh = empty_h ->
         let dfalse = PPfAp(PTmAp(Known(emptyE_h),e),Hyp(i)) in
         Some(PTmAp(dfalse,goal))
      | _::r -> scan r (i+1)
      | [] -> None
    in
    scan hyps 0
  in
  let try_intro_target () =
    match native_aby_binunion_shape binunion_h union_h upair_h target with
    | Some(left,right) ->
       let container = Ap(Ap(TmH(upair_h),left),right) in
       let try_left () =
         try
           let dmem = native_aby_binunion_membership (depth-1) cx hyps elem left in
           let dleft = PTmAp(PTmAp(Known(upairI1_h),left),right) in
           Some(build_intro container left dmem dleft)
         with
         | SearchBacktrack -> None
         | Failure(_) -> None
       in
       let try_right () =
         try
           let dmem = native_aby_binunion_membership (depth-1) cx hyps elem right in
           let dright = PTmAp(PTmAp(Known(upairI2_h),left),right) in
           Some(build_intro container right dmem dright)
         with
         | SearchBacktrack -> None
         | Failure(_) -> None
       in
       begin
         match try_left () with
         | Some(d) -> Some(d)
         | None -> try_right ()
       end
    | None -> None
  in
  let try_elim_source () =
    let rec scan scanhyps i =
      match scanhyps with
      | Ap(Ap(TmH(ih),e),source)::r when ih = in_h ->
         begin
           match conv e elem sigdelta [], native_aby_binunion_shape binunion_h union_h upair_h source with
           | Some(_), Some(left,right) ->
              let a = in_tm elem left in
              let b = in_tm elem right in
              let d_or =
                PPfAp
                  (PTmAp(PTmAp(PTmAp(Known(binunionE_h),left),right),elem),
                   Hyp(i))
              in
              begin
                try
                  let da = native_aby_binunion_membership (depth-1) cx (a::hyps) elem target in
                  let db = native_aby_binunion_membership (depth-1) cx (b::hyps) elem target in
                  Some(PPfAp(PPfAp(PTmAp(d_or,goal),PLam(a,da)),PLam(b,db)))
                with
                | SearchBacktrack -> scan r (i+1)
                | Failure(_) -> scan r (i+1)
              end
           | _ -> scan r (i+1)
         end
      | _::r -> scan r (i+1)
      | [] -> None
    in
    scan hyps 0
  in
  let try_subq_hyp () =
    let rec scan scanhyps i =
      match scanhyps with
      | Ap(Ap(TmH(h),source),target2)::r when h = subq_h ->
         begin
           match conv target2 target sigdelta [] with
           | Some(_) ->
              begin
                try
                  let dsource = native_aby_binunion_membership (depth-1) cx hyps elem source in
                  Some(PPfAp(PTmAp(Hyp(i),elem),dsource))
                with
                | SearchBacktrack -> scan r (i+1)
                | Failure(_) -> scan r (i+1)
              end
           | None -> scan r (i+1)
         end
      | _::r -> scan r (i+1)
      | [] -> None
    in
    scan hyps 0
  in
  match find_hyp_proving sigdelta hyps goal 0 with
  | Some(d) -> d
  | None ->
     match find_empty_elim () with
     | Some(d) -> d
     | None ->
        match try_subq_hyp () with
        | Some(d) -> d
        | None ->
           match try_elim_source () with
           | Some(d) -> d
           | None ->
              match try_intro_target () with
              | Some(d) -> d
              | None -> raise SearchBacktrack
and native_aby_binunion_sub_proof depth cx hyps goal =
  if depth <= 0 then None else
  try
    let subq_h = Hashtbl.find sigtmh "Subq" in
    let in_h = Hashtbl.find sigtmh "In" in
    match goal with
    | Ap(Ap(TmH(h),source),target) when h = subq_h ->
       let source1 = tmshift 0 1 source in
       let target1 = tmshift 0 1 target in
       let elem = DB(0) in
       let elem_in_source = Ap(Ap(TmH(in_h),elem),source1) in
       let body =
         native_aby_binunion_membership
           (depth-1)
           (Set::cx)
           (elem_in_source::List.map (tmshift 0 1) hyps)
           elem
           target1
       in
       Some(TLam(Set,PLam(elem_in_source,body)))
    | _ -> None
  with
  | Not_found -> None
  | SearchBacktrack -> None
  | Failure(_) -> None
and native_aby_binunion_eq_proof depth cx hyps a lhs rhs =
  if depth <= 0 || a <> Set then None else
  try
    let binunion_h = Hashtbl.find sigtmh "binunion" in
    let union_h = Hashtbl.find sigtmh "Union" in
    let upair_h = Hashtbl.find sigtmh "UPair" in
    if not (native_aby_binunion_contains binunion_h union_h upair_h lhs || native_aby_binunion_contains binunion_h union_h upair_h rhs) then
      None
    else
      let subq_h = Hashtbl.find sigtmh "Subq" in
      let set_ext_h = Hashtbl.find sigknh "set_ext" in
      let left_sub_goal = Ap(Ap(TmH(subq_h),lhs),rhs) in
      let right_sub_goal = Ap(Ap(TmH(subq_h),rhs),lhs) in
      match native_aby_binunion_sub_proof depth cx hyps left_sub_goal,
            native_aby_binunion_sub_proof depth cx hyps right_sub_goal with
      | Some(left_sub), Some(right_sub) ->
         Some(PPfAp(PPfAp(PTmAp(PTmAp(Known(set_ext_h),lhs),rhs),left_sub),right_sub))
      | _ -> None
  with
  | Not_found -> None
  | SearchBacktrack -> None
  | Failure(_) -> None
and native_aby_if_correct depth cx hyps goal a b =
  if depth <= 0 then None else
  try
    let and_h = egal_and_id in
    let eps_ax_h = Hashtbl.find sigknh "Eps_i_ax" in
    let p_x_y =
      match a,b with
      | Ap(Ap(TmH(ah1),p),eqx), Ap(Ap(TmH(ah2),notp),eqy) when ah1 = and_h && ah2 = and_h ->
         begin
           match is_eq_tm eqx, is_eq_tm eqy with
           | Some(Set,ifx,x), Some(Set,ify,y) ->
              begin
                match conv ifx ify sigdelta [] with
                | Some(_) ->
                   let expected_notp = Imp(p,TmH(egal_false_id)) in
                   begin
                     match conv notp expected_notp sigdelta [] with
                     | Some(_) -> Some(p,notp,x,y)
                     | None -> None
                   end
                | None -> None
              end
           | _ -> None
         end
      | _ -> None
    in
    match p_x_y with
    | Some(p,notp,x,y) ->
       begin
         match native_aby_known_xm p with
         | Some(dxm) ->
            let p1 = tmshift 0 1 p in
            let notp1 = tmshift 0 1 notp in
            let x1 = tmshift 0 1 x in
            let y1 = tmshift 0 1 y in
            let q =
              Lam(Set,
                  Ap(Ap(TmH(egal_or_id),
                        Ap(Ap(TmH(egal_and_id),p1),eq_tm Set (DB(0)) x1)),
                     Ap(Ap(TmH(egal_and_id),notp1),eq_tm Set (DB(0)) y1)))
            in
            let dp =
              native_aby_direct_depth
                true true (depth-1) cx (p::hyps) (Ap(q,x))
            in
            let dnotp =
              native_aby_direct_depth
                true true (depth-1) cx (notp::hyps) (Ap(q,y))
            in
            let dcase_p =
              PPfAp(PTmAp(PTmAp(Known(eps_ax_h),q),x),dp)
            in
            let dcase_notp =
              PPfAp(PTmAp(PTmAp(Known(eps_ax_h),q),y),dnotp)
            in
            Some(PPfAp(PPfAp(PTmAp(dxm,goal),PLam(p,dcase_p)),PLam(notp,dcase_notp)))
         | None -> None
       end
    | None -> None
  with
  | Not_found -> None
  | SearchBacktrack -> None
  | Failure(_) -> None
and eq_trans_proof depth cx hyps a x z =
  if depth <= 0 then None else
  let rec try_middle_terms scancx i =
    match scancx with
    | b::tl ->
       let y = DB(i) in
       if b = a then begin
         match find_eq_hyp sigdelta hyps a x y 0, find_eq_hyp sigdelta hyps a y z 0 with
         | Some(dxy), Some(dyz) ->
            let x1 = tmshift 0 1 x in
            let z1 = tmshift 0 1 z in
            let z3 = tmshift 0 2 z1 in
            let dxy = pfshift 0 1 (pftmshift 0 1 dxy) in
            let dyz = pfshift 0 1 (pftmshift 0 1 dyz) in
            let qxz = Ap(Ap(DB(0),x1),z1) in
            let q_u_z = Lam(a,Lam(a,Ap(Ap(DB(2),DB(1)),z3))) in
            let q_z_v = Lam(a,Lam(a,Ap(Ap(DB(2),z3),DB(0)))) in
            let qyz = PPfAp(PTmAp(dxy,q_u_z),Hyp(0)) in
            let qzy = PPfAp(PTmAp(dyz,DB(0)),qyz) in
            Some(TLam(Ar(a,Ar(a,Prop)),PLam(qxz,PPfAp(PTmAp(dxy,q_z_v),qzy))))
         | _ -> try_middle_terms tl (i+1)
       end else
         try_middle_terms tl (i+1)
    | [] -> None
  in
  try_middle_terms cx 0
and eq_sym_proof depth cx hyps a x z =
  if depth <= 0 then None else
  match find_eq_hyp sigdelta hyps a z x 0 with
  | Some(dzx) ->
     let x1 = tmshift 0 1 x in
     let z1 = tmshift 0 1 z in
     let dzx = pfshift 0 1 (pftmshift 0 1 dzx) in
     let qxz = Ap(Ap(DB(0),x1),z1) in
     let q_swap = Lam(a,Lam(a,Ap(Ap(DB(2),DB(0)),DB(1)))) in
     Some(TLam(Ar(a,Ar(a,Prop)),PLam(qxz,PPfAp(PTmAp(dzx,q_swap),Hyp(0)))))
  | None -> None
and eq_refl_proof depth cx hyps a x z =
  if depth <= 0 then None else
  match conv x z sigdelta [] with
  | Some(_) ->
     let x1 = tmshift 0 1 x in
     let qxx = Ap(Ap(DB(0),x1),x1) in
     Some(TLam(Ar(a,Ar(a,Prop)),PLam(qxx,Hyp(0))))
  | None -> None
and eq_prop_ext_proof depth cx hyps a p q =
  if depth <= 0 || a <> Prop then None else
  let expected = Imp(Imp(p,q),Imp(Imp(q,p),eq_tm Prop p q)) in
  let rec try_knowns knowns =
    match knowns with
    | (All(Prop,All(Prop,body)),d)::r ->
       let body_pq =
         match tmsubst (All(Prop,body)) 0 p with
         | All(_,body_p) -> tmsubst body_p 0 q
         | body_p -> tmsubst body_p 0 q
       in
       begin
         match conv body_pq expected sigdelta [] with
         | Some(_) ->
            begin
              try
                let dpq = native_aby_direct_depth true true (depth-1) cx hyps (Imp(p,q)) in
                let dqp = native_aby_direct_depth true true (depth-1) cx hyps (Imp(q,p)) in
                Some(PPfAp(PPfAp(PTmAp(PTmAp(d,p),q),dpq),dqp))
              with
              | SearchBacktrack -> try_knowns r
              | Failure(_) -> try_knowns r
            end
         | None -> try_knowns r
       end
    | _::r -> try_knowns r
    | [] -> None
  in
  try_knowns !native_aby_knowns
and eq_func_ext_proof depth cx hyps a f g =
  if depth <= 0 then None else
  match a with
  | Ar(a1,a2) ->
     begin
       try
         let h = Hashtbl.find sigknh "func_ext" in
         let point_goal = eq_tm a2 (Ap(tmshift 0 1 f,DB(0))) (Ap(tmshift 0 1 g,DB(0))) in
         let point_hyps = List.map (tmshift 0 1) hyps in
         let dpoint = native_aby_direct_depth true true (depth-1) (a1::cx) point_hyps point_goal in
         Some(PPfAp(PTmAp(PTmAp(PTpAp(PTpAp(Known(h),a1),a2),f),g),TLam(a1,dpoint)))
       with
       | Not_found -> None
       | SearchBacktrack -> None
       | Failure(_) -> None
     end
  | _ -> None
and eq_repl_empty_proof depth cx hyps a x z =
  if depth <= 0 || a <> Set then None else
  try
    let empty_h = Hashtbl.find sigtmh "Empty" in
    let repl_h = Hashtbl.find sigtmh "Repl" in
    let in_h = Hashtbl.find sigtmh "In" in
    let empty_eq_h = Hashtbl.find sigknh "Empty_eq" in
    let emptyE_h = Hashtbl.find sigknh "EmptyE" in
    let replE_impred_h = Hashtbl.find sigknh "ReplE_impred" in
    match x, z with
    | Ap(Ap(TmH(h),empty),f), TmH(eh) when h = repl_h && eh = empty_h ->
       begin
         match conv empty (TmH(empty_h)) sigdelta [] with
         | Some(_) ->
            let repl_empty_f = Ap(Ap(TmH(repl_h),TmH(empty_h)),f) in
            let shifted_repl_empty_f = tmshift 0 1 repl_empty_f in
            let shifted_f = tmshift 0 1 f in
            let y_in_repl = Ap(Ap(TmH(in_h),DB(0)),shifted_repl_empty_f) in
            let emptyE_x = PTmAp(Known(emptyE_h),DB(0)) in
            let branch_false = PPfAp(emptyE_x,Hyp(1)) in
            let y_eq_fx = eq_tm Set (DB(1)) (Ap(tmshift 0 1 shifted_f,DB(0))) in
            let branch =
              TLam(Set,
                   PLam(Ap(Ap(TmH(in_h),DB(0)),tmshift 0 2 (TmH(empty_h))),
                        PLam(y_eq_fx,branch_false)))
            in
            let repl_elim =
              PPfAp
                (PTmAp
                   (PPfAp
                      (PTmAp(PTmAp(PTmAp(Known(replE_impred_h),TmH(empty_h)),shifted_f),DB(0)),
                       Hyp(0)),
                    TmH(egal_false_id)),
                 branch)
            in
            let notin_proof = TLam(Set,PLam(y_in_repl,repl_elim)) in
            Some(PPfAp(PTmAp(Known(empty_eq_h),repl_empty_f),notin_proof))
         | None -> None
       end
    | _ -> None
  with
  | Not_found -> None
  | SearchBacktrack -> None
  | Failure(_) -> None
and eq_repl_inv_proof depth cx hyps a lhs rhs =
  if depth <= 0 || a <> Set then None else
  try
    let repl_h = Hashtbl.find sigtmh "Repl" in
    let in_h = Hashtbl.find sigtmh "In" in
    let set_ext_h = Hashtbl.find sigknh "set_ext" in
    let replI_h = Hashtbl.find sigknh "ReplI" in
    let replE_impred_h = Hashtbl.find sigknh "ReplE_impred" in
    let in_tm x y = Ap(Ap(TmH(in_h),x),y) in
    let repl_tm x f = Ap(Ap(TmH(repl_h),x),f) in
    let elem_q target use_rhs =
      let elem = if use_rhs then DB(0) else DB(1) in
      Lam(Set,Lam(Set,in_tm elem (tmshift 0 2 target)))
    in
    let app_elem_q fn target use_rhs =
      let elem = if use_rhs then DB(0) else DB(1) in
      Lam(Set,Lam(Set,in_tm (Ap(tmshift 0 2 fn,elem)) (tmshift 0 2 target)))
    in
    let find_inv x f g =
      let fx = Ap(tmshift 0 1 f,DB(0)) in
      let gfx = Ap(tmshift 0 1 g,fx) in
      let expected_eq =
        eq_tm Set gfx (DB(0))
      in
      let rec scan scanhyps i =
        match scanhyps with
        | All(Set,Imp(Ap(p,DB(0)),q))::r ->
           begin
             match conv q expected_eq sigdelta [] with
             | Some(_) -> Some(i,p)
             | None -> scan r (i+1)
           end
        | _::r -> scan r (i+1)
        | [] -> None
      in
      scan hyps 0
    in
    let find_domain_pred x p =
      let expected = All(Set,Imp(in_tm (DB(0)) (tmshift 0 1 x),Ap(p,DB(0)))) in
      let rec scan scanhyps i =
        match scanhyps with
        | h::r ->
           begin
             match conv h expected sigdelta [] with
             | Some(_) -> Some(i)
             | None -> scan r (i+1)
           end
        | [] -> None
      in
      scan hyps 0
    in
    match lhs, rhs with
    | Ap(Ap(TmH(rh1),Ap(Ap(TmH(rh2),x),f)),g), xrhs when rh1 = repl_h && rh2 = repl_h ->
       begin
         match conv x xrhs sigdelta [] with
         | Some(_) ->
            begin
              match find_inv x f g with
              | Some(inv_i,p) ->
                 begin
                   match find_domain_pred x p with
                   | Some(hx_i) ->
                      let left = lhs in
                      let right = rhs in
                      let inner = repl_tm x f in
                      let x1 = tmshift 0 1 x in
                      let f1 = tmshift 0 1 f in
                      let g1 = tmshift 0 1 g in
                      let inner1 = tmshift 0 1 inner in
                      let left1 = tmshift 0 1 left in
                      let y = DB(0) in
                      let y_in_left = in_tm y left1 in
                      let y_in_right = in_tm y x1 in
                      let x2 = tmshift 0 2 x in
                      let f2 = tmshift 0 2 f in
                      let g2 = tmshift 0 2 g in
                      let inner2 = tmshift 0 2 inner in
                      let z = DB(0) in
                      let yz = DB(1) in
                      let y_in_x_after_z = in_tm yz x2 in
                      let z_in_inner = in_tm z inner2 in
                      let y_eq_gz = eq_tm Set yz (Ap(g2,z)) in
                      let x3 = tmshift 0 3 x in
                      let f3 = tmshift 0 3 f in
                      let g3 = tmshift 0 3 g in
                      let w = DB(0) in
                      let z3 = DB(1) in
                      let w_in_x = in_tm w x3 in
                      let z_eq_fw = eq_tm Set z3 (Ap(f3,w)) in
                      let hpw = PPfAp(PTmAp(Hyp(hx_i+5),w),Hyp(1)) in
                      let dinv_w = PPfAp(PTmAp(Hyp(inv_i+5),w),hpw) in
                      let dgfw_in_x = PPfAp(PTmAp(dinv_w,elem_q x3 true),Hyp(1)) in
                      let dgz_in_x = PPfAp(PTmAp(Hyp(0),app_elem_q g3 x3 true),dgfw_in_x) in
                      let dy_in_x = PPfAp(PTmAp(Hyp(2),elem_q x3 true),dgz_in_x) in
                      let inner_branch = TLam(Set,PLam(w_in_x,PLam(z_eq_fw,dy_in_x))) in
                      let inner_elim =
                        PPfAp
                          (PTmAp
                             (PPfAp
                                (PTmAp(PTmAp(PTmAp(Known(replE_impred_h),x2),f2),z),
                                 Hyp(1)),
                              y_in_x_after_z),
                           inner_branch)
                      in
                      let outer_branch = TLam(Set,PLam(z_in_inner,PLam(y_eq_gz,inner_elim))) in
                      let left_sub =
                        TLam(Set,
                             PLam(y_in_left,
                                  PPfAp
                                    (PTmAp
                                       (PPfAp
                                          (PTmAp(PTmAp(PTmAp(Known(replE_impred_h),inner1),g1),y),
                                           Hyp(0)),
                                        y_in_right),
                                     outer_branch)))
                      in
                      let hpy = PPfAp(PTmAp(Hyp(hx_i+1),y),Hyp(0)) in
                      let dinv_y = PPfAp(PTmAp(Hyp(inv_i+1),y),hpy) in
                      let dfy_in_inner =
                        PPfAp
                          (PTmAp(PTmAp(PTmAp(Known(replI_h),x1),f1),y),
                           Hyp(0))
                      in
                      let dgy_in_left =
                        PPfAp
                          (PTmAp(PTmAp(PTmAp(Known(replI_h),inner1),g1),Ap(f1,y)),
                           dfy_in_inner)
                      in
                      let dy_in_left = PPfAp(PTmAp(dinv_y,elem_q left1 false),dgy_in_left) in
                      let right_sub = TLam(Set,PLam(y_in_right,dy_in_left)) in
                      Some(PPfAp(PPfAp(PTmAp(PTmAp(Known(set_ext_h),left),right),left_sub),right_sub))
                   | None -> None
                 end
              | None -> None
            end
         | None -> None
       end
    | _ -> None
  with
  | Not_found -> None
  | SearchBacktrack -> None
  | Failure(_) -> None
and repl_ext_sub_proof depth cx hyps goal =
  if depth <= 0 then None else
  try
    let repl_h = Hashtbl.find sigtmh "Repl" in
    let in_h = Hashtbl.find sigtmh "In" in
    let subq_h = Hashtbl.find sigtmh "Subq" in
    let replI_h = Hashtbl.find sigknh "ReplI" in
    let replE_impred_h = Hashtbl.find sigknh "ReplE_impred" in
    let find_pointwise x f g =
      let expected forward =
        let x1 = tmshift 0 1 x in
        let f1 = tmshift 0 1 f in
        let g1 = tmshift 0 1 g in
        let lhs, rhs =
          if forward then
            Ap(f1,DB(0)), Ap(g1,DB(0))
          else
            Ap(g1,DB(0)), Ap(f1,DB(0))
        in
        All(Set,Imp(Ap(Ap(TmH(in_h),DB(0)),x1),eq_tm Set lhs rhs))
      in
      let rec scan scanhyps i =
        match scanhyps with
        | p::r ->
           begin
             match conv p (expected true) sigdelta [] with
             | Some(_) -> Some(i,true)
             | None ->
                begin
                  match conv p (expected false) sigdelta [] with
                  | Some(_) -> Some(i,false)
                  | None -> scan r (i+1)
                end
           end
        | [] -> None
      in
      scan hyps 0
    in
    let elem_rewrite_q target use_rhs =
      let elem = if use_rhs then DB(0) else DB(1) in
      Lam(Set,Lam(Set,Ap(Ap(TmH(in_h),elem),tmshift 0 2 target)))
    in
    match goal with
    | Ap(Ap(TmH(sh),Ap(Ap(TmH(rh1),x1),f)),Ap(Ap(TmH(rh2),x2),g))
         when sh = subq_h && rh1 = repl_h && rh2 = repl_h ->
       begin
         match conv x1 x2 sigdelta [] with
         | Some(_) ->
            let source = Ap(Ap(TmH(repl_h),x1),f) in
            let target = Ap(Ap(TmH(repl_h),x2),g) in
            let y_in_source = Ap(Ap(TmH(in_h),DB(0)),tmshift 0 1 source) in
            let y_in_target = Ap(Ap(TmH(in_h),DB(0)),tmshift 0 1 target) in
            begin
              try
                let body =
                  repl_ext_sub_proof
                    (depth-1)
                    (Set::cx)
                    (y_in_source::List.map (tmshift 0 1) hyps)
                    y_in_target
                in
                begin
                  match body with
                  | Some(d) -> Some(TLam(Set,PLam(y_in_source,d)))
                  | None -> None
                end
              with
              | SearchBacktrack -> None
              | Failure(_) -> None
            end
         | None -> None
       end
    | Ap(Ap(TmH(ih),y),Ap(Ap(TmH(rh),x),g)) when ih = in_h && rh = repl_h ->
       let rec scan_source scanhyps source_i =
         match scanhyps with
         | Ap(Ap(TmH(ih2),y2),Ap(Ap(TmH(rh2),x2),f))::r when ih2 = in_h && rh2 = repl_h ->
            begin
              match conv y2 y sigdelta [], conv x2 x sigdelta [] with
              | Some(_), Some(_) ->
                 begin
                   match find_pointwise x f g with
                   | Some(point_i,point_forward) ->
                      let target = Ap(Ap(TmH(repl_h),x),g) in
                      let x1 = tmshift 0 1 x in
                      let f1 = tmshift 0 1 f in
                      let g1 = tmshift 0 1 g in
                      let y1 = tmshift 0 1 y in
                      let target1 = tmshift 0 1 target in
                      let w = DB(0) in
                      let winx = Ap(Ap(TmH(in_h),w),x1) in
                      let y_eq_fw = eq_tm Set y1 (Ap(f1,w)) in
                      let dpoint = PPfAp(PTmAp(Hyp(point_i+2),w),Hyp(1)) in
                      let dgw =
                        PPfAp
                          (PTmAp(PTmAp(PTmAp(Known(replI_h),x1),g1),w),
                           Hyp(1))
                      in
                      let dfw =
                        PPfAp
                          (PTmAp(dpoint,elem_rewrite_q target1 point_forward),
                           dgw)
                      in
                      let dy =
                        PPfAp
                          (PTmAp(Hyp(0),elem_rewrite_q target1 true),
                           dfw)
                      in
                      let branch = TLam(Set,PLam(winx,PLam(y_eq_fw,dy))) in
                      Some
                        (PPfAp
                           (PTmAp
                              (PPfAp
                                 (PTmAp(PTmAp(PTmAp(Known(replE_impred_h),x),f),y),
                                  Hyp(source_i)),
                               goal),
                            branch))
                   | None ->
                      scan_source r (source_i+1)
                 end
              | _ -> scan_source r (source_i+1)
            end
         | _::r -> scan_source r (source_i+1)
         | [] -> None
       in
       scan_source hyps 0
    | _ -> None
  with
  | Not_found -> None
  | SearchBacktrack -> None
  | Failure(_) -> None
and eq_in_elem_rewrite_proof depth cx hyps goal =
  if depth <= 0 then None else
  try
    let in_h = Hashtbl.find sigtmh "In" in
    let rewrite_q target use_rhs =
      let elem = if use_rhs then DB(0) else DB(1) in
      Lam(Set,Lam(Set,Ap(Ap(TmH(in_h),elem),tmshift 0 2 target)))
    in
    match goal with
    | Ap(Ap(TmH(ih),t),target) when ih = in_h ->
       let rec scan scanhyps i =
         match scanhyps with
         | p::r ->
            begin
              match is_eq_tm p with
              | Some(a,l,rhs) when a = Set ->
                 let try_left () =
                   match conv l t sigdelta [] with
                   | Some(_) ->
                      begin
                        try
                          let source = Ap(Ap(TmH(in_h),rhs),target) in
                          let dsource = native_aby_direct_depth true true (depth-1) cx hyps source in
                          Some(PPfAp(PTmAp(Hyp(i),rewrite_q target true),dsource))
                        with
                        | SearchBacktrack -> None
                        | Failure(_) -> None
                      end
                   | None -> None
                 in
                 let try_right () =
                   match conv rhs t sigdelta [] with
                   | Some(_) ->
                      begin
                        try
                          let source = Ap(Ap(TmH(in_h),l),target) in
                          let dsource = native_aby_direct_depth true true (depth-1) cx hyps source in
                          Some(PPfAp(PTmAp(Hyp(i),rewrite_q target false),dsource))
                        with
                        | SearchBacktrack -> None
                        | Failure(_) -> None
                      end
                   | None -> None
                 in
                 begin
                   match try_left () with
                   | Some(d) -> Some(d)
                   | None ->
                      begin
                        match try_right () with
                        | Some(d) -> Some(d)
                        | None -> scan r (i+1)
                      end
                 end
              | _ -> scan r (i+1)
            end
         | [] -> None
       in
       scan hyps 0
    | _ -> None
  with
  | Not_found -> None
  | SearchBacktrack -> None
  | Failure(_) -> None
and eq_pred_rewrite_proof depth cx hyps goal =
  if depth <= 0 then None else
  match goal with
  | Ap(pred,t) ->
     let rec scan scanhyps i =
       match scanhyps with
       | p::r ->
          begin
            match is_eq_tm p with
            | Some(a,l,rhs) ->
               let try_left () =
                 match conv l t sigdelta [] with
                 | Some(_) ->
                    begin
                      try
                        let source = Ap(pred,rhs) in
                        let dsource = native_aby_direct_depth true true (depth-1) cx hyps source in
                        let q = Lam(a,Lam(a,Ap(tmshift 0 2 pred,DB(0)))) in
                        Some(PPfAp(PTmAp(Hyp(i),q),dsource))
                      with
                      | SearchBacktrack -> None
                      | Failure(_) -> None
                    end
                 | None -> None
               in
               let try_right () =
                 match conv rhs t sigdelta [] with
                 | Some(_) ->
                    begin
                      try
                        let source = Ap(pred,l) in
                        let dsource = native_aby_direct_depth true true (depth-1) cx hyps source in
                        let q = Lam(a,Lam(a,Ap(tmshift 0 2 pred,DB(1)))) in
                        Some(PPfAp(PTmAp(Hyp(i),q),dsource))
                      with
                      | SearchBacktrack -> None
                      | Failure(_) -> None
                    end
                 | None -> None
               in
               begin
                 match try_left () with
                 | Some(d) -> Some(d)
                 | None ->
                    match try_right () with
                    | Some(d) -> Some(d)
                    | None -> scan r (i+1)
               end
            | None -> scan r (i+1)
          end
       | [] -> None
     in
     scan hyps 0
  | _ -> None
and find_ex_intro depth cx hyps a q i =
  let rec find_ex_intro_rec scancx i =
    match scancx with
    | b::r ->
       let try_rest () = find_ex_intro_rec r (i+1) in
       if b = a then
         begin
           let w = DB(i) in
           try
             let dq = native_aby_direct_depth true true (depth-1) cx hyps (Ap(q,w)) in
             let dq = pfshift 0 1 (pftmshift 0 1 dq) in
             Some(TLam(Prop,PLam(All(a,Imp(Ap(tmshift 0 2 q,DB(0)),DB(1))),PPfAp(PTmAp(Hyp(0),tmshift 0 1 w),dq))))
           with
           | SearchBacktrack -> try_rest ()
           | Failure(_) -> try_rest ()
         end
       else
         try_rest ()
    | [] -> None
  in
  find_ex_intro_rec cx i
and find_ex_elim_hyp depth cx hyps goal i =
  let rec find_ex_elim_hyp_rec scanhyps i =
    match scanhyps with
    | p::r ->
       begin
         match ex_elim_proof (depth-1) cx hyps (Hyp(i)) p goal with
         | Some(d) -> Some(d)
         | None -> find_ex_elim_hyp_rec r (i+1)
       end
    | [] -> None
  in
  find_ex_elim_hyp_rec hyps i
and ex_elim_proof depth cx hyps d p goal =
  if depth <= 0 then None else
  match p with
  | Ap(TpAp(TmH(h),a),q) when h = egal_ex_id ->
     begin
       try
         let qx = Ap(tmshift 0 1 q,DB(0)) in
         let branch_goal = tmshift 0 1 goal in
         let branch_hyps = qx::List.map (tmshift 0 1) hyps in
         let branch = native_aby_direct_depth true true (depth-1) (a::cx) branch_hyps branch_goal in
         Some(PPfAp(PTmAp(d,goal),TLam(a,PLam(qx,branch))))
       with
       | SearchBacktrack -> None
       | Failure(_) -> None
     end
  | _ -> None
and find_or_elim_hyp depth cx hyps goal i =
  let rec find_or_elim_hyp_rec scanhyps i =
    match scanhyps with
    | p::r ->
       begin
         match or_elim_proof (depth-1) cx hyps (Hyp(i)) p goal with
         | Some(d) -> Some(d)
         | None -> find_or_elim_hyp_rec r (i+1)
       end
    | [] -> None
  in
  find_or_elim_hyp_rec hyps i
and prove_or_branch depth cx hyps p goal =
  if depth <= 0 then raise SearchBacktrack else
  match p with
  | Ap(Ap(TmH(h),_),_) when h = egal_or_id ->
     begin
       match or_elim_proof (depth-1) cx (p::hyps) (Hyp(0)) p goal with
       | Some(d) -> d
       | None -> raise SearchBacktrack
     end
  | _ -> native_aby_direct_depth true false (depth-1) cx (p::hyps) goal
and or_elim_proof depth cx hyps d p goal =
  if depth <= 0 then None else
  match p with
  | Ap(Ap(TmH(h),a),b) when h = egal_or_id ->
     begin
       try
         let da = prove_or_branch (depth-1) cx hyps a goal in
         let db = prove_or_branch (depth-1) cx hyps b goal in
         Some(PPfAp(PPfAp(PTmAp(d,goal),PLam(a,da)),PLam(b,db)))
       with
       | SearchBacktrack -> None
       | Failure(_) -> None
     end
  | All(Prop,Imp(Imp(a,DB(0)),Imp(Imp(b,DB(0)),DB(0)))) ->
     begin
       try
         let a0 = tmsubst a 0 goal in
         let b0 = tmsubst b 0 goal in
         let da = prove_or_branch (depth-1) cx hyps a0 goal in
         let db = prove_or_branch (depth-1) cx hyps b0 goal in
         Some(PPfAp(PPfAp(PTmAp(d,goal),PLam(a0,da)),PLam(b0,db)))
       with
       | SearchBacktrack -> None
       | Failure(_) -> None
     end
  | _ ->
     let p_hn = fst (headnorm p sigdelta []) in
     if p_hn <> tm_beta_eta_norm p then
       or_elim_proof (depth-1) cx hyps d p_hn goal
     else
       None
and find_imp_elim_hyp allow_or depth cx hyps goal i =
  let rec find_imp_elim_hyp_rec scanhyps i =
    match scanhyps with
    | p::r ->
       begin
         match apply_imp_chain allow_or (depth-1) cx hyps (Hyp(i)) p goal with
         | Some(d) -> Some(d)
         | None ->
            match and_imp_elim_proof allow_or (depth-1) cx hyps (Hyp(i)) p goal with
            | Some(d) -> Some(d)
            | None -> find_imp_elim_hyp_rec r (i+1)
       end
    | [] -> None
  in
  find_imp_elim_hyp_rec hyps i
and and_imp_elim_proof allow_or depth cx hyps d p goal =
  if depth <= 0 then None else
  match apply_imp_chain allow_or (depth-1) cx hyps d p goal with
  | Some(d) -> Some(d)
  | None ->
     match p with
     | Ap(Ap(TmH(h),a),b) when h = egal_and_id ->
        begin
          match and_elim_proof sigdelta d p a with
          | Some(da) ->
             begin
               match and_imp_elim_proof allow_or (depth-1) cx hyps da a goal with
               | Some(d) -> Some(d)
               | None ->
                  begin
                    match and_elim_proof sigdelta d p b with
                    | Some(db) -> and_imp_elim_proof allow_or (depth-1) cx hyps db b goal
                    | None -> None
                  end
             end
          | None ->
             begin
               match and_elim_proof sigdelta d p b with
               | Some(db) -> and_imp_elim_proof allow_or (depth-1) cx hyps db b goal
               | None -> None
             end
        end
     | Ap(Ap(TmH(h),a),b) when h = egal_iff_id ->
        let p_as_and = Ap(Ap(TmH(egal_and_id),Imp(a,b)),Imp(b,a)) in
        and_imp_elim_proof allow_or (depth-1) cx hyps d p_as_and goal
     | _ -> None
and find_known_elim allow_or depth cx hyps goal =
  let rec find_known_elim_rec knowns =
    match knowns with
    | (p,d)::r ->
       begin
         match known_iff_elim allow_or (depth-1) cx hyps d p goal with
         | Some(d) -> Some(d)
         | None ->
            match apply_imp_chain allow_or (depth-1) cx hyps d p goal with
            | Some(d) -> Some(d)
            | None -> find_known_elim_rec r
       end
    | [] -> None
  in
  find_known_elim_rec !native_aby_knowns
and known_iff_elim allow_or depth cx hyps d p goal =
  if depth <= 0 then None else
  match p with
  | All(a,b) ->
     let rec try_terms terms =
       match terms with
       | w::r ->
          begin
            match known_iff_elim allow_or (depth-1) cx hyps (PTmAp(d,w)) (tmsubst b 0 w) goal with
            | Some(d) -> Some(d)
            | None -> try_terms r
          end
       | [] -> None
     in
     try_terms (native_aby_inst_terms cx hyps goal a)
  | Ap(Ap(TmH(h),a),b) when h = egal_iff_id ->
     let p_as_and = Ap(Ap(TmH(egal_and_id),Imp(a,b)),Imp(b,a)) in
     let try_forward () =
       match conv b goal sigdelta [] with
       | Some(_) ->
          begin
            match and_elim_proof sigdelta d p_as_and (Imp(a,b)) with
            | Some(dab) ->
               begin
                 try
                   let da = native_aby_direct_depth true allow_or (depth-1) cx hyps a in
                   Some(PPfAp(dab,da))
                 with
                 | SearchBacktrack -> None
                 | Failure(_) -> None
               end
            | None -> None
          end
       | None -> None
     in
     let try_backward () =
       match conv a goal sigdelta [] with
       | Some(_) ->
          begin
            match and_elim_proof sigdelta d p_as_and (Imp(b,a)) with
            | Some(dba) ->
               begin
                 try
                   let db = native_aby_direct_depth true allow_or (depth-1) cx hyps b in
                   Some(PPfAp(dba,db))
                 with
                 | SearchBacktrack -> None
                 | Failure(_) -> None
               end
            | None -> None
          end
       | None -> None
     in
     begin
       match try_forward () with
       | Some(d) -> Some(d)
       | None -> try_backward ()
     end
  | _ -> None
and apply_imp_chain allow_or depth cx hyps d p goal =
  if depth <= 0 then None else
  match p with
  | All(a,b) ->
     let rec try_terms terms =
       match terms with
       | w::r ->
          begin
            match apply_imp_chain allow_or (depth-1) cx hyps (PTmAp(d,w)) (tmsubst b 0 w) goal with
            | Some(d) -> Some(d)
            | None -> try_terms r
          end
       | [] -> None
     in
     try_terms (native_aby_inst_terms cx hyps goal a)
  | Ap(Ap(TmH(h),a),b) when h = egal_iff_id ->
     let p_as_and = Ap(Ap(TmH(egal_and_id),Imp(a,b)),Imp(b,a)) in
     let try_forward () =
       match and_elim_proof sigdelta d p_as_and (Imp(a,b)) with
       | Some(dab) -> apply_imp_chain allow_or depth cx hyps dab (Imp(a,b)) goal
       | None -> None
     in
     let try_backward () =
       match and_elim_proof sigdelta d p_as_and (Imp(b,a)) with
       | Some(dba) -> apply_imp_chain allow_or depth cx hyps dba (Imp(b,a)) goal
       | None -> None
     in
     begin
       match try_forward () with
       | Some(d) -> Some(d)
       | None -> try_backward ()
     end
  | Ap(TmH(h),a) when h = egal_not_id ->
     apply_imp_chain allow_or depth cx hyps d (Imp(a,TmH(egal_false_id))) goal
  | Ap(Ap(TpAp(TmH(h),a),x),y) when h = egal_neq_id ->
     apply_imp_chain allow_or depth cx hyps d (Imp(eq_tm a x y,TmH(egal_false_id))) goal
  | Imp(a,b) ->
     begin
       try
         let da = native_aby_direct_depth true allow_or (depth-1) cx hyps a in
         apply_imp_chain allow_or (depth-1) cx hyps (PPfAp(d,da)) b goal
       with
       | SearchBacktrack -> None
       | Failure(_) -> None
     end
  | _ ->
     match is_eq_tm p with
     | Some(_) ->
        begin
          match conv p goal sigdelta [] with
          | Some(_) -> Some(d)
          | None -> None
        end
     | None ->
        let p_hn = fst (headnorm p sigdelta []) in
        if p_hn <> tm_beta_eta_norm p then
          apply_imp_chain allow_or (depth-1) cx hyps d p_hn goal
        else
          match conv p goal sigdelta [] with
          | Some(_) -> Some(d)
          | None -> None

let native_aby_direct cx hyps goal =
  native_aby_direct_depth true true 16 cx hyps goal

let native_aby_named_knowns xl =
  let rec native_aby_named_knowns_rec xl acc =
    match xl with
    | x::r when x = "-" -> native_aby_named_knowns_rec r acc
    | x::r ->
       begin
         try
           let h = Hashtbl.find sigknh x in
           let (i,p) = Hashtbl.find sigdelta h in
           if i = 0 then
             native_aby_named_knowns_rec r ((p,Known(h))::acc)
           else
             native_aby_named_knowns_rec r acc
         with Not_found -> native_aby_named_knowns_rec r acc
       end
    | [] -> List.rev acc
  in
  native_aby_named_knowns_rec xl []

let native_aby_reconstruct claimtm cxtm cxpf xl =
  if !vampireabyqualifying then None
  else
  let cx = List.map (fun (_, (a, _)) -> a) cxtm in
  let hyps = List.map (fun (_, p) -> p) cxpf in
  native_aby_knowns := native_aby_named_knowns xl;
  let check_candidate d =
    match check_propofpf sigdelta sigtmof cx hyps d claimtm [] with
    | Some(_) -> Some(d)
    | None -> None
  in
  let try_direct () =
    try
      check_candidate (native_aby_direct cx hyps claimtm)
    with
    | SearchBacktrack -> None
    | Failure(_) -> None
  in
  let try_megaauto () =
    try
      check_candidate (megaauto "" "+" cx hyps claimtm)
    with
    | SearchLimit -> None
    | SearchBacktrack -> None
    | Failure(_) -> None
  in
  match try_direct () with
  | Some(d) -> Some(d)
  | None -> if !vampireabynativestrict then None else try_megaauto ()

let read_pfg_supp fn =
  let f = open_in fn in
  try
    while true do
      let l = input_line f in
      let ln = String.length l in
      if ln = 70 then
        if String.sub l 0 6 = "Param:" then
          Hashtbl.replace pfgsuppparam (String.sub l 6 64) ()
        else if String.sub l 0 6 = "Known:" then
          Hashtbl.replace pfgsuppknown (String.sub l 6 64) ()
        else
          ()
      else if ln = 68 then
        if String.sub l 0 4 = "Def:" then
          Hashtbl.replace pfgsuppdef (String.sub l 4 64) ()
        else if String.sub l 0 4 = "Thm:" then
          Hashtbl.replace pfgsuppthm (String.sub l 4 64) ()
        else
          ()
      else if ln = 69 && String.sub l 0 5 = "Conj:" then
        Hashtbl.replace pfgsuppthm (String.sub l 5 64) ()
      else
        ()
    done
  with End_of_file ->
    close_in f

let setup_megawiki root =
  ensure_directory root;
  let ddir = Filename.concat root "d" in
  let tdir = Filename.concat root "t" in
  let cdir = Filename.concat root "c" in
  ensure_directory ddir;
  ensure_directory tdir;
  ensure_directory cdir;
  { ddir = ddir; tdir = tdir; cdir = cdir }

let close_out_noerr ch =
  try close_out ch with _ -> ()

let remove_file_if_exists path =
  if Sys.file_exists path then Sys.remove path

let append_megawiki_legend mw hash name =
  let ch = open_out_gen [Open_creat;Open_text;Open_append] 0o644 (Filename.concat (Filename.dirname mw.ddir) "legend") in
  output_string ch hash;
  output_char ch ' ';
  output_string ch name;
  output_char ch '\n';
  close_out ch

let rec find_substring_from s sub i =
  let ls = String.length s in
  let lsub = String.length sub in
  if i + lsub > ls then
    None
  else if String.sub s i lsub = sub then
    Some i
  else
    find_substring_from s sub (i+1)

let theorem_statement_only_html frag =
  match find_substring_from frag "<div id='pf" 0 with
  | Some i -> String.sub frag 0 i ^ "</div></div>\n"
  | None -> frag

let megawiki_theorem_exists pfgahv =
  match !megawiki with
  | Some mw ->
      Sys.file_exists (Filename.concat mw.tdir (Hash.hashval_hexstring pfgahv))
  | None -> false

let finalize_megawiki_theorem proved =
  match !megawiki,!megawiki_thm with
  | Some mw,Some st ->
      close_out_noerr st.tmpout;
      let tpath = Filename.concat mw.tdir st.hash in
      let cpath = Filename.concat mw.cdir st.hash in
      begin
        if proved then
          begin
            remove_file_if_exists cpath;
            if Sys.file_exists tpath then
              remove_file_if_exists st.tempfile
            else if Sys.file_exists st.tempfile then
              begin
                Sys.rename st.tempfile tpath;
                append_megawiki_legend mw st.hash st.name
              end
          end
        else
          begin
            if Sys.file_exists st.tempfile then
              begin
                if Sys.file_exists tpath || Sys.file_exists cpath then
                  Sys.remove st.tempfile
                else
                  begin
                    let ch = open_out cpath in
                    output_string ch st.statement_html;
                    close_out ch;
                    Sys.remove st.tempfile;
                    append_megawiki_legend mw st.hash st.name;
                  end
              end
          end;
      end;
      megawiki_thm := None
  | _,Some st ->
      close_out_noerr st.tmpout;
      remove_file_if_exists st.tempfile;
      megawiki_thm := None
  | _,None -> ()

(*** special cases so that the certain tactics get activated ***)
let activate_special_knowns h =
  if h = !expolyI then
    begin
      expolyIknown := true;
      if !verbosity > 50 then (Printf.printf "Activated expolyI, so that witness tactic can now be used.\n"; flush stdout);
    end;;

(*** I could make this more general, but I won't for now. ***)
let extract_exclaim m =
  match m with
  | Ap(TpAp(TmH(e),etp),ep) when e = !expoly -> (etp,ep)
  | _ -> raise Not_found

let add_sigdelta h (i,m) =
  let m = tm_beta_eta_norm m in
  match m with
  | TmH(_) -> ()
  | TpAp(TmH(_),TpVar(0)) -> ()
  | TpAp(TpAp(TmH(_),TpVar(0)),TpVar(1)) -> ()
  | TpAp(TpAp(TpAp(TmH(_),TpVar(0)),TpVar(1)),TpVar(2)) -> ()
  | _ -> Hashtbl.add sigdelta h (i,m)

(*** Output docitems to the signature file, changing theorems to axioms ***)
let outtosigfile soc ditem =
  let outc s = output_char soc s in
  let outs s = output_string soc s in
  let outi i = Printf.fprintf soc "%d" i in
  let outl a = output_ltree soc a in
  let outasckd asck =
    begin
      match asck with
      | AscTp -> outs " : ";
      | AscSet -> outs " :e ";
      | AscSubeq -> outs " c= ";
    end;		    
  in
  begin
    match ditem with
    | Section(x) ->
	outs ("Section " ^ x ^ ".\n")
    | End(x) ->
	outs ("End " ^ x ^ ".\n")
    | VarDecl(xl,asck,a) ->
	outs "Variable";
	List.iter (fun x -> outc ' '; outs x) xl;
	outasckd asck;
	outl a;
	outc '.';
	outc '\n';
    | HypDecl(x,a) ->
	outs ("Hypothesis " ^ x ^ " : ");
	outl a;
	outc '.';
	outc '\n';
    | LetDecl(x,None,b) ->
	outs ("Let " ^ x ^ " := ");
	outl b;
	outc '.';
	outc '\n';
    | LetDecl(x,Some(asck,a),b) ->
	outs "Let ";
	outs x;
	outasckd asck;
	outl a;
	outs " := ";
	outl b;
	outc '.';
	outc '\n';
    | PostInfixDecl(x,a,p,Postfix) ->
	outs "Postfix ";
	outs x;
	outc ' ';
	outi p;
	outs " := ";
	outl a;
	outs ".\n";
    | PostInfixDecl(x,a,p,InfixNone) ->
	outs "Infix ";
	outs x;
	outc ' ';
	outi p;
	outs " := ";
	outl a;
	outs ".\n";
    | PostInfixDecl(x,a,p,InfixLeft) ->
	outs "Infix ";
	outs x;
	outc ' ';
	outi p;
	outs " left ";
	outs " := ";
	outl a;
	outs ".\n";
    | PostInfixDecl(x,a,p,InfixRight) ->
	outs "Infix ";
	outs x;
	outc ' ';
	outi p;
	outs " right ";
	outs " := ";
	outl a;
	outs ".\n";
    | PrefixDecl(x,a,p) ->
	outs "Prefix ";
	outs x;
	outc ' ';
	outi p;
	outs " := ";
	outl a;
	outs ".\n";
    | BinderDecl(plus,comma,x,a,bo) ->
	outs "Binder";
	if plus then outs "+ " else outc ' ';
	outs x;
	if comma then outs " , := " else outs " => := ";
	outl a;
	begin
	  match bo with
	  | Some(b) -> outs " ; "; outl b
	  | None -> ()
	end;
	outs ".\n"
    | UnicodeDecl(x,yl) ->
	outs "(* Unicode ";
	outs x;
	List.iter (fun y ->
	  outs " \"";
	  outs y;
	  outs "\"")
	  yl;
	outs " *)\n"
    | SubscriptDecl(x) ->
	outs "(* Subscript ";
	outs x;
	outs " *)\n"
    | SuperscriptDecl(x) ->
	outs "(* Superscript ";
	outs x;
	outs " *)\n"
    | NotationDecl(x,yl) ->
	outs "Notation ";
	outs x;
	List.iter (fun y -> outc ' '; outs y) yl;
	outs ".\n";
    | ParamHash(x,h,None) ->
	outs "(* Parameter ";
	outs x;
	outc ' ';
	outc '"';
	outs h;
	outc '"';
	outc ' ';
	outs "*)\n";
    | ParamHash(x,h,Some(k)) ->
	outs "(* Parameter ";
	outs x;
	outc ' ';
	outc '"';
	outs h;
	outc '"';
	outc ' ';
	outc '"';
	outs k;
	outc '"';
	outc ' ';
	outs "*)\n";
    | ParamDecl(x,a) ->
	outs "Parameter ";
	outs x;
	outs " : ";
	outl a;
	outs ".\n";
    | DefDecl(x,None,b) ->
	outs "Definition ";
	outs x;
	outs " := ";
	outl b;
	outs ".\n";
    | DefDecl(x,Some a,b) ->
	outs "Definition ";
	outs x;
	outs " : ";
	outl a;
	outs " := ";
	outl b;
	outs ".\n";
    | AxDecl(x,a) ->
	outs "Axiom ";
	outs x;
	outs " : ";
	outl a;
	outs ".\n";
    | ThmDecl(_,x,a) -> (*** Theorems are axioms in the signature. ***)
	outs "Axiom ";
	outs x;
	outs " : ";
	outl a;
	outs ".\n";
    | _ -> ()
  end

let skip_to_line_char c li1 ch1 li2 ch2 =
  try
    while (!li1 < li2) do
      ch1 := 0;
      let z = input_char c in
      if z = '\n' then incr li1;
    done;
    while (!ch1 < ch2) do
      ignore (input_char c);
      incr ch1
    done
  with End_of_file -> () (*** this probably shouldn't happen, but if it does, just stop reading the file ***)

let buffer_to_line_char c b li1 ch1 li2 ch2 =
  try
    while (!li1 < li2) do
      ch1 := 0;
      let z = input_char c in
      Buffer.add_char b z;
      if z = '\n' then incr li1;
    done;
    while (!ch1 < ch2) do
      let z = input_char c in
      Buffer.add_char b z;
      incr ch1
    done
  with End_of_file -> () (*** this probably shouldn't happen, but if it does, just stop reading the file ***)

let ctxtp = ref []
let ctxtm = ref []
let ctxpf = ref []

let html_context () =
  (List.map (fun (x,_) -> x) !ctxpf) @ (List.map (fun (x,_) -> x) !ctxtm) @ !ctxtp

let render_docitem_html_fragment cx ditem =
  let fn = Filename.temp_file "megalodon_docitem_" ".htmlfrag" in
  let cleanup () =
    try Sys.remove fn with _ -> ()
  in
  try
    let ch = open_out fn in
    output_docitem_html cx ch ditem sigtmh sigknh;
    close_out ch;
    let c = open_in fn in
    let n = in_channel_length c in
    let s = really_input_string c n in
    close_in c;
    cleanup ();
    s
  with e ->
    cleanup ();
    raise e

let pftac_html_channels () =
  let cl = ref [] in
  begin
    match !html with
    | Some hc ->
       if not !includingsigfile && (not !htmlonlypfgsupp || !supported) then
         cl := hc::!cl
    | None -> ()
  end;
  begin
    match !megawiki_thm with
    | Some st -> cl := st.tmpout::!cl
    | None -> ()
  end;
  List.rev !cl

let tparclos = ref (fun a -> a)
let tmallclos = ref (fun m -> m)
let tmlamclos = ref (fun m -> m)
let pflamclos = ref (fun d -> d)
let aptmloc = ref (fun m cxtp cxtm -> m)
let appfloc = ref (fun d cxtp cxtm cxpf -> d)
let secstack = ref []
let popfn = ref (fun () -> ())

let laststructaction = ref 0;;

let megaauto_set_item h d =
  if h = "9db634daee7fc36315ddda5f5f694934869921e9c5f55e8b25c91c0a07c5cbec" then (** ordsucc **)
    begin
      setordsucc := Some(h);
      let h1 = tm_id (Ap(TmH(h),Prim(2))) sigtmof sigdelta in
      set1 := Some(h1);
      let h2 = tm_id (Ap(TmH(h),TmH(h1))) sigtmof sigdelta in
      set2 := Some(h2)
    end
  else if h = "b260cb5327df5c1f762d4d3068ddb3c7cc96a9cccf7c89cee6abe113920d16f1" then (** setsum/pair **)
    setsum := Some(h)
  else if h = "93592da87a6f2da9f7eb0fbd449e0dc4730682572e0685b6a799ae16c236dcae" then (** lam/Sigma **)
    setlambda := Some(h)
  else if h = "ecef5cea93b11859a42b1ea5e8a89184202761217017f3a5cdce1b91d10b34a7" && d then (** setprod **)
    setprod := Some(h)
  else if h = "58c1782da006f2fb2849c53d5d8425049fad551eb4f8025055d260f0c9e1fe40" then (** ap **)
    setap := Some(h)
  else if h = "8ab5fa18b3cb4b4b313a431cc37bdd987f036cc47f175379215f69af5977eb3b" then (** Pi **)
    setPi := Some(h)
  else if h = "fcd77a77362d494f90954f299ee3eb7d4273ae93d2d776186c885fc95baa40dc" && d then (** setexp **)
    setexp := Some(h)

let megaauto_set_known h =
  if h = "4dcf737d976ab59871f178ab4227edffb26181c236613caeb68c84de8f2e6aa1" then
    known_In_0_2 := Some(h)
  else if h = "b28b8818076ea2727fe37ccdc19db7910186e7991e3cd809d9bd88239f294936" then
    known_In_1_2 := Some(h)
  else if h = "037887d4c129ed2b2fa3e5f38118106ab9d3677e677e927197774264a221a83e" then
    known_tupleI0 := Some(h)
  else if h = "4b42b19620bd13f38596de6607fccc7b23ef8c6ed2a71e396055f290a6d75265" then
    known_tupleI1 := Some(h)
  else if h = "30940631e6ea9dd2e197436d1254b1a8d7d9087b0d6df24ed44090a81c91efef" then
    known_tuple0_setsum := Some(h)
  else if h = "02c877b50d6e337679aa91261e3c90c651ccef333d0318a0d5dd2735af5f37ba" then
    known_tuple1_setsum := Some(h)
  else if h = "8ad8ee9f2a2cceb15dc4d629f57caaf70a3ef361eb59f77fe6523c202000d9e8" then
    known_tuple_2_0_eq := Some(h)
  else if h = "494f183d032dc85055f2fcc389f025ec799bf85f978311eac319162a5c3c1ae8" then
    known_tuple_2_1_eq := Some(h)
  else if h = "2553ebe05147c51d42ad34303cd2b9bcfe20abd60f990923124e40051ba30fbf" then
    known_tuple_2_Sigma := Some(h)
  else if h = "5385a6f08cba961a8f90f2e36a2f7d49681349aec6db4e85249a481e5be48899" then
    known_tuple_2_setprod := Some(h)
  else if h = "ebb9bad843b554c6cd9c373bd2fb7dd8b30c1a3fbb10a4018fafd80db6caaaee" then
    known_tuple_2_eta := Some(h)
  else if h = "73d7865ec772f43295363850120c05f9e72b0466bd3af5828a60b87caf35f70a" then
    known_ap0_Sigma := Some(h)
  else if h = "d4c92acb68a5b835371527eab3ea8ddb1c122948915729172786e2d04b552ad3" then
    known_ap1_Sigma := Some(h)
  else if h = "a00be5d41e8522ab870b586366e81c4fd66f8fb2ca0a74e27018431d280a7fbb" then
    known_tuple_Sigma_eta := Some(h)
  else if h = "c98183df697f6c43af2633457df05e325bcd6e757b0eef980ed1fa53febad476" then
    known_lam_ext := Some(h)
  else if h = "7ab4c6697df228e0723c27c62bb05e611b05b2215b151c2507aab35b4ee34676" then
    known_lam_Pi := Some(h)
  else if h = "0fc03e3865b6f7cd7e469e8661923dc1edd845b81ec12c9dd8728082d51ed83b" then
    known_ap_Pi := Some(h)
  else if h = "3b9b4b76541e3d742c0ccd9247bf93c028026783cdf1360b09677bdbfd191f7c" then
    known_beta := Some(h)
  else if h = "73fa526ffdb4fe1b47297609c1b8558ce7ee058c64e17b285de72ae0a78e2103" then
    known_Pi_ext := Some(h)
  else if h = "a87285d54bb15d7ad174232d02bcf414291aa8cf12bdae3ba6a7d97fcfef591f" then
    known_Pi_eta := Some(h)
  else if h = "c1253491187dd3685e59eca2206b98305093ded6398e1deec69a95b81adc2515" then
    known_Pi_cod_ext := Some(h)

let make_opaque x =
  try
    let xh = Hashtbl.find sigtmh x in
    let m = Hashtbl.find sigdelta xh in
    Hashtbl.add sigdelta_opaque xh m;
    Hashtbl.remove sigdelta xh;
  with Not_found ->
    Printf.printf "WARNING: %s was not transparent, so not made opaque.\n" x

let make_transparent x =
  try
    let xh = Hashtbl.find sigtmh x in
    let m = Hashtbl.find sigdelta_opaque xh in
    Hashtbl.add sigdelta xh m;
    Hashtbl.remove sigdelta_opaque xh;
  with Not_found ->
    Printf.printf "WARNING: %s was not opaque, so not made transparent.\n" x
  
let evaluate_docitem_1 ditem =
  begin
    match !sigoutfile with
    | Some soc -> outtosigfile soc ditem
    | None -> ()
  end;
  match ditem with
  | Author(x,yl) ->
      authors := !authors @ (x::yl);
      begin
	List.iter
	  (fun z ->
	    if !sqlout then
	      begin
		match !mainfilehash with
		| Some docsha ->
		    if not !presentationonly then (Printf.printf "INSERT INTO `docauthor` (`docsha`,`docauthorname`) VALUES ('%s',\"%s\");\n" docsha (String.escaped z));
		| None -> ()
	      end)
	  (x::yl);
      end
  | Title(x) ->
      begin
	match !title with
	| None -> title := Some(x);
	    if !sqlout then
	      begin
		match !mainfilehash with
		| Some docsha ->
		    if not !presentationonly then (Printf.printf "INSERT INTO `doc` (`docsha`,`docname`,`doctitle`,`dockind`,`docreleaseorder`,`docreleasedate`,`docstatus`) VALUES ('%s','%s',\"%s\",'putkind',1,'putrdate','s');\n" docsha Sys.argv.((Array.length Sys.argv) - 1) (String.escaped x));
		| None -> ()
	      end;
	| Some _ -> raise (Failure("Title can only be declared once"))
      end
  | ShowProofTerms(b) -> showproofterms := b
  | Salt(x) -> salt := Some x
  | Opaque (xl) -> List.iter make_opaque xl
  | Transparent (xl) -> List.iter make_transparent xl
  | Treasure(x) ->
      treasure := Some x;
  | Section(x) ->
     begin
       secstack := (x,!popfn,!aptmloc,!appfloc,!sigtm,!sigpf)::!secstack;
       sigtm := Hashtbl.copy !sigtm;
       popfn := (fun () -> ());
     end
  | End(x) ->
      begin
	match !secstack with
	| ((y,f,atl,apl,st,sp)::cs) when x = y ->
	    begin
	      !popfn ();
	      popfn := f;
	      aptmloc := atl;
	      appfloc := apl;
	      sigtm := st;
	      sigpf := sp;
	      secstack := cs
	    end
	| ((y,f,atl,apl,stl,spl)::_) -> raise (Failure("Section " ^ y ^ " cannot be ended with End " ^ x))
	| [] -> raise (Failure("No Section To End"))
      end
  | VarDecl(xl,AscTp,NaL "SType") -> (** Type variable **)
      begin
	match (!ctxtp,!ctxtm,!ctxpf) with
	| ([],[],[]) ->
	    ctxtp := xl;
	    if (List.length !ctxtp > 6) then raise (Failure "More than 6 type variables are not allowed.");
	    List.iter (fun x ->
	      let prevaptmloc = !aptmloc in
	      let prevappfloc = !appfloc in
	      aptmloc := (fun m cxtp cxtm -> TpAp(prevaptmloc m cxtp cxtm,tplookup cxtp x));
	      appfloc := (fun d cxtp cxtm cxpf -> PTpAp(prevappfloc d cxtp cxtm cxpf,tplookup cxtp x)))
	      xl;
	    let popfnnow = !popfn in
	    popfn := (fun () -> handlepolysnow (); ctxtp := []; popfnnow ())
	| _ ->
	    raise (Failure "Type variables can only be declared when the context is empty.")
      end
  | VarDecl(xl,AscTp,a) -> (** Ordinary variable **)
      let a = ltree_to_atree a in
      let atp = extract_tp a !ctxtp in
      let prevctxtm = !ctxtm in
      let prevctxpf = !ctxpf in
      let prevtparclos = !tparclos in
      let prevtmallclos = !tmallclos in
      let prevtmlamclos = !tmlamclos in
      let prevpflamclos = !pflamclos in
      ctxtm := (List.map (fun x -> (x,(atp,None))) (List.rev xl)) @ prevctxtm;
      let xln = List.length xl in
      ctxpf := (List.map (fun (y,p) -> (y,tmshift 0 xln p)) prevctxpf); (*** shift the hyp context to account for the fresh vars on the var context ***)
      List.iter (fun x ->
	let prevaptmloc = !aptmloc in
	let prevappfloc = !appfloc in
	aptmloc := (fun m cxtp cxtm -> Ap(prevaptmloc m cxtp cxtm,tmlookup cxtm x));
	appfloc := (fun d cxtp cxtm cxpf -> PTmAp(prevappfloc d cxtp cxtm cxpf,tmlookup cxtm x)))
	xl;
      tparclos := (fun a -> prevtparclos (List.fold_right (fun x b -> Ar(atp,b)) xl a));
      tmallclos := (fun m -> prevtmallclos (List.fold_right (fun x n -> All(atp,n)) xl m));
      tmlamclos := (fun m -> prevtmlamclos (List.fold_right (fun x n -> Lam(atp,n)) xl m));
      pflamclos := (fun d -> prevpflamclos (List.fold_right (fun x e -> TLam(atp,e)) xl d));
      let popfnnow = !popfn in
      popfn := (fun () -> ctxtm := prevctxtm; ctxpf := prevctxpf; tparclos := prevtparclos; tmallclos := prevtmallclos; tmlamclos := prevtmlamclos; pflamclos := prevpflamclos; popfnnow ())
  | VarDecl(xl,AscSet,a) -> (** Variable/Hyp combo, I might allow this later **)
      raise (Failure("Variables must be ascribed a type, not a set"))
  | VarDecl(xl,AscSubeq,a) -> (** Variable/Hyp combo, I might allow this later **)
      raise (Failure("Variables must be ascribed a type, not a set"))
  | HypDecl(x,a) -> (** declare a hypothesis, put into ctxpf, add removal to popfn, update appfloc **)
      let a = ltree_to_atree a in
      let atm = check_tm a Prop !polytm sigtmof !sigtm !ctxtp !ctxtm in
      let prevappfloc = !appfloc in
      let prevtmallclos = !tmallclos in
      let prevpflamclos = !pflamclos in
      let prevctxpf = !ctxpf in
      ctxpf := (x,atm)::prevctxpf;
      appfloc := (fun d cxtp cxtm cxpf -> PPfAp(prevappfloc d cxtp cxtm cxpf,pflookup cxpf x));
      tmallclos := (fun m -> prevtmallclos (Imp(atm,m)));
      pflamclos := (fun d -> prevpflamclos (PLam(atm,d)));
      let popfnnow = !popfn in
      popfn := (fun () -> ctxpf := prevctxpf; tmallclos := prevtmallclos; pflamclos := prevpflamclos; popfnnow ())
  | LetDecl(x,None,b) -> (** add (x,atp[extracted from btm],btm) to ctxtm, add removal to popfn **)
      (*** Note: Let variables do not correspond to de Bruijn indices. There need be no shifting of hypotheses. ***)
      let b = ltree_to_atree b in
      let (btm,btp) = extract_tm b !polytm sigtmof !sigtm !ctxtp !ctxtm in
      let prevctxtm = !ctxtm in
      ctxtm := (x,(btp,Some btm))::prevctxtm;
      let popfnnow = !popfn in
      popfn := (fun () -> ctxtm := prevctxtm; popfnnow ())
  | LetDecl(x,Some (AscTp,a),b) when a = NaL "Type" ->
     let b = ltree_to_atree b in
     let btp = extract_tp b !ctxtp in
     Hashtbl.add tpabbrev x btp
  | LetDecl(x,Some (AscTp,a),b) -> (** add (x,atp,btm) to ctxtm, add removal to popfn **)
      let a = ltree_to_atree a in
      let b = ltree_to_atree b in
      let btp = extract_tp a !ctxtp in
      let btm = check_tm b btp !polytm sigtmof !sigtm !ctxtp !ctxtm in
      let prevctxtm = !ctxtm in
      ctxtm := (x,(btp,Some btm))::prevctxtm;
      let popfnnow = !popfn in
      popfn := (fun () -> ctxtm := prevctxtm; popfnnow ())
  | LetDecl(x,Some (_,a),b) -> (*** I doubt I will allow this later since it would require finding a proof that b is in the set a ***)
      raise (Failure("Lets must be ascribed a type, not a set"))
  | PostInfixDecl(x,a,p,pic) ->
      let a = ltree_to_atree a in
      popfn := declare_postinfix x a p pic !popfn
  | PrefixDecl(x,a,p) ->
      let a = ltree_to_atree a in
      popfn := declare_prefix x a p !popfn
  | BinderDecl(plus,comma,x,a,bo) ->
      let a = ltree_to_atree a in
      let bo = (match bo with Some(b) -> Some(ltree_to_atree b) | None -> None) in
      popfn := declare_binder plus comma x a bo !popfn
  | UnicodeDecl(x,ul) ->
      Hashtbl.add unicode x ul; (*** just associate x with ul forever - not contained within a section ***)
  | SubscriptDecl(x) -> Hashtbl.add subscript x () (*** escapes sections, only use this when it should be permanent ***)
  | SuperscriptDecl(x) -> Hashtbl.add superscript x () (*** escapes sections, only use this when it should be permanent ***)
  | NotationDecl(x,yl) ->
      begin
	match x with
	| "IfThenElse" ->
	    begin
	      match yl with
	      | [y] ->
		  begin
		    try
		      let h = Hashtbl.find sigtmh y in
		      match Hashtbl.find sigtmof h with
		      | (1,Ar(Prop,Ar(TpVar(0),Ar(TpVar(0),TpVar(0))))) ->
			 ifop := Some(h)
                      | (0,Ar(Prop,Ar(Set,Ar(Set,Set)))) ->
                         ifopset := Some(h)
		      | _ -> raise (Failure("IfThenElse Notation should be given a polymorphic name of type prop->?0->?0->?0 or prop->set->set->set"))
		    with Not_found -> raise (Failure("IfThenElse Notation should be given a polymorphic name of type prop->?0->?0->?0 or prop->set->set->set"))
		  end
  	      | _ -> raise (Failure("IfThenElse Notation should be given a polymorphic name of type prop->?0->?0->?0 or prop->set->set->set"))
	    end
	| "Repl" ->
	    begin
	      match yl with
	      | [y] ->
		  begin
		    try
		      let h = Hashtbl.find sigtmh y in
		      match Hashtbl.find sigtmof h with
		      | (0,Ar(Set,Ar(Ar(Set,Set),Set))) ->
			  replop := Some(h)
		      | _ -> raise (Failure("Repl Notation should be given a parameter or definition name of type set->(set->set)->set"))
		    with Not_found -> raise (Failure("Repl Notation should be given a parameter or definition name of type set->(set->set)->set"))
		  end
  	      | _ -> raise (Failure("Repl Notation should be given a parameter or definition name of type set->(set->set)->set"))
	    end
	| "Sep" ->
	    begin
	      match yl with
	      | [y] ->
		  begin
		    try
		      let h = Hashtbl.find sigtmh y in
		      match Hashtbl.find sigtmof h with
		      | (0,Ar(Set,Ar(Ar(Set,Prop),Set))) ->
			  sepop := Some(h)
		      | _ -> raise (Failure("Repl Notation should be given a parameter or definition name of type set->(set->set)->set"))
		    with Not_found -> raise (Failure("Repl Notation should be given a parameter or definition name of type set->(set->set)->set"))
		  end
  	      | _ -> raise (Failure("Repl Notation should be given a parameter or definition name of type set->(set->set)->set"))
	    end
	| "ReplSep" ->
	    begin
	      match yl with
	      | [y] ->
		  begin
		    try
		      let h = Hashtbl.find sigtmh y in
		      match Hashtbl.find sigtmof h with
		      | (0,Ar(Set,Ar(Ar(Set,Prop),Ar(Ar(Set,Set),Set)))) ->
			  replsepop := Some(h)
		      | _ -> raise (Failure("ReplSep Notation should be given a parameter or definition name of type set->(set->prop)->(set->set)->set"))
		    with Not_found -> raise (Failure("ReplSep Notation should be given a parameter or definition name of type set->(set->prop)->(set->set)->set"))
		  end
  	      | _ -> raise (Failure("ReplSep Notation should be given a parameter or definition name of type set->(set->prop)->(set->set)->set"))
	    end
	| "SetEnum" ->
	    begin
	      if List.length yl <= 1 then
		raise (Failure("SetEnum should be given at least n>=2 names: constructors for the first n-1 cases and finally constructor for adjoining to a set"))
	      else
		let rec f i yl ztp =
		  match yl with
		  | [y] ->
		      begin
			try
			  let h = Hashtbl.find sigtmh y in
			  match Hashtbl.find sigtmof h with
			  | (0,Ar(Set,Ar(Set,Set))) ->
			      setenumadj := Some(h)
			  | _ -> raise (Failure("The last name in the SetEnum Notation should be given a parameter or definition name of type set->set->set"))
			with Not_found -> raise (Failure("The last name in the SetEnum Notation should be given a parameter or definition name of type set->set->set"))
		      end
		  | (y::yr) ->
		      begin
			try
			  let h = Hashtbl.find sigtmh y in
			  match Hashtbl.find sigtmof h with
			  | (0,htp) ->
			      if htp = ztp then
				setenuml := Some(h)::!setenuml
			      else
				begin
				  Printf.printf "y = %s h = %s\nhtp = %s\nztp = %s\n" y h (tp_to_str htp) (tp_to_str ztp); flush stdout;
				  raise (Failure("Name " ^ string_of_int i ^ " in the SetEnum Notation should be given a parameter or definition name of type " ^ tp_to_str ztp))
				end
			  | _ -> raise (Failure("Name " ^ string_of_int i ^ " in the SetEnum Notation should be given a parameter or definition name of type " ^ tp_to_str ztp))
			with Not_found -> raise (Failure("Name " ^ string_of_int i ^ " in the SetEnum Notation should be given a parameter or definition name of type " ^ tp_to_str ztp))
		      end;
		      f (i+1) yr (Ar(Set,ztp))
		  | [] -> raise (Failure("SetEnum should be given at least n>=2 names: constructors for the first n-1 cases and finally constructor for adjoining to a set"))
		in
		setenuml := [];
		f 0 yl Set;
		setenuml := List.rev !setenuml
	    end
	| "SetEnum0" ->
	    begin
	      match yl with
	      | [y] ->
		  begin
		    try
		      let h = Hashtbl.find sigtmh y in
		      match Hashtbl.find sigtmof h with
		      | (0,Set) ->
			  set_setenuml_n 0 h
		      | _ -> raise (Failure("SetEnum0 Notation should be given a parameter or definition name of type set"))
		    with Not_found -> raise (Failure("SetEnum0 Notation should be given a parameter or definition name of type set"))
		  end
  	      | _ -> raise (Failure("SetEnum0 Notation should be given a parameter or definition name of type set"))
	    end
	| "SetEnum1" ->
	    begin
	      match yl with
	      | [y] ->
		  begin
		    try
		      let h = Hashtbl.find sigtmh y in
		      match Hashtbl.find sigtmof h with
		      | (0,Ar(Set,Set)) ->
			  set_setenuml_n 1 h
		      | _ -> raise (Failure("SetEnum1 Notation should be given a parameter or definition name of type set->set"))
		    with Not_found -> raise (Failure("SetEnum1 Notation should be given a parameter or definition name of type set->set"))
		  end
  	      | _ -> raise (Failure("SetEnum1 Notation should be given a parameter or definition name of type set->set"))
	    end
	| "SetEnum2" ->
	    begin
	      match yl with
	      | [y] ->
		  begin
		    try
		      let h = Hashtbl.find sigtmh y in
		      match Hashtbl.find sigtmof h with
		      | (0,Ar(Set,Ar(Set,Set))) ->
			  set_setenuml_n 2 h;
		      | _ -> raise (Failure("SetEnum2 Notation should be given a parameter or definition name of type set->set->set"))
		    with Not_found -> raise (Failure("SetEnum2 Notation should be given a parameter or definition name of type set->set->set"))
		  end
  	      | _ -> raise (Failure("SetEnum2 Notation should be given a parameter or definition name of type set->set->set"))
	    end
	| "Nat" ->
	    begin
	      match yl with
	      | [y0;yS] ->
		  begin
		    try
		      let h0 = Hashtbl.find sigtmh y0 in
		      let hS = Hashtbl.find sigtmh yS in
		      match (Hashtbl.find sigtmof h0,Hashtbl.find sigtmof hS) with
		      | ((0,Set),(0,Ar(Set,Set))) ->
			  nat0 := Some(h0);
			  natS := Some(hS)
		      | _ -> raise (Failure("Nat Notation should be given a name of type set (for 0) and a name of type set->set (for successor)"))
		    with Not_found -> raise (Failure("Nat Notation should be given a name of type set (for 0) and a name of type set->set (for successor)"))
		  end
	      | _ -> raise (Failure("Nat Notation should be given a name of type set (for 0) and a name of type set->set (for successor)"))
	    end
	| "SetLam" ->
	    begin
	      match yl with
	      | [y] ->
		  begin
		    try
		      let h = Hashtbl.find sigtmh y in
		      match Hashtbl.find sigtmof h with
		      | (0,Ar(Set,Ar(Ar(Set,Set),Set))) ->
			  setlam := Some h
		      | _ -> raise (Failure("SetLam Notation should be given a name of type set->(set->set)->set"))
		    with Not_found -> raise (Failure("SetLam Notation should be given a name of type set->(set->set)->set"))
		  end
	      | _ -> raise (Failure("SetLam Notation should be given a name of type set->(set->set)->set"))
	    end
	| "SetImplicitOp" ->
	    begin
	      match yl with
	      | [y] ->
		  begin
		    try
		      let h = Hashtbl.find sigtmh y in
		      match Hashtbl.find sigtmof h with
		      | (0,Ar(Set,Ar(Set,Set))) ->
			  setimplop := Some h
		      | _ -> raise (Failure("SetAp Notation should be given a name of type set->set->set"))
		    with Not_found -> raise (Failure("SetAp Notation should be given a name of type set->set->set"))
		  end
	      | _ -> raise (Failure("SetAp Notation should be given a name of type set->set->set"))
	    end
	| _ -> raise (Failure("Unknown Notation " ^ x))
      end
  | ParamHash(x,h,ok) ->
      if (!verbosity > 9) then (Printf.printf "ParamHash %s %s\n" x h; flush stdout);
      if !pfgtheory = SetMM && (x = "wi" || x = "wal") then raise (Failure (Printf.sprintf "%s is a reserved built-in name for SetMM" x));
      begin
        if !pfgtheory = HF then
          begin
            try
              let n = Hashtbl.find pfghfprim h in
              Hashtbl.add pfghfanchor x (Printf.sprintf "p%d" n)
            with Not_found -> ()
          end;
	try
	  let (xj,(xi,_)) = primname x in
	  let xh = ptm_lam_id (xi,Prim xj) sigtmof sigdelta in
	  if (h <> xh) then raise (Failure(x ^ " is the name of a built-in primitive and must have the id " ^ xh))
	with
        | Not_found ->
           if Hashtbl.mem sigtmh x then raise (Failure(x ^ " is already assigned an id"));
           Hashtbl.add sigtmh x h;
           match ok with (** proofgold id **)
           | None -> ()
           | Some(k) -> Hashtbl.add pfgtmhh h (Hash.hexstring_hashval k)
      end
  | ParamDecl(x,a) ->
      if !reporteachitem then (Printf.printf "++ %s\n" x; flush stdout);
      if !pfgtheory = SetMM && (x = "wi" || x = "wal") then raise (Failure (Printf.sprintf "%s is a reserved built-in name for SetMM" x));
      let a = ltree_to_atree a in
      if Hashtbl.mem !sigtm x || List.mem_assoc x !sigpf || List.mem x !ctxtp || List.mem_assoc x !ctxtm || List.mem_assoc x !ctxpf then
	raise (Failure(x ^ " has already been used."));
      if (!verbosity > 9) then (Printf.printf "Param %s : " x; output_ltree stdout (atree_to_ltree a); Printf.printf "\n"; flush stdout);
      let i = List.length !ctxtp in
      let atp = extract_tp a !ctxtp in
      if (!verbosity > 19) then Printf.printf "i = %d\natp = %s\n" i (tp_to_str atp);
      let agtp = !tparclos atp in
      begin
	try
	  let (xj,(xi,xtp)) = primname x in
	  if (xi,xtp) <> (i,agtp) then raise (Failure(x ^ " is the name of a built-in primitive which does not have the given type."));
	  if i > 6 then raise (Failure("It is forbidden to have more than 6 type variables."));
	  let xhv = tm_id (Prim(xj)) sigtmof sigdelta in
          supported := Hashtbl.mem pfgsuppparam xhv;
          if !sexprinfo then Printf.printf "(PRIM %d \"%s\" \"%s\" %s %d)\n" xj x xhv (tp_to_sexpr agtp) !lineno;
	  if x = "Empty" then set0 := Some(xhv);
	  add_sigdelta xhv (0,Prim(xj));
	  if !pfgtheory = Egal then megaauto_set_item xhv false;
          if !pfgtheory = SetMM then (** I'm not sure why every theory isn't treated this way. **)
            begin
              let (pure,pfghv) = pfg_objid (Prim(xj)) agtp in
              Hashtbl.add pfgtmhh xhv pure;
              Hashtbl.add pfgtmroot x (Hash.hashval_hexstring pure);
              Hashtbl.add pfgobjid x (Hash.hashval_hexstring pfghv);
            end;
          if fofp() && i = 0 && not (Hashtbl.mem fofskip xhv) then Hashtbl.add tptp_id_name xhv (tptpize_name x,agtp);
          if th0p() && i = 0 && not (Hashtbl.mem th0skip xhv) then
            begin
              Hashtbl.add tptp_id_name xhv (tptpize_name x,agtp);
              if !th0ps1 then
                th0sgps1 := (None,Printf.sprintf "thf(%s,type,(%s : %s)). %% %s" (tptpize_name x) (tptpize_name x) (th0_stp_str agtp) xhv)::!th0sgps1
              else
                th0sg := ("type","",x,Printf.sprintf "thf(%s,type,(%s : %s)). %% %s" (tptpize_name x) (tptpize_name x) (th0_stp_str agtp) xhv)::!th0sg
            end;
          begin
            match !sexprallsubgoals_inclfile with
            | None -> ()
            | Some(f) ->
               Printf.fprintf f "(PRIM %d \"%s\" \"%s\" %s %d)\n" xj x xhv (tp_to_sexpr agtp) !lineno
          end;
	  begin
	    if !sqlout then
	      begin
		match !mainfilehash with
		| Some docsha ->
		    if !sqltermout then Printf.printf "INSERT INTO `term` (`termid`,`termtp`,`termpoly`,`termprimitive`) VALUES ('%s','%s',%d,true);\n" xhv (stp_html_string agtp) i;
		    if not !presentationonly then (Printf.printf "INSERT INTO `termdoc` (`termid`,`docsha`,`termdocname`,`termdockind`) VALUES ('%s','%s',\"%s\",'p');\n" xhv docsha (String.escaped x));
		| None -> ()
	      end
	  end;
	  if !verbosity > 3 then (Printf.printf "%s has id %s\n" x xhv; flush stdout);
	  if (x = "Power") then setPow := Some xhv;
	  if (x = "In") then (*** As soon as In is declared, declare the id's corresponding to :e and c= ***)
	    begin
	      setIn := Some xhv;
	      let subhv = ptm_lam_id (0,Lam(Set,Lam(Set,All(Set,Imp(Ap(Ap(TmH(xhv),DB(0)),DB(2)),Ap(Ap(TmH(xhv),DB(0)),DB(1))))))) sigtmof sigdelta in
	      setSubeq := Some subhv
	    end;
	  Hashtbl.add sigtmh x xhv;
	  Hashtbl.add sigtmof xhv (i,agtp);
	  if i > 0 then (*** x will look polymorphic with i types after the appropriate section is ended ***)
	    pushpolytm ((x,i),agtp);
	  if i = 0 && not (Hashtbl.mem indextms xhv) then Hashtbl.add indextms xhv xtp; (*** since this is a primitive, it doesn't really need to be indexed. However, indexing it will allow me to use parameters with different names for the primitives if I want. ***)
	  let m = TmH xhv in
	  Hashtbl.replace !sigtm x (!aptmloc m);
	  secstack := List.map (fun (y,f,atl,apl,st,sp) -> (y,f,atl,apl,((Hashtbl.replace st x (atl m)); st),sp)) !secstack
	with Not_found ->
	  begin
	    if (i > 0) then raise (Failure(x ^ " must be defined. The only polymorphic parameter allowed are built-in primitives."));
	    if Hashtbl.mem !sigtm x || List.mem_assoc x !sigpf || List.mem x !ctxtp || List.mem_assoc x !ctxtm || List.mem_assoc x !ctxpf then
	      raise (Failure(x ^ " has already been used."))
	    else
	      try
		let xhv = Hashtbl.find sigtmh x in
                supported := Hashtbl.mem pfgsuppparam xhv;
                if !sexprinfo then Printf.printf "(PARAM \"%s\" \"%s\" %d %s %d)\n" x xhv i (tp_to_sexpr agtp) !lineno;
		if !pfgtheory = Egal then megaauto_set_item xhv false;
                if !pfgtheory = Egal && xhv = "7a7fd30507c2156eeace3d2784ada104fee81316a9d6f02db384ad7f0a180e26" then seqcons := Some(xhv);
                if fofp() && i = 0 && not (Hashtbl.mem fofskip xhv) then Hashtbl.add tptp_id_name xhv (tptpize_name x,agtp);
                if th0p() && i = 0 && not (Hashtbl.mem th0skip xhv) then
                  begin
                    Hashtbl.add tptp_id_name xhv (tptpize_name x,agtp);
                    if !th0ps1 then
                      th0sgps1 := (None,Printf.sprintf "thf(%s,type,(%s : %s)). %% %s" (tptpize_name x) (tptpize_name x) (th0_stp_str agtp) xhv)::!th0sgps1
                    else
                      th0sg := ("type","",x,Printf.sprintf "thf(%s,type,(%s : %s)). %% %s" (tptpize_name x) (tptpize_name x) (th0_stp_str agtp) xhv)::!th0sg;
                  end;
                begin
                  match !sexprallsubgoals_inclfile with
                  | None -> ()
                  | Some(f) ->
                     Printf.fprintf f "(PARAM \"%s\" \"%s\" %d %s)\n" x xhv i (tp_to_sexpr agtp)
                end;
		begin
                  if i = 0 then Hashtbl.add pfgtmph xhv (x,agtp,None);
		  if !pfgout && i = 0 && not !includingsigfile then pfgmain := PfgParam(xhv,x,agtp)::!pfgmain;
                  Hashtbl.add tmh_legend xhv x
		end;
		begin
		  if !sqlout then
		    begin
		      match !mainfilehash with
		      | Some docsha ->
			  if !sqltermout then Printf.printf "INSERT INTO `term` (`termid`,`termtp`,`termpoly`) VALUES ('%s','%s',%d);\n" xhv (stp_html_string agtp) i;
			  if not !presentationonly then (Printf.printf "INSERT INTO `termdoc` (`termid`,`docsha`,`termdocname`,`termdockind`) VALUES ('%s','%s',\"%s\",'p');\n" xhv docsha (String.escaped x));
		      | None -> ()
		    end
		end;
		begin
		  try
		    if (x = "Subq") then
		      begin
			match !setSubeq with
			| Some subhv ->
			    if xhv <> subhv then
			      raise (Failure("Subq can only be used to mean fun X Y:set => forall x:set, x :e X -> x :e Y"))
			| None ->
			    raise (Failure("Subq can only be used after In is declared and then only to mean fun X Y:set => forall x:set, x :e X -> x :e Y"))
		      end;
		    let itp = Hashtbl.find indextms xhv in (** megalodon knows it **)
		    if agtp <> itp then raise (Failure("The id " ^ xhv ^ " associated with the parameter " ^ x ^ " has is indexed to have the type " ^ tp_to_str itp ^ " not " ^ tp_to_str agtp));
		    Hashtbl.add sigtmof xhv (i,agtp);
		    let m = TmH xhv in
		    Hashtbl.replace !sigtm x (!aptmloc m);
                    secstack := List.map (fun (y,f,atl,apl,st,sp) -> (y,f,atl,apl,((Hashtbl.replace st x (atl m)); st),sp)) !secstack
		  with
                  | Not_found ->
                     try
                       if i > 0 then raise Not_found;
                       let pfghpure = Hashtbl.find pfgtmhh xhv in
                       let pfghthy = pfg_objid_pure_to_thy pfghpure agtp in
                       if !pfgsummary then Printf.printf "Param:%s:%s:%s\n" x (Hash.hashval_hexstring pfghpure) (Hash.hashval_hexstring pfghthy);
                       Hashtbl.add pfgtmroot x (Hash.hashval_hexstring pfghpure);
                       Hashtbl.add pfgobjid x (Hash.hashval_hexstring pfghthy);
                       (*                       if not (Hashtbl.mem ownedobj pfghthy) then raise Not_found; (** proofgold knows it **) *)
		       Hashtbl.add sigtmof xhv (i,agtp);
		       let m = TmH xhv in
		       Hashtbl.replace !sigtm x (!aptmloc m);
                       secstack := List.map (fun (y,f,atl,apl,st,sp) -> (y,f,atl,apl,((Hashtbl.replace st x (atl m)); st),sp)) !secstack
		     with
                     | Not_found ->
                         (* () *)
                         raise (Failure("The given id " ^ xhv ^ " for " ^ x ^ " is not a known index for a term.")) (* this was commented out, but it really should be a failure right? *)
		end
   	      with Not_found ->
		raise (Failure("Unknown id for " ^ x))
	  end
      end
  | DefDecl(x,None,b) ->
      if !reporteachitem then (Printf.printf "++ %s\n" x; flush stdout);
      if !pfgtheory = SetMM && (x = "wi" || x = "wal") then raise (Failure (Printf.sprintf "%s is a reserved built-in name for SetMM" x));
      let b = ltree_to_atree b in
      if Hashtbl.mem !sigtm x || List.mem_assoc x !sigpf || List.mem x !ctxtp || List.mem_assoc x !ctxtm || List.mem_assoc x !ctxpf then
	raise (Failure(x ^ " has already been used."))
      else
	begin
	  if (!verbosity > 9) then (Printf.printf "Def %s := " x; output_ltree stdout (atree_to_ltree b); Printf.printf "\n"; flush stdout);
	  let i = List.length !ctxtp in
	  let (btm,btp) = extract_tm b !polytm sigtmof !sigtm !ctxtp !ctxtm in
	  if (!verbosity > 9) then (Printf.printf "Def %s := " x; output_ltree stdout (atree_to_ltree b); Printf.printf "\n"; flush stdout);
	  let bgtm = !tmlamclos btm in
	  let bgtp = !tparclos btp in
	  let xhv = ptm_lam_id (i,bgtm) sigtmof sigdelta in
          supported := Hashtbl.mem pfgsuppparam xhv || Hashtbl.mem pfgsuppdef xhv;
	  if !pfgtheory = Egal then megaauto_set_item xhv true;
          if !pfgtheory = Egal && xhv = "7a7fd30507c2156eeace3d2784ada104fee81316a9d6f02db384ad7f0a180e26" then seqcons := Some(xhv);
          if fofp() && i = 0 && not (Hashtbl.mem fofskip xhv) then
            begin
              try
                Hashtbl.add tptp_id_name xhv (tptpize_name x,bgtp);
                fofsg := ("def",xhv,x,Printf.sprintf "fof(%s,axiom,%s). %% %s" (tptpize_name x) (fof_def_str bgtp xhv bgtm) xhv)::!fofsg;
              with NotFO -> ()
            end;
          if th0p() && i = 0 && not (Hashtbl.mem th0skip xhv) then
            begin
              Hashtbl.add tptp_id_name xhv (tptpize_name x,bgtp);
              if !th0ps1 then
                begin
                  th0sgps1 := (None,Printf.sprintf "thf(%s,type,(%s : %s))." (tptpize_name x) (tptpize_name x) (th0_stp_str bgtp))::!th0sgps1;
                  if not !bushy || Hashtbl.mem bushykdeps xhv then
                    th0sgps1 := (Some(tm_deps bgtm),Printf.sprintf "thf(%s,axiom,%s). %% %s" (tptpize_name x) (th0_def_str bgtp xhv bgtm) xhv)::!th0sgps1
                end
              else
                begin
                  th0sg := ("type","",x,Printf.sprintf "thf(%s,type,(%s : %s))." (tptpize_name x) (tptpize_name x) (th0_stp_str bgtp))::!th0sg;
                  th0sg := ("def",xhv,x,Printf.sprintf "thf(%s_def,definition,%s). %% %s" (tptpize_name x) (th0_def_str bgtp xhv bgtm) xhv)::!th0sg
                end
            end;
          if !sexprinfo then Printf.printf "(DEF \"%s\" \"%s\" %d %s %s %d)\n" x xhv i (tp_to_sexpr bgtp) (tm_to_sexpr bgtm) !lineno;
          begin
            match !sexprallsubgoals_inclfile with
            | None -> ()
            | Some(f) ->
               Printf.fprintf f "(DEF \"%s\" \"%s\" %d %s %s %d)\n" x xhv i (tp_to_sexpr bgtp) (tm_to_sexpr bgtm) !lineno
          end;
          if !verbosity > 5 then Printf.printf "(MGID \"%s\" \"%s\")\n" x xhv;
          begin
            if i = 0 then
              let (pure,pfghv) = pfg_objid bgtm bgtp in
              (*              if !includingsigfile && not (Hashtbl.mem ownedobj pfghv) then Printf.printf "WARNING: The pfg id %s for the object %s is not owned.\n" (Hash.hashval_hexstring pfghv) x; *)
              if !pfgsummary then Printf.printf "Def:%s:%s:%s\n" x (Hash.hashval_hexstring pure) (Hash.hashval_hexstring pfghv);
              Hashtbl.add pfgtmroot x (Hash.hashval_hexstring pure);
              Hashtbl.add pfgobjid x (Hash.hashval_hexstring pfghv);
	      if (!verbosity > 3) then (Printf.printf "%s was assigned pfg obj pure id %s and theory id %s\n" x (Hash.hashval_hexstring pure) (Hash.hashval_hexstring pfghv); flush stdout);
              Hashtbl.add ownedobj pfghv ();
              if (!verbosity > 3) then (Printf.printf "(* Parameter %s \"%s\" \"%s\" *)\n" x xhv (Hash.hashval_hexstring pure));
              Hashtbl.add pfgtmhh xhv pure;
          end;
	  add_sigdelta xhv (i,bgtm);
	  begin
            if i = 0 then Hashtbl.add pfgtmph xhv (x,bgtp,Some(bgtm));
	    if !pfgout && i = 0 && not !includingsigfile then pfgmain := PfgDef(xhv,x,bgtp,bgtm)::!pfgmain;
            Hashtbl.add tmh_legend xhv x
	  end;
	  begin
	    if !sqlout then
	      begin
		match !mainfilehash with
		| Some docsha ->
		    if !sqltermout then Printf.printf "INSERT INTO `term` (`termid`,`termtp`,`termpoly`) VALUES ('%s','%s',%d);\n" xhv (stp_html_string bgtp) i;
		    if not !presentationonly then (Printf.printf "INSERT INTO `termdoc` (`termid`,`docsha`,`termdocname`,`termdockind`) VALUES ('%s','%s',\"%s\",'d');\n" xhv docsha (String.escaped x));
		| None -> ()
	      end
	  end;
	  if (x = "Subq") then
	    begin
	      match !setSubeq with
	      | Some subhv ->
		  if xhv <> subhv then
		    raise (Failure("Subq can only be used to mean fun X Y:set => forall x:set, x :e X -> x :e Y"))
	      | None ->
		  raise (Failure("Subq can only be used after In is declared and then only to mean fun X Y:set => forall x:set, x :e X -> x :e Y"))
	    end;
	  if (!verbosity > 3) then (Printf.printf "%s := %s was assigned id %s\n" x (tm_to_str bgtm) xhv; flush stdout);
	  if i > 0 then (*** x will look polymorphic with i types after the appropriate section is ended ***)
	    pushpolytm ((x,i),bgtp);
	  begin
	    try
	      let xhv2 = Hashtbl.find sigtmh x in
	      if xhv <> xhv2 then raise (Failure(x ^ " was explicitly assigned id " ^ xhv2 ^ " but this does not match its computed id " ^ xhv))
	    with Not_found -> ()
	  end;
	  Hashtbl.add sigtmh x xhv;
	  Hashtbl.add sigtmof xhv (i,bgtp);
	  if i = 0 then
	    begin
	      try
		let itp = Hashtbl.find indextms xhv in
		if bgtp <> itp then raise (Failure("The id " ^ xhv ^ " associated with the definition of " ^ x ^ " has is indexed to have the type " ^ tp_to_str itp ^ " not " ^ tp_to_str bgtp ^ ". This indicates some fundamental bug since it would presumably imply a hash collision."));
	      with Not_found ->
		Hashtbl.add indextms xhv bgtp
	    end;
	  let m = TmH xhv in
	  Hashtbl.replace !sigtm x (!aptmloc m);
	  secstack := List.map (fun (y,f,atl,apl,st,sp) -> (y,f,atl,apl,((Hashtbl.replace st x (atl m)); st),sp)) !secstack;
	  if (!verbosity > 19) then (Printf.printf "i = %d\nbtm = %s\nbtp = %s\n" i (tm_to_str btm) (tp_to_str btp); flush stdout);
	end
  | DefDecl(x,Some a,b) ->
      if !reporteachitem then (Printf.printf "++ %s\n" x; flush stdout);
      if !pfgtheory = SetMM && (x = "wi" || x = "wal") then raise (Failure (Printf.sprintf "%s is a reserved built-in name for SetMM" x));
      let a = ltree_to_atree a in
      let b = ltree_to_atree b in
      if Hashtbl.mem !sigtm x || List.mem_assoc x !sigpf || List.mem x !ctxtp || List.mem_assoc x !ctxtm || List.mem_assoc x !ctxpf then
	raise (Failure(x ^ " has already been used."))
      else
	begin
	  if (!verbosity > 9) then (Printf.printf "Def %s : " x; output_ltree stdout (atree_to_ltree a); Printf.printf "\n := "; output_ltree stdout (atree_to_ltree b); Printf.printf "\n"; flush stdout);
	  let i = List.length !ctxtp in
	  let atp = extract_tp a !ctxtp in
	  let btm = check_tm b atp !polytm sigtmof !sigtm !ctxtp !ctxtm in
	  if (!verbosity > 9) then (Printf.printf "Def %s := " x; output_ltree stdout (atree_to_ltree b); Printf.printf "\n"; flush stdout);
	  let bgtm = !tmlamclos btm in
	  let agtp = !tparclos atp in
	  let xhv = ptm_lam_id (i,bgtm) sigtmof sigdelta in
          supported := Hashtbl.mem pfgsuppparam xhv || Hashtbl.mem pfgsuppdef xhv;
	  if !pfgtheory = Egal then megaauto_set_item xhv true;
          if !pfgtheory = Egal && xhv = "7a7fd30507c2156eeace3d2784ada104fee81316a9d6f02db384ad7f0a180e26" then seqcons := Some(xhv);
          if fofp() && i = 0 && not (Hashtbl.mem fofskip xhv) then
            begin
              try
                Hashtbl.add tptp_id_name xhv (tptpize_name x,agtp);
                fofsg := ("def",xhv,x,Printf.sprintf "fof(%s,axiom,%s). %% %s" (tptpize_name x) (fof_def_str agtp xhv bgtm) xhv)::!fofsg;
              with NotFO -> ()
            end;
          if th0p() && i = 0 && not (Hashtbl.mem th0skip xhv) then
            begin
              Hashtbl.add tptp_id_name xhv (tptpize_name x,agtp);
              if !th0ps1 then
                begin
                  th0sgps1 := (None,Printf.sprintf "thf(%s,type,(%s : %s))." (tptpize_name x) (tptpize_name x) (th0_stp_str agtp))::!th0sgps1;
                  if not !bushy || Hashtbl.mem bushykdeps xhv then
                    th0sgps1 := (Some(tm_deps bgtm),Printf.sprintf "thf(%s,axiom,%s). %% %s" (tptpize_name x) (th0_def_str agtp xhv bgtm) xhv)::!th0sgps1
                end
              else
                begin
                  th0sg := ("type","",x,Printf.sprintf "thf(%s,type,(%s : %s))." (tptpize_name x) (tptpize_name x) (th0_stp_str agtp))::!th0sg;
                  th0sg := ("def",xhv,x,Printf.sprintf "thf(%s_def,definition,%s). %% %s" (tptpize_name x) (th0_def_str agtp xhv bgtm) xhv)::!th0sg;
                end
            end;
          if !sexprinfo then Printf.printf "(DEF \"%s\" \"%s\" %d %s %s %d)\n" x xhv i (tp_to_sexpr agtp) (tm_to_sexpr bgtm) !lineno;
          begin
            match !sexprallsubgoals_inclfile with
            | None -> ()
            | Some(f) ->
               Printf.fprintf f "(DEF \"%s\" \"%s\" %d %s %s %d)\n" x xhv i (tp_to_sexpr agtp) (tm_to_sexpr bgtm) !lineno
          end;
          if !verbosity > 5 then Printf.printf "(MGID \"%s\" \"%s\")\n" x xhv;
          begin
            if i = 0 then
              let (pure,pfghv) = pfg_objid bgtm agtp in
              (*              if !includingsigfile && not (Hashtbl.mem ownedobj pfghv) then Printf.printf "WARNING: The pfg id %s for the object %s is not owned.\n" (Hash.hashval_hexstring pfghv) x; *)
              if !includingsigfile then
                begin
                  if not (Hashtbl.mem ownedobj pfghv || Hashtbl.mem indextms xhv) then
                    if !preambleassig then
                      includingsigfile := false
                    else
                      raise (Failure ("Unknown definition " ^ x ^ " in signature file"))
                end;
              if !pfgsummary then Printf.printf "Def:%s:%s:%s\n" x (Hash.hashval_hexstring pure) (Hash.hashval_hexstring pfghv);
              Hashtbl.add pfgtmroot x (Hash.hashval_hexstring pure);
              Hashtbl.add pfgobjid x (Hash.hashval_hexstring pfghv);
	      if (!verbosity > 3) then (Printf.printf "%s was assigned pfg obj id %s\n" x (Hash.hashval_hexstring pfghv); flush stdout);
              Hashtbl.add ownedobj pfghv ();
              if (!verbosity > 3) then (Printf.printf "(* Parameter %s \"%s\" \"%s\" *)\n" x xhv (Hash.hashval_hexstring pure));
              Hashtbl.add pfgtmhh xhv pure;
          end;
	  add_sigdelta xhv (i,bgtm);
	  begin
            if i = 0 then Hashtbl.add pfgtmph xhv (x,agtp,Some(bgtm));
	    if !pfgout && i = 0 && not !includingsigfile then pfgmain := PfgDef(xhv,x,agtp,bgtm)::!pfgmain;
            Hashtbl.add tmh_legend xhv x
	  end;
	  begin
	    if !sqlout then
	      begin
		match !mainfilehash with
		| Some docsha ->
		    if !sqltermout then Printf.printf "INSERT INTO `term` (`termid`,`termtp`,`termpoly`) VALUES ('%s','%s',%d);\n" xhv (stp_html_string agtp) i;
		    if not !presentationonly then (Printf.printf "INSERT INTO `termdoc` (`termid`,`docsha`,`termdocname`,`termdockind`) VALUES ('%s','%s',\"%s\",'d');\n" xhv docsha (String.escaped x));
		| None -> ()
	      end
	  end;
	  if (x = "Subq") then
	    begin
	      match !setSubeq with
	      | Some subhv ->
		  if xhv <> subhv then
		    raise (Failure("Subq can only be used to mean fun X Y:set => forall x:set, x :e X -> x :e Y"))
	      | None ->
		  raise (Failure("Subq can only be used after In is declared and then only to mean fun X Y:set => forall x:set, x :e X -> x :e Y"))
	    end;
	  if (!verbosity > 3) then (Printf.printf "%s := %s was assigned id %s\n" x (tm_to_str bgtm) xhv; flush stdout);
	  if i > 0 then (*** x will look polymorphic with i types after the appropriate section is ended ***)
	    pushpolytm ((x,i),agtp);
	  begin
	    try
	      let xhv2 = Hashtbl.find sigtmh x in
	      if xhv <> xhv2 then raise (Failure(x ^ " was explicitly assigned id " ^ xhv2 ^ " but this does not match its computed id " ^ xhv))
	    with Not_found -> ()
	  end;
	  Hashtbl.add sigtmh x xhv;
	  Hashtbl.add sigtmof xhv (i,agtp);
	  if i = 0 then
	    begin
	      try
		let itp = Hashtbl.find indextms xhv in
		if agtp <> itp then raise (Failure("The id " ^ xhv ^ " associated with the definition of " ^ x ^ " has is indexed to have the type " ^ tp_to_str itp ^ " not " ^ tp_to_str agtp ^ ". This indicates some fundamental bug since it would presumably imply a hash collision."));
	      with Not_found ->
		Hashtbl.add indextms xhv agtp
	    end;
	  let m = TmH xhv in
	  Hashtbl.replace !sigtm x (!aptmloc m);
	  secstack := List.map (fun (y,f,atl,apl,st,sp) -> (y,f,atl,apl,((Hashtbl.replace st x (atl m)); st),sp)) !secstack;
	  if (!verbosity > 19) then (Printf.printf "i = %d\nbtm = %s\nbtp = %s\n" i (tm_to_str btm) (tp_to_str atp); flush stdout);
	end
  | AxDecl(x,a) ->
      if !reporteachitem then (Printf.printf "++ %s\n" x; flush stdout);
      let a = ltree_to_atree a in
      if Hashtbl.mem !sigtm x || List.mem_assoc x !sigpf || List.mem x !ctxtp || List.mem_assoc x !ctxtm || List.mem_assoc x !ctxpf then
	raise (Failure(x ^ " has already been used."));
      let i = List.length !ctxtp in
      let atm = check_tm a Prop !polytm sigtmof !sigtm !ctxtp !ctxtm in
      let agtm = !tmallclos atm in
      let ahv = ptm_all_id (i,agtm) sigtmof sigdelta in
      supported := Hashtbl.mem pfgsuppknown ahv || Hashtbl.mem pfgsuppthm ahv;
      if !pfgtheory = HF then
        begin
          try
            let n = Hashtbl.find pfghfaxnum ahv in
            Hashtbl.add pfghfanchor x (Printf.sprintf "a%d" n)
          with Not_found -> ()
        end;
      if !pfgtheory = Egal then megaauto_set_known ahv;
      if fofp() && i = 0 && not (Hashtbl.mem fofskip ahv) then (try fofsg := ("known",ahv,x,Printf.sprintf "fof(%s,axiom,%s). %% %s" (tptpize_name x) (fof_prop_str agtm [] 0) ahv)::!fofsg with NotFO -> ());
      if th0p() && i = 0 && not (Hashtbl.mem th0skip ahv) then
        begin
          if not !bushy || Hashtbl.mem bushykdeps ahv then
            if !th0ps1 then
              th0sgps1 := (Some(tm_deps agtm),Printf.sprintf "thf(%s,axiom,%s). %% %s" (tptpize_name x) (th0_str agtm []) ahv)::!th0sgps1
            else
              th0sg := ("known",ahv,x,Printf.sprintf "thf(%s,axiom,%s). %% %s" (tptpize_name x) (th0_str agtm []) ahv)::!th0sg
        end;
      if !sexprinfo then Printf.printf "(AXIOM \"%s\" \"%s\" %d %s %d)\n" x ahv i (tm_to_sexpr agtm) !lineno;
      begin
        match !sexprallsubgoals_inclfile with
        | None -> ()
        | Some(f) ->
           Printf.fprintf f "(AXIOM \"%s\" \"%s\" %d %s %d)\n" x ahv i (tm_to_sexpr agtm) !lineno
      end;
      if !verbosity > 5 then Printf.printf "(MGPROPID \"%s\" \"%s\")\n" x ahv;
      add_sigdelta ahv (i,agtm);
      Hashtbl.add sigknh x ahv;
      Hashtbl.add sigknh_rev ahv x;
      begin
        if i = 0 then
          begin
            Hashtbl.add pfgknph ahv agtm;
          end;
	if !pfgout && i = 0 && not !includingsigfile then pfgmain := PfgKnown(ahv,x,agtm)::!pfgmain
      end;
      activate_special_knowns ahv;
      begin
	if !sqlout then
	  begin
	    match !mainfilehash with
	    | Some docsha ->
		if !sqltermout then Printf.printf "INSERT INTO `term` (`termid`,`termtp`,`termpoly`) VALUES ('%s','%s',%d);\n" ahv (stp_html_string Prop) i;
		if not !presentationonly then (Printf.printf "INSERT INTO `termdoc` (`termid`,`docsha`,`termdocname`,`termdockind`) VALUES ('%s','%s',\"%s\",'a');\n" ahv docsha (String.escaped x));
	    | None -> ()
	  end
      end;
      sigpf := (x,!appfloc (Known(ahv)))::!sigpf;
      if i > 0 then (*** x will look polymorphic with i types after the appropriate section is ended ***)
	pushpolypf ((x,i),agtm);
      if i = 0 then
        begin
          let (pfgpure,pfgahv) = pfg_propid2 agtm in
          Hashtbl.add pfgtmroot x (Hash.hashval_hexstring pfgpure);
          Hashtbl.add pfgpropid x (Hash.hashval_hexstring pfgahv);
          if !pfgsummary then
            Printf.printf "Known:%s:%s:%s\n" x (Hash.hashval_hexstring pfgpure) (Hash.hashval_hexstring pfgahv);
        end;

      if !trustdeclaredaxioms then
        Hashtbl.replace istrustedhash ahv ();
      if not !trustdeclaredaxioms &&
           not (Hashtbl.mem indexknowns ahv) &&
           begin
             if i = 0 then
               let pfgahv = pfg_propid agtm in
               not (Hashtbl.mem ownedprop pfgahv) &&
               not (megawiki_theorem_exists pfgahv)
             else
               false
           end
      then
        Printf.printf "WARNING: The id %s for the proposition for axiom %s [pfg %s] is not indexed as previously known.\n" ahv x (Hash.hashval_hexstring (pfg_propid agtm))
        (* (Printf.printf "ERROR: The id %s for the proposition for axiom %s [pfg %s] is not indexed as previously known.\nYou have to prove it (or leave it as admitted).\n" ahv x (Hash.hashval_hexstring (pfg_propid agtm)); exit 1) *) (* Chad treats this as an error so he comments the warning and uncomments this error. If Chad wants to allow it, the next line outputting UNKNOWN so the instances are easier to find. *)
        (*          (Printf.printf "(UNKNOWN \"%s\" \"%s\" \"%s\")\n" ahv x (Hash.hashval_hexstring (pfg_propid agtm)); flush stdout) *)
      else
        Hashtbl.replace istrustedhash ahv ();
      if trusted_classical_xm_axiom x i agtm then
        Hashtbl.replace istrustedhash ahv ();
      Hashtbl.replace indexknowns ahv ();
      secstack := List.map (fun (y,f,atl,apl,st,sp) -> (y,f,atl,apl,st,(x,apl (Known(ahv)))::sp)) !secstack;
      if (!verbosity > 3) then (Printf.printf "Proposition of Axiom %s : %s was assigned id %s\n" x (tm_to_str agtm) ahv; flush stdout);
      ()
  | ThmDecl(c,x,a) ->
      currthm := x;
      if !pfgtheory = SetMM && (x = "wi" || x = "wal") then raise (Failure (Printf.sprintf "%s is a reserved built-in name for SetMM" x));
      let a = ltree_to_atree a in
      if Hashtbl.mem !sigtm x || List.mem_assoc x !sigpf || List.mem x !ctxtp || List.mem_assoc x !ctxtm || List.mem_assoc x !ctxpf then
	raise (Failure(x ^ " has already been used."));
      if !includingsigfile then if !preambleassig then includingsigfile := false else raise (Failure("Included signature file includes a theorem (" ^ x ^ "), but should only include axioms."));
      let i = List.length !ctxtp in
      let atm = check_tm a Prop !polytm sigtmof !sigtm !ctxtp !ctxtm in
      let agtm = !tmallclos atm in
      let ahv = ptm_all_id (i,agtm) sigtmof sigdelta in
      supported := Hashtbl.mem pfgsuppknown ahv || Hashtbl.mem pfgsuppthm ahv;
      if !verbosity > 5 then Printf.printf "(MGPROPID \"%s\" \"%s\")\n" x ahv;
      let pfgahv = pfg_propid agtm in
      if !warnaboutreproven && (Hashtbl.mem indexknowns ahv || Hashtbl.mem ownedprop pfgahv) then
        begin
          Printf.printf "WARNING: The proposition given in theorem %s is already known, so it should be included as an Axiom or ProofArchived declaration instead.\n" x;
          flush stdout;
        end;
      Hashtbl.add sigknh x ahv;
      Hashtbl.add sigknh_rev ahv x;
      (** Hashtbl.add ownedprop pfgahv ()  This was a major bug! **)
      if i = 0 && (!pfgsummary || not (!html = None) || not (!megawiki = None)) then
        begin
          let (pfgpure,pfgahv) = pfg_propid2 agtm in
          Hashtbl.add pfgtmroot x (Hash.hashval_hexstring pfgpure);
          Hashtbl.add pfgpropid x (Hash.hashval_hexstring pfgahv);
          if !pfgsummary then
            Printf.printf "Thm:%s:%s:%s\n" x (Hash.hashval_hexstring pfgpure) (Hash.hashval_hexstring pfgahv);
        end;
      add_sigdelta ahv (i,agtm);
      if !reporteachitem then (Printf.printf "++ %s\nHASH %s\n" x ahv; flush stdout);
      if !sqlout then
	begin
	  match !treasure with
	  | Some(traddr) ->
	      begin
		match !mainfilehash with
		| Some docsha ->
		    if not !presentationonly then (Printf.printf "INSERT INTO `treasuretermdoc` (`treasureaddress`,`propid`,`docsha`,`thmdocname`) VALUES ('%s','%s','%s','%s');\n" traddr ahv docsha x);
		| None -> ()
	      end
	  | None -> ()
	end;
      if (!verbosity > 3) then (Printf.printf "Proposition of %s %s : %s was assigned id %s\n" c x (tm_to_str agtm) ahv; flush stdout);
      if !sexprinfo then Printf.printf "(THM \"%s\" \"%s\" \"%s\" %d %s %d)\n" x ahv (Hash.hashval_hexstring pfgahv) i (tm_to_sexpr agtm) !lineno;
      begin
        match !sexprallsubgoals_inclfile with
        | None -> ()
        | Some(f) -> close_out f; sexprallsubgoals_inclfile := None
      end;
      let currpflamclos = !pflamclos in
      deltaset := [];
      proving := Some (x,i,agtm,ahv,pfgahv);
      begin
        if !fofpostsubgoals && fofp() then
          let cxtm = !ctxtm in
          let cxpf = !ctxpf in
          let (startlineno,startcharno) = (!lineno,!charno) in
          prooffun :=
            (fun dl ->
              match dl with
                [(endpos,d)] ->
                begin
                  match !fof with
                  | Some(c) ->
                     begin
                       match endpos with
                       | None -> Printf.printf "Do not know end pos of top level %d %d\n" !lineno !charno
                       | Some(endlineno,endcharno) ->
                          try
                            Hashtbl.clear usedknowns;
                            Hashtbl.clear usedhyps;
                            pf_used d 0 usedknowns usedhyps;
                            let z = fof_prop_str atm (tptpizecxtm cxtm) 0 in (** only if the conclusion is FO **)
                            let fn =
                              Printf.sprintf "%s.sl%d.sc%d.el%d.ec%d.top.fof.p" c startlineno startcharno endlineno endcharno
                            in
                            let conjn =
                              Printf.sprintf "%s_%d_%d_%d_%d" c startlineno startcharno endlineno endcharno
                            in
                            let ch = open_out fn in
                            List.iter
                              (fun (cl,h,_,a) ->
                                if cl = "type" || cl = "def" && not (Hashtbl.mem sigdelta_opaque h) || cl = "known" && Hashtbl.mem usedknowns h then
                                  Printf.fprintf ch "%s\n" a)
                              (List.rev !fofsg);
                            let hypcnt = ref (-1) in
                            List.iter
                              (fun (x,p) ->
                                try
                                  incr hypcnt;
                                  if Hashtbl.mem usedhyps !hypcnt then
                                    let a = fof_prop_str p (tptpizecxtm cxtm) 0 in
                                    Printf.fprintf ch "fof(%s,axiom,%s).\n" (tptpize_name x) a
                                with NotFO -> ())
                              cxpf;
                            Printf.fprintf ch "fof(conj_%s,conjecture,%s).\n" conjn z;
                            close_out ch
                          with NotFO -> ()
                     end
                  | None -> ()
                end;
                currpflamclos d
              | _ -> raise (Failure("Bug with proof construction")))
        else if !th0postsubgoals && th0p () then
          let cxtm = !ctxtm in
          let cxpf = !ctxpf in
          let (startlineno,startcharno) = (!lineno,!charno) in
          prooffun :=
            (fun dl ->
              match dl with
                [(endpos,d)] ->
                 begin
                   match !th0 with
                   | Some(c) ->
                      begin
                        match endpos with
                        | None -> Printf.printf "Do not know end pos of top level %d %d" !lineno !charno
                        | Some(endlineno,endcharno) ->
                           Hashtbl.clear usedknowns;
                           Hashtbl.clear usedhyps;
                           pf_used d 0 usedknowns usedhyps;
                           let fn =
                             Printf.sprintf "%s.sl%d.sc%d.el%d.ec%d.top.th0.p" c startlineno startcharno endlineno endcharno
                           in
                           let conjn =
                             Printf.sprintf "%s_%d_%d_%d_%d" c startlineno startcharno endlineno endcharno
                           in
                           let ch = open_out fn in
                           List.iter
                             (fun (cl,h,_,a) ->
                               if cl = "type" || cl = "def" && not (Hashtbl.mem sigdelta_opaque h) || cl = "known" && Hashtbl.mem usedknowns h then
                                 Printf.fprintf ch "%s\n" a)
                             (List.rev !th0sg);
                           let rec th0_cx cxtm =
                             match cxtm with
                             | [] -> ()
                             | (x,(a,d))::cxtmr ->
                                th0_cx cxtmr;
                                Printf.fprintf ch "thf(%s_tp,type,(%s : %s)).\n" (tptpize_name x) (tptpize_name x) (th0_stp_str a);
                                match d with
                                | Some(d) ->
                                   Printf.fprintf ch "thf(%s_def,definition,(%s = %s)).\n" (tptpize_name x) (tptpize_name x) (th0_str d (tptpizecxtm cxtmr))
                                | None -> ()
                           in
                           th0_cx cxtm;
                           let hypcnt = ref (-1) in
                           List.iter
                             (fun (x,p) ->
                               incr hypcnt;
                               if Hashtbl.mem usedhyps !hypcnt then
                                 let a = th0_str p (tptpizecxtm cxtm) in
                                 Printf.fprintf ch "thf(%s,axiom,%s).\n" (tptpize_name x) a)
                             cxpf;
                           Printf.fprintf ch "thf(conj_%s,conjecture,%s).\n" conjn (th0_str atm (tptpizecxtm cxtm));
                           close_out ch
                      end
                   | None -> ()
                 end;
                 currpflamclos d
              | _ -> raise (Failure("Bug with proof construction")))
        else
          prooffun := (fun dl -> match dl with [(_,d)] -> currpflamclos d | _ -> raise (Failure("Bug with proof construction")))
      end;
      pfstate := [PfStateGoal(Some(!lineno,!charno),atm,!ctxtm,!ctxpf)];
      laststructaction := -1

let evaluate_docitem ditem =
  evaluate_docitem_1 ditem;
  begin
    let cx = html_context () in
    let html_targets = ref [] in
    let theorem_for_megawiki =
      match !megawiki,ditem with
      | Some(_),ThmDecl(_,_,_) -> true
      | _ -> false
    in
    begin
      match !html with
      | Some hc ->
         if not !includingsigfile && (not !htmlonlypfgsupp || !supported) then
           html_targets := (hc,false,None)::!html_targets
      | None -> ()
    end;
    begin
      match !megawiki with
      | Some mw ->
         begin
           match ditem with
           | DefDecl(x,_,_) ->
              begin
                try
                  let xh = Hashtbl.find pfgobjid x in
                  let dpath = Filename.concat mw.ddir xh in
                  if not (Sys.file_exists dpath) then
                    begin
                      let ch = open_out dpath in
                      html_targets := (ch,true,Some(xh,x))::!html_targets
                    end
                with Not_found -> ()
              end
           | ThmDecl(_,_,_) -> ()
           | _ -> ()
         end
      | None -> ()
    end;
    let html_targets = List.rev !html_targets in
    let frag_cache = ref None in
    let get_frag () =
      match !frag_cache with
      | Some s -> s
      | None ->
          let s = render_docitem_html_fragment cx ditem in
          frag_cache := Some s;
          s
    in
    begin
      if theorem_for_megawiki || List.length html_targets > 1 then
        let frag = get_frag () in
        List.iter (fun (hc,_,_) -> output_string hc frag) html_targets
      else
        match html_targets with
        | [] -> ()
        | [(hc,_,_)] ->
           output_docitem_html cx hc ditem sigtmh sigknh
        | _ -> ()
    end;
    List.iter
      (fun (hc,close_now,legend_opt) ->
        if close_now then
          begin
            close_out hc;
            match !megawiki,legend_opt with
            | Some mw,Some(hash,name) -> append_megawiki_legend mw hash name
            | _,_ -> ()
          end)
      html_targets;
    begin
      match !megawiki,ditem with
      | Some(mw),ThmDecl(_,x,_) ->
         finalize_megawiki_theorem false;
         begin
           try
             let xh = Hashtbl.find pfgpropid x in
             let frag = get_frag () in
             let tmpfn = Filename.concat mw.tdir (xh ^ ".tmp") in
             if Sys.file_exists tmpfn then Sys.remove tmpfn;
             let ch = open_out tmpfn in
             output_string ch frag;
             let sth = theorem_statement_only_html frag in
             megawiki_thm := Some({ hash = xh; name = x; tempfile = tmpfn; tmpout = ch; statement_html = sth });
           with Not_found ->
             megawiki_thm := None
         end
      | _ -> ()
    end;
    begin
      match ditem with
      | ThmDecl(_,x,_) ->
         begin
           match !html,!megawiki_thm with
           | None,None -> ()
           | _,_ ->
              begin
                match !inchan with
                | Some(c) ->
                   begin
                     try
                       let h = Hashtbl.find sigknh x in
                       currtmid := h
                     with Not_found -> ()
                   end;
                   pflinestart := !lineno;
                   pfcharstart := !charno;
                   skip_to_line_char c inchanline inchanchar !lineno !charno;
                | None -> ()
              end
         end
      | _ -> ()
    end
  end;
  match !latex with
  | Some hc ->
      begin
	if !thmsasexercises then
	  begin
	    match ditem with
	    | ThmDecl(_,x,_) ->
		begin
		  try
		    let h = Hashtbl.find sigknh x in
		    Printf.fprintf hc "\n$x%s\n" h
		  with Not_found -> ()
		end
	    | _ -> ()
	  end;
	output_docitem_latex hc ditem sigtmh sigknh;
	match ditem with
	| ThmDecl(_,x,_) ->
	    begin
	      match !inchan with
	      | Some(c) ->
		  begin
		    try
		      let h = Hashtbl.find sigknh x in
		      currtmid := h
		    with Not_found -> ()
		  end;
		  pflinestart := !lineno;
		  pfcharstart := !charno;
		  skip_to_line_char c inchanline inchanchar !lineno !charno;
	      | None -> ()
	    end
	| _ -> ()
      end
  | None -> ()

let max_pos (line1,char1) (line2,char2) =
  if line1 < line2 then
    (line2,char2)
  else if line1 = line2 then
    if char1 < char2 then
      (line2,char2)
    else
      (line1,char1)
  else
    (line1,char1)
  
let max_opt_pos pos1 pos2 =
  match pos1 with
  | None -> pos2
  | Some(line1,char1) ->
     match pos2 with
     | None -> pos1
     | Some(line2,char2) ->
        Some(max_pos (line1,char1) (line2,char2))

let rec max_opt_pos_l posl =
  match posl with
  | [] -> None
  | pos::posr -> max_opt_pos pos (max_opt_pos_l posr)

let pos_fst_pfst pfst =
  match pfst with
  | PfStateGoal(_,claimtm,cxtm,cxpf)::pfstr ->
     PfStateGoal(Some(!lineno,!charno),claimtm,cxtm,cxpf)::pfstr
  | _ -> pfst

let rec structure_pfstate i goal1 pfstl =
  match pfstl with
  | (PfStateGoal(startpos,claim2,cxtm2,cxpf2)::pfstr) ->
      (PfStateSep(i,true)::goal1::structure_pfstate i (PfStateGoal(startpos,claim2,cxtm2,cxpf2)) pfstr)
  | pfstr ->
      (PfStateSep(i,true)::goal1::PfStateSep(i,false)::pfstr)

let print_pfstate () =
  List.iter
    (fun p ->
      match p with
      | PfStateSep(j,true) -> Printf.printf "PfStateSep(%d,true)\n" j
      | PfStateSep(j,false) -> Printf.printf "PfStateSep(%d,false)\n" j
      | PfStateGoal(startpos,claim1,_,_) -> Printf.printf "PfStateGoal(startpos,%s,_,_)\n" (tm_to_str claim1)
      )
    !pfstate

let postprobs cls startpos endpos claimtm cxtm cxpf d =
  if !fofpostsubgoals then
    begin
      match !fof with
      | None -> ()
      | Some(c) ->
         match endpos with
         | None ->
            begin
              match startpos with
              | None -> Printf.printf "do not know start pos and end pos of %s (%d %d)\n" cls !lineno !charno
              | Some(startlineno,startcharno) -> Printf.printf "do not know end pos of %s starting at %d %d (%d %d)\n" cls startlineno startcharno !lineno !charno
            end
         | Some(endlineno,endcharno) ->
            match startpos with
            | None -> Printf.printf "do not know start pos of %s ending at %d %d (%d %d)\n" cls endlineno endcharno !lineno !charno
            | Some(startlineno,startcharno) ->
               try
                 Hashtbl.clear usedknowns;
                 Hashtbl.clear usedhyps;
                 pf_used d 0 usedknowns usedhyps;
                 let z = fof_prop_str claimtm (tptpizecxtm cxtm) 0 in (** only if the conclusion is FO **)
                 let fn =
                   Printf.sprintf "%s.sl%d.sc%d.el%d.ec%d.%s.fof.p" c startlineno startcharno endlineno endcharno cls
                 in
                 let conjn =
                   Printf.sprintf "%s_%d_%d_%d_%d" c startlineno startcharno endlineno endcharno
                 in
                 let ch = open_out fn in
                 List.iter
                   (fun (cl,h,_,a) ->
                     if cl = "type" || cl = "def" && not (Hashtbl.mem sigdelta_opaque h) || cl = "known" && Hashtbl.mem usedknowns h then
                       Printf.fprintf ch "%s\n" a)
                   (List.rev !fofsg);
                 let hypcnt = ref (-1) in
                 List.iter
                   (fun (x,p) ->
                     try
                       incr hypcnt;
                       if Hashtbl.mem usedhyps !hypcnt then
                         let a = fof_prop_str p (tptpizecxtm cxtm) 0 in
                         Printf.fprintf ch "fof(%s,axiom,%s).\n" (tptpize_name x) a
                     with NotFO -> ())
                   cxpf;
                 Printf.fprintf ch "fof(conj_%s,conjecture,%s).\n" conjn z;
                 close_out ch
               with NotFO -> ()
    end;
  if !th0postsubgoals then
    begin
      match !th0 with
      | None -> ()
      | Some(c) ->
         match endpos with
         | None ->
            begin
              match startpos with
              | None -> Printf.printf "do not know start pos and end pos of %s (%d %d)\n" cls !lineno !charno
              | Some(startlineno,startcharno) -> Printf.printf "do not know end pos of %s starting at %d %d (%d %d)\n" cls startlineno startcharno !lineno !charno
            end
         | Some(endlineno,endcharno) ->
            match startpos with
            | None -> Printf.printf "do not know start pos of %s ending at %d %d (%d %d)\n" cls endlineno endcharno !lineno !charno
            | Some(startlineno,startcharno) ->
               Hashtbl.clear usedknowns;
               Hashtbl.clear usedhyps;
               pf_used d 0 usedknowns usedhyps;
               let fn =
                 Printf.sprintf "%s.sl%d.sc%d.el%d.ec%d.%s.th0.p" c startlineno startcharno endlineno endcharno cls
               in
               let conjn =
                 Printf.sprintf "%s_%d_%d_%d_%d" c startlineno startcharno endlineno endcharno
               in
               let ch = open_out fn in
               List.iter
                 (fun (cl,h,_,a) ->
                   if cl = "type" || cl = "def" && not (Hashtbl.mem sigdelta_opaque h) || cl = "known" && Hashtbl.mem usedknowns h then
                     Printf.fprintf ch "%s\n" a)
                 (List.rev !th0sg);
               let rec th0_cx cxtm =
                 match cxtm with
                 | [] -> ()
                 | (x,(a,d))::cxtmr ->
                    th0_cx cxtmr;
                    Printf.fprintf ch "thf(%s_tp,type,(%s : %s)).\n" (tptpize_name x) (tptpize_name x) (th0_stp_str a);
                    match d with
                    | Some(d) ->
                       Printf.fprintf ch "thf(%s_def,definition,(%s = %s)).\n" (tptpize_name x) (tptpize_name x) (th0_str d (tptpizecxtm cxtmr))
                    | None -> ()
               in
               th0_cx cxtm;
               let hypcnt = ref (-1) in
               List.iter
                 (fun (x,p) ->
                   incr hypcnt;
                   if Hashtbl.mem usedhyps !hypcnt then
                     let a = th0_str p (tptpizecxtm cxtm) in
                     Printf.fprintf ch "thf(%s,axiom,%s).\n" (tptpize_name x) a)
                 cxpf;
               Printf.fprintf ch "thf(conj_%s,conjecture,%s).\n" conjn (th0_str claimtm (tptpizecxtm cxtm));
               close_out ch
    end

let evaluate_pftac_1 pitem thmname i gpgtm gphv pfggphv =
  let megawiki_target : bool option ref = ref None in
  begin
    match !th0,!th0singlesubgoal with
    | Some(c),Some(ln,cn) ->
       begin
         if !lineno = ln && !charno >= cn then
           begin
             match !pfstate with
             | PfStateGoal(startpos,atm,cxtm,cxpf)::_ ->
                begin
                  begin match pitem with
                  | VampireTac _ when !vampireaby = None ->
                     raise (Failure("vampire proof command requires -vampireaby"))
                  | VampireTac _ when !vampireabyproof <> "megalodon" ->
                     raise (Failure("vampire proof command requires -vampireabyproof megalodon"))
                  | _ -> ()
                  end;
                  let fn =
                    Printf.sprintf "%s.th0.p" c
                  in
                  let ch = open_out fn in
                  begin match pitem with
                  | Aby xl | VampireTac xl ->
                     let certified_vampire_tac =
                       match pitem with
                       | VampireTac _ -> true
                       | _ -> false
                     in
                     let conjn = stable_aby_obligation_name () in
                     let proof_command_label = if certified_vampire_tac then "vampire" else "aby" in
                     let content = th0_aby_problem_content ~origin_kind:proof_command_label atm cxtm cxpf xl conjn in
                     Printf.fprintf ch "%s" content;
                     close_out ch;
                     begin
                       match !vampireaby with
                       | None -> ()
                       | Some(_) ->
                          let reconstructed =
                            run_vampire_aby_certificate
                              ~claimtm:atm
                              ~cxtm
                              ~cxpf
                              ~proof_command_label
                              content
                          in
                          if !vampireabynative || certified_vampire_tac then
                            match reconstructed with
                            | Some(_) ->
                               if !verbosity > 2 then
                                 begin
                                   Printf.printf
                                     "Vampire th0single native certificate reconstructed target proof term at line %d char %d.\n"
                                     !lineno
                                     !charno;
                                   flush stdout
                                 end
                            | None when !vampireabynativestrict || certified_vampire_tac ->
                               raise
                                 (Failure
                                    (Printf.sprintf
                                       "Vampire th0single native certificate did not reconstruct target proof term at line %d char %d"
                                       !lineno
                                       !charno))
                            | None -> ()
                     end;
                     exit 0
                  | _ ->
                     List.iter
                       (fun (_,_,_,a) -> Printf.fprintf ch "%s\n" a)
                       (List.rev !th0sg);
                     let rec th0_cx cxtm =
                       match cxtm with
                       | [] -> ()
                       | (x,(a,d))::cxtmr ->
                          th0_cx cxtmr;
                          Printf.fprintf ch "thf(%s_tp,type,(%s : %s)).\n" (tptpize_name x) (tptpize_name x) (th0_stp_str a);
                          match d with
                          | Some(d) ->
                             Printf.fprintf ch "thf(%s_def,definition,(%s = %s)).\n" (tptpize_name x) (tptpize_name x) (th0_str d (tptpizecxtm cxtmr))
                          | None -> ()
                     in
                     th0_cx cxtm;
                     let cnt = ref 0 in
                     List.iter
                       (fun (x,p) ->
                         incr cnt;
                         if not !bushy || Hashtbl.mem bushyhdeps !cnt then
                           let a = th0_str p (tptpizecxtm cxtm) in
                           Printf.fprintf ch "thf(%s,axiom,%s).\n" (tptpize_name x) a)
                       (List.rev cxpf);
                     Printf.fprintf ch "thf(conj_%s,conjecture,%s).\n" c (th0_str atm (tptpizecxtm cxtm))
                  end;
                  close_out ch;
                  exit 0
                end
             | _ ->
                Printf.printf "No claim at line %d and char %d\n" ln cn;
                exit 1
           end
       end
    | _ -> ()
  end;
  if !th0allsubgoals && th0p() then
    begin
      match !pfstate with
      | PfStateGoal(startpos,atm,cxtm,cxpf)::_ ->
         begin
           match !th0 with
           | Some(c) ->
              begin
                let n = !th0subgoalcnt in
                incr th0subgoalcnt;
                let fn =
                  Printf.sprintf "%s.sg%d.line%d.%d.th0.p" c n !lineno !charno
                in
                let conjn =
                  Printf.sprintf "%s_sg%d" c n
                in
                let ch = open_out fn in
                List.iter
                  (fun (_,_,_,a) -> Printf.fprintf ch "%s\n" a)
                  (List.rev !th0sg);
                let rec th0_cx cxtm =
                  match cxtm with
                  | [] -> ()
                  | (x,(a,d))::cxtmr ->
                     th0_cx cxtmr;
                     Printf.fprintf ch "thf(%s_tp,type,(%s : %s)).\n" (tptpize_name x) (tptpize_name x) (th0_stp_str a);
                     match d with
                     | Some(d) ->
                        Printf.fprintf ch "thf(%s_def,definition,(%s = %s)).\n" (tptpize_name x) (tptpize_name x) (th0_str d (tptpizecxtm cxtmr))
                     | None -> ()
                in
                th0_cx cxtm;
                let cnt = ref 0 in
                List.iter
                  (fun (x,p) ->
                    incr cnt;
                    if not !bushy || Hashtbl.mem bushyhdeps !cnt then
                      let a = th0_str p (tptpizecxtm cxtm) in
                      Printf.fprintf ch "thf(%s,axiom,%s).\n" (tptpize_name x) a)
                  (List.rev cxpf);
                Printf.fprintf ch "thf(conj_%s,conjecture,%s).\n" conjn (th0_str atm (tptpizecxtm cxtm));
                close_out ch
              end
           | None -> ()
         end
      | _ -> ()
    end;
  if !fofallsubgoals && fofp() then
    begin
      match !pfstate with
      | PfStateGoal(startpos,atm,cxtm,cxpf)::_ ->
         begin
           match !fof with
           | Some(c) ->
              begin
                try
                  let z = fof_prop_str atm (tptpizecxtm cxtm) 0 in (** only if the conclusion is FO **)
                  let n = !fofsubgoalcnt in
                  incr fofsubgoalcnt;
                  let fn =
                    Printf.sprintf "%s.sg%d.line%d.%dfof.p" c n !lineno !charno
                  in
                  let conjn =
                    Printf.sprintf "%s_sg%d" c n
                  in
                  let ch = open_out fn in
                  List.iter
                    (fun (_,_,_,a) -> Printf.fprintf ch "%s\n" a)
                    (List.rev !fofsg);
                  List.iter
                    (fun (x,p) ->
                      try
                        let a = fof_prop_str p (tptpizecxtm cxtm) 0 in
                        Printf.fprintf ch "fof(%s,axiom,%s).\n" (tptpize_name x) a
                      with NotFO -> ())
                    (List.rev cxpf);
                  Printf.fprintf ch "fof(conj_%s,conjecture,%s).\n" conjn z;
                  close_out ch
                with NotFO -> ()
              end
           | None -> ()
         end
      | _ -> ()
    end;
  (match pitem with
  | PfStruct i when i < 4 ->
      if !verbosity > 19 then (Printf.printf "pfstruct %d\nLength of pfstate stack: %d\n" i (List.length !pfstate); print_pfstate (); flush stdout);
      begin
	match !pfstate with
	| PfStateSep(j,true)::pfstr ->
	    if i = j then
	      begin
		laststructaction := 2;
		pfstate := pos_fst_pfst pfstr;
		if !verbosity > 19 then (Printf.printf "pfstruct %d pop\nLength of pfstate stack: %d\n" i (List.length !pfstate); flush stdout);
	      end
	    else
	      raise (Failure("Previous subproof not completed"))
	| PfStateSep(j,false)::pfstr ->
	    raise (Failure("Proof structuring bug"))
	| [] ->
	    raise (Failure("No claim to prove here"))
	| PfStateGoal(_,claim1,cxtm1,cxpf1)::PfStateGoal(startpos2,claim2,cxtm2,cxpf2)::pfstr ->
	    laststructaction := 1;
	    pfstate := PfStateGoal(Some(!lineno,!charno),claim1,cxtm1,cxpf1)::structure_pfstate i (PfStateGoal(startpos2,claim2,cxtm2,cxpf2)) pfstr;
	    if !verbosity > 19 then (Printf.printf "pfstruct %d push\nLength of pfstate stack: %d\n" i (List.length !pfstate); flush stdout);
	| PfStateGoal(startpos,claim1,cxtm1,cxpf1)::pfstr ->
	    raise (Failure("Inappropriate place for this proof structuring symbol since there is only one goal"))
      end
  | PfStruct 4 ->
      begin
	match !pfstate with
	| PfStateSep _::pfstr ->
	    raise (Failure("A subproof cannot be started here"))
	| [] ->
	    raise (Failure("No claim to prove here"))
	| PfStateGoal(_,claim1,cxtm1,cxpf1)::pfstr ->
           
	   pfstate := PfStateGoal(Some(!lineno,!charno),claim1,cxtm1,cxpf1)::PfStateSep(5,true)::pfstr
      end
  | PfStruct 5 ->
      begin
	match !pfstate with
	| PfStateSep(j,_)::pfstr ->
	    if j = 5 then
	      pfstate := pos_fst_pfst pfstr
	    else
	      raise (Failure("Previous subproof not completed"))
	| [] ->
	    raise (Failure("Not proving a goal"))
	| _ -> raise (Failure("Subproof not completed"))
      end
  | Exact(d) ->
      laststructaction := 0;
      let d = ltree_to_atree d in
      begin
	match !pfstate with
	| (PfStateGoal(startpos,claimtm,cxtm,cxpf) as pfst)::pfstr ->
           begin
             try
	       let dpf = check_pf d claimtm !polytm !polypf sigtmof sigdelta !sigtm !sigpf !ctxtp cxtm cxpf in
	       let currprooffun = !prooffun in
               let endpos = Some(!lineno,!charno) in
	       prooffun := (fun dl -> currprooffun ((endpos,dpf)::dl));
	       pfstate := pfstr;
               begin
                 if !fofpostsubgoals && fofp() then
                   begin
                     match !fof with
                     | None -> ()
                     | Some(c) ->
                        match startpos with
                        | None -> ()
                        | Some(startlineno,startcharno) ->
                           try
                             Hashtbl.clear usedknowns;
                             Hashtbl.clear usedhyps;
                             pf_used dpf 0 usedknowns usedhyps;
                             let z = fof_prop_str claimtm (tptpizecxtm cxtm) 0 in (** only if the conclusion is FO **)
                             let fn =
                               Printf.sprintf "%s.sl%d.sc%d.el%d.ec%d.exact.fof.p" c startlineno startcharno !lineno !charno
                             in
                             let conjn =
                               Printf.sprintf "%s_%d_%d_%d_%d" c startlineno startcharno !lineno !charno
                             in
                             let ch = open_out fn in
                             List.iter
                               (fun (cl,h,_,a) ->
                                 if cl = "type" || cl = "def" && not (Hashtbl.mem sigdelta_opaque h) || cl = "known" && Hashtbl.mem usedknowns h then
                                   Printf.fprintf ch "%s\n" a)
                               (List.rev !fofsg);
                             let hypcnt = ref (-1) in
                             List.iter
                               (fun (x,p) ->
                                 try
                                   incr hypcnt;
                                   if Hashtbl.mem usedhyps !hypcnt then
                                     let a = fof_prop_str p (tptpizecxtm cxtm) 0 in
                                     Printf.fprintf ch "fof(%s,axiom,%s).\n" (tptpize_name x) a
                                 with NotFO -> ())
                               cxpf;
                             Printf.fprintf ch "fof(conj_%s,conjecture,%s).\n" conjn z;
                             close_out ch
                           with NotFO -> ()
                   end
               end;
               if !th0postsubgoals && th0p () then
                 begin
                   match !th0 with
                   | None -> ()
                   | Some(c) ->
                      match startpos with
                      | None ->
                         Printf.printf "do not know start position of exact ending at %d %d\n" !lineno !charno
                      | Some(startlineno,startcharno) ->
                         Hashtbl.clear usedknowns;
                         Hashtbl.clear usedhyps;
                         pf_used dpf 0 usedknowns usedhyps;
                         let fn =
                           Printf.sprintf "%s.sl%d.sc%d.el%d.ec%d.exact.th0.p" c startlineno startcharno !lineno !charno
                         in
                         let conjn =
                           Printf.sprintf "%s_%d_%d_%d_%d" c startlineno startcharno !lineno !charno
                         in
                         let ch = open_out fn in
                         List.iter
                           (fun (cl,h,_,a) ->
                             if cl = "type" || cl = "def" && not (Hashtbl.mem sigdelta_opaque h) || cl = "known" && Hashtbl.mem usedknowns h then
                               Printf.fprintf ch "%s\n" a)
                           (List.rev !th0sg);
                         let rec th0_cx cxtm =
                           match cxtm with
                           | [] -> ()
                           | (x,(a,d))::cxtmr ->
                              th0_cx cxtmr;
                              Printf.fprintf ch "thf(%s_tp,type,(%s : %s)).\n" (tptpize_name x) (tptpize_name x) (th0_stp_str a);
                              match d with
                              | Some(d) ->
                                 Printf.fprintf ch "thf(%s_def,definition,(%s = %s)).\n" (tptpize_name x) (tptpize_name x) (th0_str d (tptpizecxtm cxtmr))
                              | None -> ()
                         in
                         th0_cx cxtm;
                         let cnt = ref 0 in
                         List.iter
                           (fun (x,p) ->
                             incr cnt;
                             if not !bushy || Hashtbl.mem bushyhdeps !cnt then
                               let a = th0_str p (tptpizecxtm cxtm) in
                               Printf.fprintf ch "thf(%s,axiom,%s).\n" (tptpize_name x) a)
                           (List.rev cxpf);
                         Printf.fprintf ch "thf(conj_%s,conjecture,%s).\n" conjn (th0_str claimtm (tptpizecxtm cxtm));
                         close_out ch
                 end;
             with SearchLimit ->
               admitpfstateatp pfst;
	       pfstate := pfstr;
	       prooffun := (fun _ -> raise AdmittedPf)               
           end
	| _ ->
	    raise (Failure("No current claim"))
      end
  | LetTac(xl,None) ->
      laststructaction := 0;
      begin
	match !pfstate with
	| PfStateGoal(startpos,claimtm,cxtm,cxpf)::pfstr ->
	    let rec let_tac_None_r xs claimtm cxtm cxpf =
	      match xs with
	      | [] ->
		  pfstate := PfStateGoal(Some(!lineno,!charno),claimtm,cxtm,cxpf)::pfstr
	      | (x::xr) ->
		  match claimtm with
		  | All(a,body) -> (*** If it's already an All, then don't call headnorm since headnorm will at least beta eta normalize and change the structure. ***)
		      let currprooffun = !prooffun in
		      prooffun := (fun dl ->
                        match dl with
                          (endpos,d1)::dr ->
                           let d = TLam(a,d1) in
                           postprobs "let" startpos endpos claimtm cxtm cxpf d;
                           currprooffun ((endpos,d)::dr)
                        | _ -> raise (Failure("proof reconstruction problem")));
		      let_tac_None_r xr body ((x,(a,None))::cxtm) (List.map (fun (y,q) -> (y,tmshift 0 1 q)) cxpf)
		  | _ -> (*** If it's not an All, then call headnorm and try to expose an All. ***)
		      let (p,dl) = headnorm claimtm sigdelta !deltaset in
		      match p with
		      | All(a,body) ->
			  let currprooffun = !prooffun in
			  prooffun :=
                            (fun dl ->
                              match dl with
                                (endpos,d1)::dr ->
                                 let d = TLam(a,d1) in
                                 postprobs "let" startpos endpos claimtm cxtm cxpf d;
                                 currprooffun ((endpos,d)::dr)
                              | _ -> raise (Failure("proof reconstruction problem")));
			  let_tac_None_r xr body ((x,(a,None))::cxtm) (List.map (fun (y,q) -> (y,tmshift 0 1 q)) cxpf)
		      | _ ->
			  raise (Failure("let tactic used with " ^ x ^ " when claim is not a universal quantifier"))
	    in
	    let_tac_None_r xl claimtm cxtm cxpf
	| _ ->
	    raise (Failure("No current claim"))
      end
  | LetTac(xl,Some b) ->
      laststructaction := 0;
      let b = ltree_to_atree b in
      let btp = extract_tp b !ctxtp in
      begin
	match !pfstate with
	| PfStateGoal(startpos,claimtm,cxtm,cxpf)::pfstr ->
	    let rec let_tac_Some_r xs claimtm cxtm cxpf =
	      match xs with
	      | [] ->
		  pfstate := PfStateGoal(Some(!lineno,!charno),claimtm,cxtm,cxpf)::pfstr
	      | (x::xr) ->
		  match claimtm with
		  | All(a,body) -> (*** If it's already an All, then don't call headnorm since headnorm will at least beta eta normalize and change the structure. ***)
		      if a = btp then
			let currprooffun = !prooffun in
			prooffun := (fun dl -> match dl with (endpos,d)::dr -> currprooffun ((endpos,TLam(a,d))::dr) | _ -> raise (Failure("proof reconstruction problem")));
			let_tac_Some_r xr body ((x,(a,None))::cxtm) (List.map (fun (y,q) -> (y,tmshift 0 1 q)) cxpf)
		      else
			raise (Failure(x ^ " ascribe type " ^ (tp_to_str btp) ^ " but the claim is universally quantified over type " ^ (tp_to_str a)))
		  | _ -> (*** If it's not an All, then call headnorm and try to expose an All. ***)
		      let (p,dl) = headnorm claimtm sigdelta !deltaset in
		      match p with
		      | All(a,body) ->
			  if a = btp then
			    let currprooffun = !prooffun in
			    prooffun := (fun dl -> match dl with (endpos,d)::dr -> currprooffun ((endpos,TLam(a,d))::dr) | _ -> raise (Failure("proof reconstruction problem")));
			    let_tac_Some_r xr body ((x,(a,None))::cxtm) (List.map (fun (y,q) -> (y,tmshift 0 1 q)) cxpf)
			  else
			    raise (Failure(x ^ " ascribe type " ^ (tp_to_str btp) ^ " but the claim is universally quantified over type " ^ (tp_to_str a)))
		      | _ ->
			  raise (Failure("let tactic used with " ^ x ^ " when claim is not a universal quantifier"))
	    in
	    let_tac_Some_r xl claimtm cxtm cxpf
	| _ ->
	    raise (Failure("No current claim"))
      end
  | AssumeTac(xl,None) ->
      laststructaction := 0;
      begin
	match !pfstate with
	| PfStateGoal(startpos,claimtm,cxtm,cxpf)::pfstr ->
	    let rec assume_tac_None_r xs claimtm cxtm cxpf =
	      match xs with
	      | [] ->
		  pfstate := PfStateGoal(Some(!lineno,!charno),claimtm,cxtm,cxpf)::pfstr
	      | (x::xr) ->
		  match claimtm with
		  | Imp(p1,p2) -> (*** If it's already an Imp, then don't call headnorm since headnorm will at least beta eta normalize and change the structure. ***)
		      let currprooffun = !prooffun in
		      prooffun := (fun dl -> match dl with (endpos,d)::dr -> currprooffun ((endpos,PLam(p1,d))::dr) | _ -> raise (Failure("proof reconstruction problem")));
		      assume_tac_None_r xr p2 cxtm ((x,p1)::cxpf)
		  | _ -> (*** If it's not an All, then call headnorm and try to expose an All. ***)
		      let (p,dl) = headnorm claimtm sigdelta !deltaset in
		      match p with
		      | Imp(p1,p2) ->
			  let currprooffun = !prooffun in
			  prooffun := (fun dl -> match dl with (endpos,d)::dr -> currprooffun ((endpos,PLam(p1,d))::dr) | _ -> raise (Failure("proof reconstruction problem")));
			  assume_tac_None_r xr p2 cxtm ((x,p1)::cxpf)
		      | _ ->
			  raise (Failure("assume tactic used with " ^ x ^ " when claim is not an implication"))
	    in
	    assume_tac_None_r xl claimtm cxtm cxpf
	| _ ->
	    raise (Failure("No current claim"))
      end
  | AssumeTac(xl,Some b) ->
      laststructaction := 0;
      let b = ltree_to_atree b in
      begin
	match !pfstate with
	| PfStateGoal(startpos,claimtm,cxtm,cxpf)::pfstr ->
	    let btm = check_tm b Prop !polytm sigtmof !sigtm !ctxtp cxtm in
	    let rec assume_tac_Some_r xs claimtm cxtm cxpf =
	      match xs with
	      | [] ->
		  pfstate := PfStateGoal(Some(!lineno,!charno),claimtm,cxtm,cxpf)::pfstr
	      | (x::xr) ->
		  match claimtm with
		  | Imp(p1,p2) -> (*** If it's already an Imp, then don't call headnorm since headnorm will at least beta eta normalize and change the structure. ***)
		      begin
			match conv p1 btm sigdelta !deltaset with
			| Some(dl) ->
			    deltaset := dl;
			    let currprooffun = !prooffun in
			    prooffun :=
                              (fun dl ->
                                match dl with
                                  (endpos,d1)::dr ->
                                   let d = PLam(btm,d1) in
                                   postprobs "assume" startpos endpos claimtm cxtm cxpf d;
                                   currprooffun ((endpos,d)::dr)
                                | _ -> raise (Failure("proof reconstruction problem")));
			    assume_tac_Some_r xr p2 cxtm ((x,btm)::cxpf)
			| None ->
			    raise (Failure(x ^ " ascribed prop " ^ (tm_to_str btm) ^ " but the antecendent of the claim is " ^ (tm_to_str p1)))
		      end
		  | _ -> (*** If it's not an Imp, then call headnorm and try to expose an Imp. ***)
		      let (p,dl) = headnorm claimtm sigdelta !deltaset in
		      match p with
		      | Imp(p1,p2) ->
			  begin
			    match conv p1 btm sigdelta !deltaset with
			    | Some(dl) ->
				deltaset := dl;
				let currprooffun = !prooffun in
				prooffun := (fun dl -> match dl with (endpos,d)::dr -> currprooffun ((endpos,PLam(btm,d))::dr) | _ -> raise (Failure("proof reconstruction problem")));
				assume_tac_Some_r xr p2 cxtm ((x,btm)::cxpf)
			    | None ->
				raise (Failure(x ^ " ascribed prop " ^ (tm_to_str btm) ^ " but the antecendent of the claim is " ^ (tm_to_str p1)))
			  end
		      | _ ->
			  raise (Failure("assume tactic used with " ^ x ^ " when claim is not an implication"))
	    in
	    assume_tac_Some_r xl claimtm cxtm cxpf
	| _ ->
	    raise (Failure("No current claim"))
      end
  | SetTac(x,None,b) ->
      laststructaction := 0;
      let b = ltree_to_atree b in
      begin
	match !pfstate with
	| PfStateGoal(startpos,claimtm,cxtm,cxpf)::pfstr ->
	    let (btm,btp) = extract_tm b !polytm sigtmof !sigtm !ctxtp cxtm in
	    pfstate := (PfStateGoal(Some(!lineno,!charno),claimtm,(x,(btp,Some(btm)))::cxtm,cxpf))::pfstr
	| _ ->
	    raise (Failure("set tactic cannot be used when there is no claim"))
      end
  | SetTac(x,Some(a),b) ->
      let a = ltree_to_atree a in
      let b = ltree_to_atree b in
      begin
	match !pfstate with
	| PfStateGoal(startpos,claimtm,cxtm,cxpf)::pfstr ->
	    let atp = extract_tp a !ctxtp in
	    let btm = check_tm b atp !polytm sigtmof !sigtm !ctxtp cxtm in
	    pfstate := (PfStateGoal(Some(!lineno,!charno),claimtm,(x,(atp,Some(btm)))::cxtm,cxpf))::pfstr
	| _ ->
	    raise (Failure("set tactic cannot be used when there is no claim"))
      end
  | ApplyTac(a) ->
      laststructaction := 0;
      let a = ltree_to_atree a in
      if !verbosity > 19 then (Printf.printf "apply tactic begin\nLength of pfstate stack: %d\n" (List.length !pfstate); flush stdout);
      begin
	match !pfstate with
	| PfStateGoal(startpos,claimtm,cxtm,cxpf)::pfstr ->
	    let (apf,atm) = extract_pf a !polytm !polypf sigtmof sigdelta !sigtm !sigpf !ctxtp cxtm cxpf in
	    let sigma =
	      begin
		let i = ref 0 in
		List.iter (fun (_,(_,d)) -> match d with None -> incr i | _ -> ()) cxtm;
		map_for (fun j -> MDB j) 0 (!i-1)
	      end
	    in
	    let rec foapplyf p n margs subclaims apff =
	      try
		if !verbosity > 19 then (Printf.printf "about to call pattern_match with %s\n" (mtm_to_str p); flush stdout);
		let theta = pattern_match sigdelta p claimtm (fun _ -> raise Not_found) in
		if !verbosity > 19 then (Printf.printf "after pattern_match\n"; flush stdout);
		let ml = List.map (fun m -> mtm_to_tm (mtm_msub theta m)) margs in
		(*** The next code reverses the subclaims (so earliest arguments are to be proven first) and also grounds them from mtm to tm simultaneously ***)
		let subclaimtms = ref [] in
		List.iter
		  (fun c ->
		    let c1 = mtm_msub theta c in
		    let c2 = mtm_to_tm c1 in
		    subclaimtms := c2::!subclaimtms)
		  subclaims;
		(!subclaimtms,apff ml)
	      with MatchFail ->
		match p with
		| MImp(p1,p2) ->
		   foapplyf p2 n margs (p1::subclaims) (fun ml dl -> match dl with (endpos,d)::dr -> PPfAp(apff ml dr,d) | _ -> raise (Failure("proof reconstruction problem")))
		| MAll(a1,p2) ->
		    begin
		      match mtm_minap_db p2 0 with
		      | None -> (*** special case: no occurrence, use Eps _:a1, False ***)
			  let defelt = Ap(TpAp(Prim(0),a1),Lam(a1,All(Prop,DB(0)))) in
			  foapplyf p2 n margs subclaims (fun ml dl -> match dl with (endpos,d)::dr -> PTmAp(apff ml dr,defelt) | _ -> raise (Failure("proof reconstruction problem")))
		      | Some(l) when l = 0 -> (*** simple case, like a FO var ***)
			  foapplyf (mtm_ssub (MVar(n,sigma)::sigma) p2) (n+1) (MVar(n,sigma)::margs) subclaims (fun ml dl -> match ml with m::mr -> PTmAp(apff mr dl,m) | _ -> raise (Failure("proof reconstruction problem")))
		      | Some(l) -> (*** otherwise, move l arguments into the context of the metavar so that the higher-order pattern case is handled ***)
			  let sigmal = (map_for (fun j -> MDB j) 0 (l-1)) @ (List.map (mtm_shift 0 l) sigma) in
			  let rec lmvnr l a m =
			    if l > 0 then
			      begin
				match a with
				| Ar(a1,a2) -> MLam(a1,lmvnr (l-1) a2 m)
				| _ -> raise (Failure("Type Error found while attempting apply tactic"))
			      end
			    else
			      m
			  in
			  let lmvn = lmvnr l a1 (MVar(n,sigmal)) in
			  let p3 = mtm_ssub (lmvn::sigma) p2 in
			  let p4 = mtm_betared_if p3 (fun q _ -> mtm_lammvar_p q) in
			  foapplyf p4 (n+1) (lmvn::margs) subclaims (fun ml dl -> match ml with m::mr -> PTmAp(apff mr dl,m) | _ -> raise (Failure("proof reconstruction problem")))
		    end
		| _ ->
		    begin
		      let p1 = mtm_betared_if p (fun _ _ -> true) in (*** try to beta reduce ***)
		      if p = p1 then (*** there were no beta reductions ***)
			let (p2,del) = mheadnorm p sigdelta !deltaset in (*** try to delta expand some heads ***)
			if p = p2 then (*** no delta expansions ***)
			  raise Not_found (*** give up and fail ***)
			else
			  begin
			    deltaset := del;
			    foapplyf p2 n margs subclaims apff
			  end
		      else
			foapplyf p1 n margs subclaims apff
		    end
	    in
	    begin
	      try
		if !verbosity > 19 then (Printf.printf "Proof term given with apply proves %s\n" (tm_to_str atm); flush stdout);
		let (subclaims,apff) = foapplyf (tm_to_mtm atm) 0 [] [] (fun ml dl -> apf) in
		let nsubs = List.length subclaims in
		let currprooffun = !prooffun in
                let currpos = Some(!lineno,!charno) in
		prooffun :=
                  (fun dl ->
                    let (dl1,dl2) = split_list nsubs dl in
                    let endpos = max_opt_pos currpos (max_opt_pos_l (List.map (fun (ep,_) -> ep) dl1)) in
                    let d = apff (List.rev dl1) in
                    postprobs "apply" startpos endpos claimtm cxtm cxpf d;
                    currprooffun ((endpos,d)::dl2));
                begin
                  match subclaims with
                  | [] -> pfstate := pfstr
                  | [subclaim1] -> pfstate := PfStateGoal(Some(!lineno,!charno),subclaim1,cxtm,cxpf)::pfstr
                  | subclaim1::subclaimsr ->
		     pfstate := PfStateGoal(Some(!lineno,!charno),subclaim1,cxtm,cxpf)::(List.map (fun c -> PfStateGoal(None,c,cxtm,cxpf)) subclaimsr) @ pfstr;
                end;
		if !verbosity > 19 then (Printf.printf "here nach apply\nLength of pfstate stack: %d\n" (List.length !pfstate); flush stdout);
	      with Not_found ->
		raise (Failure("apply does not match the current claim"))
	    end
	| _ ->
	    raise (Failure("apply tactic cannot be used when there is no claim"))
      end
  | ClaimTac(x,a) ->
      laststructaction := 0;
      let a = ltree_to_atree a in
      begin
	match !pfstate with
	| PfStateGoal(startpos,claimtm,cxtm,cxpf)::pfstr ->
	   let atm = check_tm a Prop !polytm sigtmof !sigtm !ctxtp cxtm in
           let currpos = Some(!lineno,!charno) in
	   pfstate := (PfStateGoal(currpos,atm,cxtm,cxpf))::(PfStateGoal(None,claimtm,cxtm,(x,atm)::cxpf))::pfstr;
	   let currprooffun = !prooffun in
	   prooffun :=
             (fun dl ->
               match dl with
                 (endpos1,d1)::(endpos2,d2)::dr ->
                  let d = PPfAp(PLam(atm,d2),d1) in
                  postprobs "claim" startpos endpos2 claimtm cxtm cxpf d;
                  currprooffun ((endpos2,d)::dr)
               | _ -> raise (Failure("proof reconstruction problem")))
	| _ ->
	   raise (Failure("claim tactic cannot be used when there is no claim"))
      end
  | ProveTac(a,[]) ->
      laststructaction := 0;
      let a = ltree_to_atree a in
      begin
	match !pfstate with
	| PfStateGoal(startpos,claimtm,cxtm,cxpf)::pfstr ->
	    let atm = check_tm a Prop !polytm sigtmof !sigtm !ctxtp cxtm in
	    begin
	      match conv claimtm atm sigdelta !deltaset with
	      | Some(dl) ->
		 deltaset := dl;
                 begin
                   if !fofpostsubgoals || !th0postsubgoals then
                     let currprooffun = !prooffun in
                     prooffun :=
                       (fun dl ->
                         match dl with
                         | (endpos1,d1)::dr ->
                            postprobs "prove" startpos endpos1 claimtm cxtm cxpf d1;
                            currprooffun ((endpos1,d1)::dr)
                         | _ -> raise (Failure("proof reconstruction problem")))
                 end;
		 pfstate := (PfStateGoal(Some(!lineno,!charno),atm,cxtm,cxpf))::pfstr
	      | None ->
		  match conv (TmH(!fal)) atm sigdelta !deltaset with (*** or if prove False, then use FalseE ***)
                  | Some(del) ->
		     deltaset := del;
		     let currprooffun = !prooffun in
		     prooffun :=
                       (fun dl ->
                         match dl with
                           (endpos1,d1)::dr ->
                            let d = PTmAp(PPfAp(Known(!fale),d1),claimtm) in
                            postprobs "prove" startpos endpos1 claimtm cxtm cxpf d;
                            currprooffun ((endpos1,d)::dr)
                         | _ -> raise (Failure("proof reconstruction problem")));
		     pfstate := (PfStateGoal(Some(!lineno,!charno),atm,cxtm,cxpf))::pfstr
                  | None ->
		     match conv (All(Prop,DB(0))) atm sigdelta !deltaset with (*** or if prove False, then use old FalseE ***)
		     | Some(del) ->
		        deltaset := del;
		        let currprooffun = !prooffun in
		        prooffun :=
                          (fun dl ->
                            match dl with
                              (endpos1,d1)::dr ->
                               let d = PTmAp(d1,claimtm) in
                               postprobs "prove" startpos endpos1 claimtm cxtm cxpf d;
                               currprooffun ((endpos1,d)::dr)
                            | _ -> raise (Failure("proof reconstruction problem")));
		        pfstate := (PfStateGoal(Some(!lineno,!charno),atm,cxtm,cxpf))::pfstr
		     | None ->
		        raise (Failure("Proposition given with prove tactic does not match the current claim.\n" ^ tm_to_str claimtm ^ "\n" ^ tm_to_str atm))
	    end
	| _ ->
	    raise (Failure("prove tactic cannot be used when there is no claim"))
      end
  | ProveTac(a,bl) ->
      laststructaction := 0;
      raise (Failure("prove tactic can currently only be used with one proposition"))
  | CasesTac(a,xbll) ->
      laststructaction := 0;
      raise (Failure("cases tactic is not yet implemented"))
  | WitnessTac(a) ->
      laststructaction := 0;
      let a = ltree_to_atree a in
      begin
	match !pfstate with
	| PfStateGoal(startpos,claimtm,cxtm,cxpf)::pfstr ->
	   begin
	     try
	       let (etp,ep) = extract_exclaim claimtm in
	       let atm = check_tm a etp !polytm sigtmof !sigtm !ctxtp cxtm in
	       let epatm =
		 begin
		   match ep with
		   | Lam(_,epbody) -> tmsubst epbody 0 atm
		   | _ -> Ap(ep,atm)
		 end
	       in
	       if !verbosity > 50 then (Printf.printf "witness tactic with etp = %s\n and ep = %s\n and atm = %s\n and epatm = %s\n" (tp_to_str etp) (tm_to_str ep) (tm_to_str atm) (tm_to_str epatm); flush stdout);
	       pfstate := (PfStateGoal(startpos,epatm,cxtm,cxpf)::pfstr);
	       let currprooffun = !prooffun in
               if !expolyIknown then
	         prooffun :=
                   (fun dl ->
                     match dl with
                       (endpos,d1)::dr ->
                        let d = PPfAp(PTmAp(PTmAp(PTpAp(Known(!expolyI),etp),ep),atm),d1) in
                        postprobs "witness" startpos endpos claimtm cxtm cxpf d;
                        currprooffun ((endpos,d)::dr)
                     | _ -> raise (Failure("proof reconstruction problem")))
               else
	         prooffun :=
                   (fun dl ->
                     match dl with
                       (endpos,d1)::dr ->
                        let d = TLam(Prop,PLam(All(etp,Imp(gen_lam_body(tmshift 0 1 ep),DB(1))),PPfAp(PTmAp(Hyp(0),tmshift 0 1 atm),pftmshift 0 1 (pfshift 0 1 d1)))) in
                        postprobs "witness" startpos endpos claimtm cxtm cxpf d;
                        currprooffun ((endpos,d)::dr)
                     | _ -> raise (Failure("proof reconstruction problem")))
	     with Not_found ->
	       raise (Failure("witness tactic can only be used when claim is existential"))
	   end
	| _ ->
	   raise (Failure("witness tactic cannot be used when there is no claim"))
      end
  | RewriteTac(sym,a,posl) -> (*** rewrite from right to left if not sym or left to right if sym ***)
      laststructaction := 0;
      let a = ltree_to_atree a in
      if !verbosity > 19 then (Printf.printf "rewrite tactic begin\nLength of pfstate stack: %d\n" (List.length !pfstate); flush stdout);
      begin
	match !pfstate with
	| PfStateGoal(startpos,claimtm,cxtm,cxpf)::pfstr ->
	    let (apf,atm) = extract_pf a !polytm !polypf sigtmof sigdelta !sigtm !sigpf !ctxtp cxtm cxpf in
	    let sigma =
	      begin
		let i = ref 0 in
		List.iter (fun (_,(_,d)) -> match d with None -> incr i | _ -> ()) cxtm;
		map_for (fun j -> MDB j) 0 (!i-1)
	      end
	    in
	    let inpos i = match posl with [] -> true | _ -> List.mem i posl in
	    let posr = ref 0 in
	    let rec forewritef4 z etmi mtm =
	      if !verbosity > 79 then (Printf.printf "forewritef4: %d\n etmi: %s\n mtm: %s\n" z (tm_to_str etmi) (tm_to_str mtm); flush stdout);
	      if mtm = etmi then
		begin
		  incr posr;
		  if inpos !posr then
		    DB(z)
		  else
		    forewritef5 z etmi mtm
		end
	      else
		forewritef5 z etmi mtm
	    and forewritef5 z etmi mtm =
	      if !verbosity > 79 then (Printf.printf "forewritef5: %d\n etmi: %s\n mtm: %s\n" z (tm_to_str etmi) (tm_to_str mtm); flush stdout);
	      match mtm with
	      | Ap(m1,m2) ->
		  let m1b = forewritef4 z etmi m1 in
		  let m2b = forewritef4 z etmi m2 in
		  Ap(m1b,m2b)
	      | Imp(m1,m2) ->
		  let m1b = forewritef4 z etmi m1 in
		  let m2b = forewritef4 z etmi m2 in
		  Imp(m1b,m2b)
	      | Lam(a1,m1) -> Lam(a1,forewritef4 (z+1) (tmshift 0 1 etmi) m1)
	      | All(a1,m1) -> All(a1,forewritef4 (z+1) (tmshift 0 1 etmi) m1)
	      | DB(j) when j >= z -> DB(j+1)
	      | _ -> mtm
	    in
	    let rec forewritef2 z n etp etm mtm =
	      if !verbosity > 79 then (Printf.printf "forewritef2: %d %d\n etm: %s\n mtm: %s\n" z n (mtm_to_str etm) (tm_to_str mtm); flush stdout);
	      begin
		try
		  begin
		    if !verbosity > 19 then (Printf.printf "rewrite: about to call pattern_match with\n    %s\n =? %s\n" (mtm_to_str etm) (tm_to_str mtm); flush stdout);
		    let theta = pattern_match sigdelta etm mtm (fun _ -> raise Not_found) in
		    if !verbosity > 19 then (Printf.printf "after pattern_match %d\n" !posr; flush stdout);
		    try
		      begin
			for i = 0 to n-1 do
			  let _ = theta i in ()
			done;
			incr posr;
			if inpos !posr then
			  begin
			    (*** the instantiation to use ***)
			    (DB(z),theta)
			  end
			else
			  forewritef3 z n etp etm mtm
		      end
		    with Not_found ->
		      forewritef3 z n etp etm mtm
		  end
		with MatchFail ->
		  forewritef3 z n etp etm mtm
	      end
	    and forewritef3 z n etp etm mtm =
	      if !verbosity > 79 then (Printf.printf "forewritef3: %d %d\n etm: %s\n mtm: %s\n" z n (mtm_to_str etm) (tm_to_str mtm); flush stdout);
	      match mtm with
	      | Ap(m1,m2) ->
		  begin
		    try
		      let (leibp1,theta) = forewritef2 z n etp etm m1 in
		      let leibp2 = forewritef4 z (mtm_to_tm (mtm_msub theta etm)) m2 in
		      (Ap(leibp1,leibp2),theta)
		    with Not_found ->
		      let (leibp2,theta) = forewritef2 z n etp etm m2 in
		      (Ap(tmshift z 1 m1,leibp2),theta)
		  end
	      | Imp(m1,m2) ->
		  begin
		    try
		      let (leibp1,theta) = forewritef2 z n etp etm m1 in
		      let leibp2 = forewritef4 z (mtm_to_tm (mtm_msub theta etm)) m2 in
		      (Imp(leibp1,leibp2),theta)
		    with Not_found ->
		      let (leibp2,theta) = forewritef2 z n etp etm m2 in
		      (Imp(tmshift z 1 m1,leibp2),theta)
		  end
	      | Lam(a1,m1) ->
		  let (leibp1,theta) = forewritef2 (z+1) n etp (mtm_shift 0 1 etm) m1 in
		  (Lam(a1,leibp1),theta)
	      | All(a1,m1) ->
		  let (leibp1,theta) = forewritef2 (z+1) n etp (mtm_shift 0 1 etm) m1 in
		  (All(a1,leibp1),theta)
	      | _ -> raise Not_found
	    in
	    let destruct_leibeq p =
	      match p with
	      | MAp(MAp(MTpAp(MTmH(e),etp),ltm),rtm) when e = !eqPoly -> (etp,ltm,rtm) (*** recognize it before delta expanding ***)
	      | MAll(Ar(etp,Prop),MImp(MAp(MDB(0),shltm),MAp(MDB(0),shrtm))) -> (*** also need to recognize delta expanded version to avoid confusion ***)
		  begin
		    try
		      let ltm = mtm_shift 0 (-1) shltm in
		      let rtm = mtm_shift 0 (-1) shrtm in
		      (etp,ltm,rtm)
		    with NegDB -> raise Not_found
		  end
	      | MAll(Ar(etp,Ar(etp2,Prop)),
		     MImp(MAp(MAp(MDB(0),shltm1),shrtm1),
			  MAp(MAp(MDB(0),shrtm2),shltm2))) when etp = etp2 -> (*** Megalodon library equality: forall Q:a->a->prop, Q l r -> Q r l ***)
		  begin
		    try
		      if shltm1 = shltm2 && shrtm1 = shrtm2 then
			let ltm = mtm_shift 0 (-1) shltm1 in
			let rtm = mtm_shift 0 (-1) shrtm1 in
			(etp,ltm,rtm)
		      else
			raise Not_found
		    with NegDB -> raise Not_found
		  end
	      | _ ->
		  raise Not_found
	    in
	    let rec forewritef p n margs subclaims apff =
	      if !verbosity > 19 then (Printf.printf "forewritef p : %s\n" (mtm_to_str p); flush stdout);
	      begin
		try
		  let (etp,ltm,rtm) = destruct_leibeq p in
		  begin
		    try
		      let tm1 = if sym then rtm else ltm in
		      let tm2 = if sym then ltm else rtm in
		      let (leibq,theta) = forewritef2 0 n etp tm1 claimtm in
		      if !verbosity > 90 then (Printf.printf "leibq: %s\n" (tm_to_str leibq); flush stdout);
		      let tm2i = mtm_to_tm (mtm_msub theta tm2) in
		      let ml = List.map (fun m -> mtm_to_tm (mtm_msub theta m)) margs in
		      let subclaimtms = ref [] in
		      List.iter
			(fun c ->
			  let c1 = mtm_msub theta c in
			  let c2 = mtm_to_tm c1 in
			  subclaimtms := c2::!subclaimtms)
			subclaims;
		      let apffm =
			if sym then
			  (fun dl ->
			    match dl with
			      (endpos,d)::dr ->
				let epf = apff ml dr in
				PPfAp(PTmAp(epf,Lam(etp,Lam(etp,tmshift 0 1 leibq))),d)
			    | _ -> raise (Failure("proof reconstruction problem")))
			else
			  (fun dl ->
			    match dl with
			      (endpos,d)::dr ->
				let epf = apff ml dr in
				PPfAp(PTmAp(epf,Lam(etp,Lam(etp,tmshift 1 1 leibq))),d)
			    | _ -> raise (Failure("proof reconstruction problem")))
		      in
		      (tmsubst leibq 0 tm2i::!subclaimtms,apffm)
		    with Not_found ->
		      raise (Failure("rewrite tactic failed"))
		  end
		with Not_found ->
		  match p with
		  | MImp(p1,p2) ->
		      forewritef p2 n margs (p1::subclaims) (fun ml dl -> match dl with (endpos,d)::dr -> PPfAp(apff ml dr,d) | _ -> raise (Failure("proof reconstruction problem")))
		  | MAll(a1,p2) ->
		      begin
			match mtm_minap_db p2 0 with
			| None -> (*** special case: no occurrence, use Eps _:a1, False ***)
			    let defelt = Ap(TpAp(Prim(0),a1),Lam(a1,All(Prop,DB(0)))) in
			    forewritef p2 n margs subclaims (fun ml dl -> match dl with (endpos,d)::dr -> PTmAp(apff ml dr,defelt) | _ -> raise (Failure("proof reconstruction problem")))
			| Some(l) when l = 0 -> (*** simple case, like a FO var ***)
			    forewritef (mtm_ssub (MVar(n,sigma)::sigma) p2) (n+1) (MVar(n,sigma)::margs) subclaims (fun ml dl -> match ml with m::mr -> PTmAp(apff mr dl,m) | _ -> raise (Failure("proof reconstruction problem")))
			| Some(l) -> (*** otherwise, move l arguments into the context of the metavar so that the higher-order pattern case is handled ***)
			    let sigmal = (map_for (fun j -> MDB j) 0 (l-1)) @ (List.map (mtm_shift 0 l) sigma) in
			    let rec lmvnr l a m =
			      if l > 0 then
				begin
				  match a with
				  | Ar(a1,a2) -> MLam(a1,lmvnr (l-1) a2 m)
				  | _ -> raise (Failure("Type Error found while attempting apply tactic"))
				end
			      else
				m
			    in
			    let lmvn = lmvnr l a1 (MVar(n,sigmal)) in
			    let p3 = mtm_ssub (lmvn::sigma) p2 in
			    let p4 = mtm_betared_if p3 (fun q _ -> mtm_lammvar_p q) in
			    forewritef p4 (n+1) (lmvn::margs) subclaims (fun ml dl -> match ml with m::mr -> PTmAp(apff mr dl,m) | _ -> raise (Failure("proof reconstruction problem")))
		      end
		  | _ ->
		      begin
			let p1 = mtm_betared_if p (fun _ _ -> true) in (*** try to beta reduce ***)
			if p = p1 then (*** there were no beta reductions ***)
			  let (p2,del) = mheadnorm p sigdelta !deltaset in (*** try to delta expand some heads ***)
			  if p = p2 then
			    begin
			      if !verbosity > 19 then (Printf.printf "p : %s\n" (mtm_to_str p); flush stdout);
			      raise (Failure("rewrite tactic given a proof of a non-equation"))
			    end
			  else
			    begin
			      deltaset := del;
			      forewritef p2 n margs subclaims apff
			    end
			else
			  forewritef p1 n margs subclaims apff
		      end
	      end
	    in
	    begin
	      try
		if !verbosity > 19 then (Printf.printf "Proof term given with rewrite proves %s\n" (tm_to_str atm); flush stdout);
		let (subclaims,apff) = forewritef (tm_to_mtm atm) 0 [] [] (fun ml dl -> apf) in
		let nsubs = List.length subclaims in
		let currprooffun = !prooffun in
		prooffun := (fun dl ->
                  match dl with
                    d0::dr ->
                     let (dl1,dl2) = split_list (nsubs-1) dr in
                     let endpos = max_opt_pos_l (List.map (fun (ep,_) -> ep) (d0::dl1)) in
                     let d = apff (d0::List.rev dl1) in
                     postprobs "rewrite" startpos endpos claimtm cxtm cxpf d;
                     currprooffun ((endpos,d)::dl2)
                  | [] -> raise (Failure("proof reconstruction problem")));
                begin
                  match subclaims with
                  | [] -> pfstate := pfstr
                  | [subclaim1] -> pfstate := PfStateGoal(Some(!lineno,!charno),subclaim1,cxtm,cxpf)::pfstr
                  | subclaim1::subclaimsr ->
		     pfstate := PfStateGoal(Some(!lineno,!charno),subclaim1,cxtm,cxpf)::(List.map (fun c -> PfStateGoal(None,c,cxtm,cxpf)) subclaimsr) @ pfstr;
                end;
		if !verbosity > 19 then (Printf.printf "here nach apply\nLength of pfstate stack: %d\n" (List.length !pfstate); flush stdout);
	      with Not_found ->
		raise (Failure("rewrite tactic failed"))
	    end
	| _ ->
	    raise (Failure("rewrite tactic cannot be used when there is no claim"))
      end
  | Qed ->
      begin
        let qed_debug_timing =
          Sys.getenv_opt "MEGALODON_CERT_DEBUG_TIMING" = Some "1"
        in
        let qed_timing_start = Unix.gettimeofday () in
        let qed_timing_last = ref qed_timing_start in
        let qed_timing stage =
          if qed_debug_timing then
            begin
              let now = Unix.gettimeofday () in
              Printf.printf
                "Megalodon Qed timing %s at line %d char %d theorem %s: +%.3fs total %.3fs.\n"
                stage
                !lineno
                !charno
                thmname
                (now -. !qed_timing_last)
                (now -. qed_timing_start);
              qed_timing_last := now;
              flush stdout
            end
        in
        qed_timing "start";
        currthm := "";
	if !pfstate = [] then
	  begin
	    try
	      if !verbosity > 19 then (Printf.printf "Qed start\n"; flush stdout);
	      Hashtbl.replace indexknowns gphv ();
              Hashtbl.replace ownedprop pfggphv ();
	      activate_special_knowns gphv;
	      if !pfgtheory = Egal then megaauto_set_known gphv;
              if fofp() && i = 0 && not (Hashtbl.mem fofskip gphv) then
                begin
                  try
                    fofsg := ("known",gphv,thmname,Printf.sprintf "fof(%s,axiom,%s). %% %s" (tptpize_name thmname) (fof_prop_str gpgtm [] 0) gphv)::!fofsg;
                  with NotFO -> ()
                end;
              if th0p() && i = 0 && not (Hashtbl.mem th0skip gphv) then
                begin
                  if not !bushy || Hashtbl.mem bushykdeps gphv then
                    if !th0ps1 then
                      (th0sgps1 := (Some(tm_deps gpgtm),Printf.sprintf "thf(%s,axiom,%s). %% %s" (tptpize_name thmname) (th0_str gpgtm []) gphv)::!th0sgps1)
                    else
                      (th0sg := ("known",gphv,thmname,Printf.sprintf "thf(%s,axiom,%s). %% %s" (tptpize_name thmname) (th0_str gpgtm []) gphv)::!th0sg)
                end;
              begin
                match !sexprallsubgoals with
                | None -> ()
                | Some(seaspre,seasincl,i) ->
                   let fn = Printf.sprintf "%s_incl_%d.lisp" seaspre i in
                   let f = open_out fn in
                   if not (seasincl = "") then Printf.fprintf f "(INCLUDE \"%s\")\n" seasincl;
                   Printf.fprintf f "(THM \"%s\" \"%s\" %d %s)\n" thmname gphv i (tm_to_sexpr gpgtm);
                   sexprallsubgoals_inclfile := Some(f);
                   sexprallsubgoals := Some(seaspre,fn,i+1)
              end;
	      sigpf := (thmname,!appfloc (Known(gphv)))::!sigpf;
	      if i > 0 then (*** x will look polymorphic with i types after the appropriate section is ended ***)
		pushpolypf ((thmname,i),gpgtm);
	      secstack := List.map (fun (y,f,atl,apl,st,sp) -> (y,f,atl,apl,st,(thmname,apl (Known(gphv)))::sp)) !secstack;
	      proving := None;
              qed_timing "prooffun:start";
	      let dgpf = !prooffun [] in
              qed_timing "prooffun:done";
              qed_timing "optimize_pf_1:start";
              let dgpf = if !optimizepf1 then optimize_pf_1 dgpf else dgpf in
              qed_timing "optimize_pf_1:done";
              qed_timing "optimize_pf_2:start";
              let dgpf = if !optimizepf2 then optimize_pf_2 sigdelta sigtmof dgpf !optimizepf2tc !optimizepf2pc else dgpf in
              qed_timing "optimize_pf_2:done";
              qed_timing "normalize_pf:start";
              let dgpf = if !normalizepf then normalize_pf dgpf else dgpf in
              qed_timing "normalize_pf:done";
	      let qed_is_complete = ref true in
	      begin
		if i = 0 then
		  begin
		    Hashtbl.add pfgknph gphv gpgtm;
		  end;
		if !pfgout && i = 0 && not !includingsigfile then
		  pfgmain := PfgThm(gphv,thmname,gpgtm,dgpf)::!pfgmain;
                qed_timing "istrusted:start";
	        if not !allowincompleteqed then
	          istrusted thmname dgpf (* Raises an exception if not proved *)
	        else
	          begin
	            try
	              istrusted thmname dgpf
	            with Failure(_) ->
	              qed_is_complete := false
	          end;
                qed_timing "istrusted:done";
	        Hashtbl.add istrustedhash gphv ()
	      end;
	      if (!verbosity > 19) then (Printf.printf "Double checking:\n%s\n%s\n" (pf_to_str dgpf) (tm_to_str gpgtm); flush stdout);
              qed_timing "check_propofpf:start";
	      match
                if !doublecheckpf then
                  check_propofpf sigdelta sigtmof [] [] dgpf gpgtm !deltaset
                else
                  Some(!deltaset)
              with
	      | None ->
                  qed_timing "check_propofpf:failed";
		  if (!verbosity > 19) then (Printf.printf "Proof doesn't doublecheck!\n%s\n" (pf_to_str dgpf); flush stdout);
		  raise (Failure("Proof doesn't prove the proposition."))
	      | Some(dl) ->
                  qed_timing "check_propofpf:done";
		  deltaset := dl;
                  if !sexprinfo then (List.iter (fun d -> Printf.printf "(DELTA \"%s\")\n" d) dl; Printf.printf "(QED)\n");
                  if !pfgout && not !includingsigfile then List.iter (fun d -> Hashtbl.add pfgdelta d ()) !deltaset;
		  if (!verbosity > 19) then (Printf.printf "Delta Set:"; List.iter (fun h -> Printf.printf " %s" h) dl; Printf.printf "\n"; flush stdout);
		  let dhv = ppf_id (i,dgpf) sigtmof sigdelta in
		  if (!verbosity > 3) then (Printf.printf "Proof of %s was assigned id %s\n" thmname dhv; flush stdout);
		  if (!reportpfcomplexity) then (Printf.printf "(PFCOMPLEXITY \"%s\" \"%s\" \"%s\" %d)\n" thmname gphv dhv (pf_complexity dgpf); flush stdout);
		  begin
		    if !sqlout then
		      begin
			match !mainfilehash with
			| Some docsha ->
			    if !sqltermout then Printf.printf "INSERT INTO `term` (`termid`,`termtp`,`termpoly`) VALUES ('%s','%s',%d);\n" gphv (stp_html_string Prop) i;
			    if not !presentationonly then (Printf.printf "INSERT INTO `termdoc` (`termid`,`docsha`,`termdocname`,`termdockind`) VALUES ('%s','%s',\"%s\",'T');\n" gphv docsha (String.escaped thmname));
			    if !sqltermout then Printf.printf "INSERT INTO `proppf` (`propid`,`pfid`) VALUES ('%s','%s');\n" gphv dhv;
			    if not !presentationonly then
			      begin
				Printf.printf "INSERT INTO `proppfdoc` (`propid`,`pfid`,`docsha`) VALUES ('%s','%s',\"%s\");\n" gphv dhv docsha;
				List.iter
				  (fun d ->
				    Printf.printf "INSERT INTO `proppfdocdelta` (`propid`,`pfid`,`docsha`,`termid`) VALUES ('%s','%s','%s','%s');\n" gphv dhv docsha d)
				  !deltaset
			  end
			| None -> ()
		      end
		  end;
                  qed_timing "vampire_qed_cleanup:start";
                  vampire_clear_reconstruction_delta_for_qed ();
                  vampire_assert_no_qed_reconstruction_state "Qed cleanup";
                  qed_timing "vampire_qed_cleanup:done";
	          megawiki_target := Some(!qed_is_complete);
	    with AdmittedPf ->
              if !sexprinfo then Printf.printf "(QEDWITHADMITS)\n";
              megawiki_target := Some false;
	      if (!verbosity > 9) then (Printf.printf "Theorem %s admitted\n" thmname; flush stdout);
              if !pfgout && i = 0 && not !includingsigfile then pfgmain := PfgConj(gphv,thmname,gpgtm)::!pfgmain;
	      if (!ajax && !ajaxactive) then (Printf.printf "I$"; exit 1);
	      begin
		if !sqlout then
		  begin
		    match !mainfilehash with
		    | Some docsha ->
			if !sqltermout then Printf.printf "INSERT INTO `term` (`termid`,`termtp`,`termpoly`) VALUES ('%s','%s',%d);\n" gphv (stp_html_string Prop) i;
			if not !presentationonly then (Printf.printf "INSERT INTO `termdoc` (`termid`,`docsha`,`termdocname`,`termdockind`) VALUES ('%s','%s',\"%s\",'t');\n" gphv docsha (String.escaped thmname));
		    | None -> ()
		  end
	      end;
	      treasure := None;
              if not !allowincompleteqed then failwith "Qed is not allowed for a proof with admits, use Admitted instead."
	  end
	else
	  raise (Failure("Proof of " ^ thmname ^ " is incomplete"))
      end
  | Admitted ->
      begin
        if not (!currthm = "") then Hashtbl.add admittedthms !currthm ();
        currthm := "";
        if !sexprinfo then Printf.printf "(ADMITTED)\n";
        if !pfgout && i = 0 && not !includingsigfile then pfgmain := PfgConj(gphv,thmname,gpgtm)::!pfgmain;
	if i > 0 then (*** x will look polymorphic with i types after the appropriate section is ended ***)
	  pushpolypf ((thmname,i),gpgtm);
	activate_special_knowns gphv;
	sigpf := (thmname,!appfloc (Known(gphv)))::!sigpf;
	secstack := List.map (fun (y,f,atl,apl,st,sp) -> (y,f,atl,apl,st,(thmname,apl (Known(gphv)))::sp)) !secstack;
	proving := None;
        List.iter admitpfstateatp !pfstate;
        if fofp() && i = 0 && not (Hashtbl.mem fofskip gphv) then
          begin
            try
              fofsg := ("known",gphv,thmname,Printf.sprintf "fof(%s,axiom,%s). %% %s" (tptpize_name thmname) (fof_prop_str gpgtm [] 0) gphv)::!fofsg;
            with NotFO -> ()
          end;
        if th0p() && i = 0 && not (Hashtbl.mem th0skip gphv) then
          begin
            if not !bushy || Hashtbl.mem bushykdeps gphv then
              if !th0ps1 then
                (th0sgps1 := (Some(tm_deps gpgtm),Printf.sprintf "thf(%s,axiom,%s). %% %s" (tptpize_name thmname) (th0_str gpgtm []) gphv)::!th0sgps1)
              else
                (th0sg := ("known",gphv,thmname,Printf.sprintf "thf(%s,axiom,%s). %% %s" (tptpize_name thmname) (th0_str gpgtm []) gphv)::!th0sg)
          end;
	pfstate := [];
		treasure := None;
	begin
	  if !sqlout then
	    begin
	      match !mainfilehash with
	      | Some docsha ->
		  if !sqltermout then Printf.printf "INSERT INTO `term` (`termid`,`termtp`,`termpoly`) VALUES ('%s','%s',%d);\n" gphv (stp_html_string Prop) i;
		  if not !presentationonly then (Printf.printf "INSERT INTO `termdoc` (`termid`,`docsha`,`termdocname`,`termdockind`) VALUES ('%s','%s',\"%s\",'t');\n" gphv docsha (String.escaped thmname));
	      | None -> ()
	    end
	end;
        megawiki_target := Some false;
      end
  | Admit ->
      begin
	match !pfstate with
	| (pfst::pfstr) ->
	           admitpfstateatp pfst;
		   pfstate := pfstr;
		   prooffun := (fun _ -> raise AdmittedPf)
	| [] -> raise (Failure("No goal to admit"))
      end
  | Aby(xl) | VampireTac(xl) ->
      begin
        let certified_vampire_tac =
          match pitem with
          | VampireTac _ -> true
          | _ -> false
        in
	match !pfstate with
        | (PfStateGoal(startpos,claimtm,cxtm,cxpf) as pfst)::pfstr ->
           if certified_vampire_tac && !vampireaby = None then
             raise (Failure("vampire proof command requires -vampireaby"));
           if certified_vampire_tac && !vampireabyproof <> "megalodon" then
             raise (Failure("vampire proof command requires -vampireabyproof megalodon"));
           List.iter
             (fun x ->
               try
                 ignore (pfproplookup cxpf x)
               with Not_found ->
                     try
                       ignore (List.assoc x !sigpf !ctxtp cxtm cxpf)
                     with Not_found ->
	                   if x <> "-" then raise (Failure("Unknown proof " ^ x ^ " -- it might be a term in a position where a proof is expected")))
             xl;
           let checkfail fn = (Sys.file_exists fn && Sys.command ("grep -q '\\(Theorem\\|ContradictoryAxioms\\)' " ^ fn) = 1) in
           if !createabyprobs then
             begin
               begin
                 match !fof with
                 | None -> ()
                 | Some(c) ->
                    try
                      let z = fof_prop_str claimtm (tptpizecxtm cxtm) 0 in (** only if the conclusion is FO **)
                      let conjn = stable_aby_obligation_name () in
                      Buffer.clear sb;
                      let xfound : (string,unit) Hashtbl.t = Hashtbl.create 10 in
                      List.iter
                        (fun (cl,h,x,a) ->
                          if cl = "type" || cl = "def" && not (Hashtbl.mem sigdelta_opaque h) || cl = "known" && (List.mem x xl || xl = ["-"]) then
                            begin
                              Hashtbl.add xfound x ();
                              Buffer.add_string sb (Printf.sprintf "%s\n" a)
                            end)
                        (List.rev !fofsg);
                      List.iter
                        (fun (x,p) ->
                          if List.mem x xl then
                            let a = fof_prop_str p (tptpizecxtm cxtm) 0 in
                            Hashtbl.add xfound x ();
                            Buffer.add_string sb (Printf.sprintf "fof(%s,axiom,%s).\n" (tptpize_name x) a))
                        cxpf;
                      Buffer.add_string sb (Printf.sprintf "fof(conj_%s,conjecture,%s).\n" conjn z);
                      List.iter
                        (fun x -> if not (Hashtbl.mem xfound x) then raise NotFO)
                        xl;
                      let content = Buffer.contents sb in
                      if !abyproblemscached then
                        let fn = "cache/" ^ Hash.hashval_hexstring (Hash.sha256 content) ^ ".fof.p" in
                        if checkfail (fn ^ ".out") then Printf.printf "ERROR: aby at line %i char %i fails\n" !lineno !charno else
                        begin
                          let ch = open_out fn in
                          Printf.fprintf ch "%s" content;
                          close_out ch
                        end
                      else
                        begin
                          let fn = Printf.sprintf "%s.%d.%d.fof.p" c !lineno !charno in
                          let ch = open_out fn in
                          Printf.fprintf ch "%s" content;
                          close_out ch
                        end
                    with NotFO -> ()
               end;
               begin
                 match !th0 with
                 | None -> ()
                 | Some(c) ->
                    let conjn = stable_aby_obligation_name () in
                    let proof_command_label = if certified_vampire_tac then "vampire" else "aby" in
                    let content = th0_aby_problem_content ~origin_kind:proof_command_label claimtm cxtm cxpf xl conjn in
                    if !abyproblemscached then
                      let fn = "cache/" ^ Hash.hashval_hexstring (Hash.sha256 content) ^ ".thf.p" in
                      if checkfail (fn ^ ".out") then Printf.printf "ERROR: aby at line %i char %i fails\n" !lineno !charno else
                      begin
                        let ch = open_out fn in
                        Printf.fprintf ch "%s" content;
                        close_out ch
                      end
                    else
                      begin
                        let fn = Printf.sprintf "%s.%d.%d.th0.p" c !lineno !charno in
                        let ch = open_out fn in
                        Printf.fprintf ch "%s" content;
                        close_out ch
                      end
               end;
             end;
           begin
             let th0single_targeting =
               match !th0singlesubgoal with
               | None -> false
               | Some(_) -> true
             in
             let vampireaby_targeting =
               match !vampireabytarget with
               | None -> false
               | Some(ln,cn) -> not (!lineno = ln && !charno >= cn)
             in
             let skip_targeted_vampireaby =
               th0single_targeting || vampireaby_targeting
             in
             if certified_vampire_tac && skip_targeted_vampireaby then
               raise
                 (Failure
                    (Printf.sprintf
                       "vampire proof command at line %d char %d cannot be skipped by Vampire targeting"
                       !lineno
                       !charno));
             let require_vampire_native_certificate =
               (certified_vampire_tac || !vampireabynativestrict) && !vampireaby <> None && not skip_targeted_vampireaby
             in
             let native_aby_result =
               if !vampireabynative
                  && not require_vampire_native_certificate
                  && not skip_targeted_vampireaby
               then
                 native_aby_reconstruct claimtm cxtm cxpf xl
               else
                 None
             in
             let vampire_native_result = ref None in
             if not skip_targeted_vampireaby then begin
               match !vampireaby with
               | None -> ()
               | Some(_) ->
                  let conjn = stable_aby_obligation_name () in
                  let proof_command_label = if certified_vampire_tac then "vampire" else "aby" in
                  let content = th0_aby_problem_content ~origin_kind:proof_command_label claimtm cxtm cxpf xl conjn in
                  try
                    vampire_native_result :=
                      run_vampire_aby_certificate
                        ~claimtm
                        ~cxtm
                        ~cxpf
                        ~proof_command_label
                        content
                  with
                  | Failure(msg) ->
                     if require_vampire_native_certificate then
                       raise (Failure(msg))
                     else
                     begin
                       match native_aby_result with
                       | Some(_) ->
                          if !verbosity > 2 then
                            begin
                              Printf.printf
                                "Vampire did not certify aby at line %d char %d; using native reconstruction (%s)\n"
                                !lineno !charno msg;
                              flush stdout
                            end
                       | None -> raise (Failure(msg))
                     end
             end;
             begin
               if (!vampireabynative || certified_vampire_tac) && not skip_targeted_vampireaby then
                 let native_aby_result =
                   match !vampire_native_result with
                   | Some _ as result -> result
                   | None ->
                      if require_vampire_native_certificate then
                        raise
                          (Failure
                             (Printf.sprintf
                                "Vampire native certificate did not reconstruct current proof goal at line %d char %d"
                                !lineno !charno))
                      else
                        native_aby_result
                 in
                 match native_aby_result with
	                 | Some(d) ->
	                    let currprooffun = !prooffun in
	                    let endpos = Some(!lineno,!charno) in
	                    let final_debug_proof = ref None in
                            let final_debug_timing =
                              Sys.getenv_opt "MEGALODON_CERT_DEBUG_TIMING" = Some "1"
                            in
                            let final_timing_start = Unix.gettimeofday () in
                            let final_timing_last = ref final_timing_start in
                            let final_timing stage =
                              if final_debug_timing then
                                begin
                                  let now = Unix.gettimeofday () in
                                  Printf.printf
                                    "Vampire native final-closure timing %s at line %d char %d: +%.3fs total %.3fs.\n"
                                    stage
                                    !lineno
                                    !charno
                                    (now -. !final_timing_last)
                                    (now -. final_timing_start);
                                  final_timing_last := now;
                                  flush stdout
                                end
                            in
                            final_timing "local_fragment:available";
                            if Sys.getenv_opt "MEGALODON_CERT_DEBUG" = Some "1" then
                              begin
                                try
                                  final_timing "local_fragment_debug:start";
                                  let local_cx =
                                    List.map (fun (_, (tp, _)) -> tp) cxtm
                                  in
                                  let local_hyps = List.map snd cxpf in
                                  let actual, dl =
                                    extr_propofpf
                                      sigdelta
                                      sigtmof
                                      local_cx
                                      local_hyps
                                      d
                                      []
                                  in
                                  Printf.printf
                                    "Native reconstructed local proof fragment at line %d char %d.\nexpected local goal: %s\nactual local proof: %s\nlocal convertible: %s\n"
                                    !lineno
                                    !charno
                                    (tm_to_str claimtm)
                                    (tm_to_str actual)
                                    (match conv actual claimtm sigdelta dl with
                                     | Some _ -> "yes"
                                     | None -> "no");
                                  begin match
                                    check_propofpf
                                      sigdelta
                                      sigtmof
                                      local_cx
                                      local_hyps
                                      d
                                      claimtm
                                      []
                                  with
                                  | Some _ ->
                                      Printf.printf
                                        "Native reconstructed local proof fragment checks against current goal at line %d char %d.\n"
                                        !lineno
                                        !charno
                                  | None ->
                                      Printf.printf
                                        "Native reconstructed local proof fragment does not check against current goal at line %d char %d.\n"
                                        !lineno
                                        !charno
                                      end;
                                  flush stdout;
                                  final_timing "local_fragment_debug:done"
                                with exn ->
                                  begin
                                    begin match
                                      vampire_debug_missing_live_reference
                                        sigdelta
                                        sigtmof
                                        d
                                    with
                                    | Some detail ->
                                        Printf.printf
                                          "Native reconstructed local proof fragment missing live reference at line %d char %d: %s\n"
                                          !lineno
                                          !charno
                                          detail
                                    | None -> ()
                                    end;
                                    begin match
                                      vampire_debug_bad_proof_application
                                        sigdelta
                                        sigtmof
                                        (List.map (fun (_, (tp, _)) -> tp) cxtm)
                                        (List.map snd cxpf)
                                        d
                                    with
                                    | Some detail ->
                                        Printf.printf
                                          "Native reconstructed local proof fragment bad application at line %d char %d: %s\n"
                                          !lineno
                                          !charno
                                          detail
                                    | None -> ()
                                    end;
                                    Printf.printf
                                      "Native reconstructed local proof fragment proposition extraction failed at line %d char %d: %s\n"
                                      !lineno
                                      !charno
                                      (Printexc.to_string exn);
                                    flush stdout;
                                  final_timing "local_fragment_debug:failed"
                                  end
                              end;
	                    let final_closure_checks =
	                      if pfstr <> [] then true
                              else if Sys.getenv_opt "MEGALODON_CERT_FINAL_LOCAL_CHECK" <> Some "1" then
                                true
	                      else
	                        try
                          final_timing "local_check:start";
                          let local_cx =
                            List.map (fun (_, (tp, _)) -> tp) cxtm
                          in
                          let local_hyps = List.map snd cxpf in
                          match
                            check_propofpf
                              sigdelta
                              sigtmof
                              local_cx
                              local_hyps
                              d
                              claimtm
                              []
                          with
                          | None ->
                              final_timing "local_check:failed";
                              false
                          | Some _ ->
                              final_timing "local_check:done";
                              if Sys.getenv_opt "MEGALODON_CERT_FULL_FINAL_CHECK" <> Some "1" then
                                true
                              else
                                begin
                                  final_timing "currprooffun:start";
                                  let dgpf = currprooffun [(endpos,d)] in
                                  final_timing "currprooffun:done";
                                  final_timing "optimize_pf_1:start";
                                  let dgpf = if !optimizepf1 then optimize_pf_1 dgpf else dgpf in
                                  final_timing "optimize_pf_1:done";
                                  final_timing "optimize_pf_2:start";
                                  let dgpf =
                                    if !optimizepf2 then
                                      optimize_pf_2
                                        sigdelta
                                        sigtmof
                                        dgpf
                                        !optimizepf2tc
                                        !optimizepf2pc
                                    else dgpf
                                  in
                                  final_timing "optimize_pf_2:done";
                                  final_timing "normalize_pf:start";
                                  let dgpf = if !normalizepf then normalize_pf dgpf else dgpf in
                                  final_timing "normalize_pf:done";
                                  final_debug_proof := Some dgpf;
                                  final_timing "full_check_propofpf:start";
                                  match
                                    if !doublecheckpf then
                                      check_propofpf sigdelta sigtmof [] [] dgpf gpgtm !deltaset
                                    else
                                      Some(!deltaset)
                                  with
                                  | Some _ ->
                                      final_timing "full_check_propofpf:done";
                                      true
                                  | None ->
                                      final_timing "full_check_propofpf:failed";
                                      if Sys.getenv_opt "MEGALODON_CERT_DEBUG" = Some "1" then
                                        begin
                                          try
                                            let actual, dl =
                                              extr_propofpf sigdelta sigtmof [] [] dgpf []
                                            in
                                            Printf.printf
                                              "Native reconstructed final proof has wrong proposition at line %d char %d.\nexpected: %s\nactual: %s\nconvertible: %s\n"
                                              !lineno
                                              !charno
                                              (tm_to_str gpgtm)
                                              (tm_to_str actual)
                                              (match conv actual gpgtm sigdelta dl with
                                               | Some _ -> "yes"
                                               | None -> "no");
                                            flush stdout
                                          with exn ->
                                            Printf.printf
                                              "Native reconstructed final proof proposition extraction failed at line %d char %d: %s\n"
                                              !lineno
                                              !charno
                                              (Printexc.to_string exn);
                                            flush stdout
                                        end;
                                      false
                                end
                        with
                        | Failure msg ->
                            final_timing "final_closure:failure";
                            if !verbosity > 8 then
                              begin
                                Printf.printf
                                  "Native reconstructed proof term does not close final theorem at line %d char %d: %s.\n"
                                  !lineno
                                  !charno
                                  msg;
                                if Sys.getenv_opt "MEGALODON_CERT_DEBUG" = Some "1" then
                                  begin match !final_debug_proof with
                                  | None -> ()
                                  | Some dgpf ->
                                      begin match
                                        vampire_debug_bad_proof_application
                                          sigdelta
                                          sigtmof
                                          []
                                          []
                                          dgpf
                                  with
                                  | Some detail ->
                                      Printf.printf
                                        "Native reconstructed final proof bad application at line %d char %d: %s\n"
                                        !lineno
                                        !charno
                                        detail
                                  | None -> ()
                                      end
                                  end;
                                flush stdout
                              end;
                            false
                        | _ ->
                            final_timing "final_closure:exception";
                            false
                    in
                    if not final_closure_checks then
                      raise
                        (Failure
                           (Printf.sprintf
                              "Native reconstruction produced a local proof term that does not close the final theorem at line %d char %d"
                              !lineno
                              !charno));
                    if !verbosity > 2 then
                      begin
                        Printf.printf
                          "Vampire certified %s at line %d char %d.\n"
                          (if certified_vampire_tac then "vampire" else "aby")
                          !lineno
                          !charno;
                        flush stdout
                      end;
                    prooffun := (fun dl -> currprooffun ((endpos,d)::dl));
                    pfstate := pfstr;
                    if certified_vampire_tac && !verbosity > 2 then
                      begin
                        Printf.printf
                          "Vampire proof command reconstructed proof term at line %d char %d.\n"
                          !lineno
                          !charno;
                        flush stdout
                      end;
                    if !vampireabytargetstop then
                      begin
                        if certified_vampire_tac then
                          Printf.printf
                            "Vampire target stop after reconstructed proof term at line %d char %d.\n"
                            !lineno
                            !charno
                        else
                          Printf.printf
                            "Vampire target stop after reconstructed aby proof term at line %d char %d.\n"
                            !lineno
                            !charno;
                        flush stdout;
                        exit 0
                      end
                 | None ->
                    if certified_vampire_tac || !vampireabynativestrict then
                      raise
                        (Failure
                           (if certified_vampire_tac then
                              Printf.sprintf "Native reconstruction failed for certified Vampire proof at line %d char %d" !lineno !charno
                            else
                              Printf.sprintf "Native reconstruction failed for certified aby at line %d char %d" !lineno !charno))
                    else
                      begin
	                admitpfstateatp pfst;
		        pfstate := pfstr;
		        prooffun := (fun _ -> raise AdmittedPf)
                      end
               else
                 begin
	           admitpfstateatp pfst;
	           pfstate := pfstr;
		   prooffun := (fun _ -> raise AdmittedPf)
	                 end
	             end
           end
	| _ ->
           if certified_vampire_tac then
             raise (Failure("No goal for Vampire proof command"))
           else
             raise (Failure("No goal to aby"))
      end
  | SpecialTac(x,[]) when x = "distinct" ->
     begin
       if !pfgtheory = HOAS then
         begin
           match !pfstate with
           | PfStateGoal(startpos,claimtm,cxtm,cxpf)::pfstr ->
              begin
                let pair_p h = h = "d58762d200971dcc7f1850726d9f2328403127deeba124fc3ba2d2d9f7c3cb8c" in
                let bind_p h = h = "73c9efe869770ab42f7cde0b33fe26bbc3e2bd157dad141c0c27d1e7348d60f5" in
                let nil_p h = h = "f2f23aaed49035f6a02316839e024937b84f34a64984a739b9926cab5a542a5f" in
                let pair_inj_1 = "457b940661b14b2f6c55f4e7605ad9a08b93a9b227b7e4878ddffc6e57df03a2" in
                let pair_inj_2 = "73f4a4caf8cee16dce31f48373fcde8d22191ae8296b2b2bf68179080d71a009" in
                let bind_inj_ap = "8fdd8c4b6d2d33c21317e9fc8ac0f977b3b46107d8cc02f74d0fed4687b9c56d" in
                let pair_not_bind = "a23f2c1f208ea6ea3b76e405265b31ec3200243c72060d4f98bb444454185d06" in
                let bind_not_pair = "fcdac3008d43d05308faafb376db2dfeb46eab33d92fa74e62cb0e1cd7c2ebdb" in
                let neq_nil_pair = "1bc9e5a6bb4b9fc4bcea4014f16d6bce1e24d81a4ac53f43308fd4fc2341d7b2" in
                let neq_pair_nil = "b607690c256cba399c9e93b5e9eba9ff5076b96d3db0cdd3d5a7d7265d94153e" in
                let neq_nil_bind_bind = "f345e493f800501229a81468d5fa1d95d06a9553d7e0fcf7224a17b5bd031df7" in
                let neq_nil_bind_pair = "cd9ce7241c739c03b20b982846667c257ce793909e22508b22eccd7c6cb6299c" in
                let neq_bind_bind_nil = "40c1e7e6df27ccc363e7453d25a4e162fc682a1302e1a1fa0e80d81335f1f8b9" in
                let neq_bind_pair_nil = "aff40b8394f4b562125e5dd663ac533a7b5cb32141da97ac07aba16892910c66" in
                let neq_bind_nil_nil = "b0d0dea69aaf4f5154a19e1dc220feb9ff274d1be96686a1dd935b52d206c5e4" in
                let neq_nil_bind_nil = "b3f848b81475c0ad6324c86de54a34b2c73046e7317705a6ded788fdae822e2d" in
                let nil = TmH("f2f23aaed49035f6a02316839e024937b84f34a64984a739b9926cab5a542a5f") in
                let nil2 = Ap(Ap(TmH("d58762d200971dcc7f1850726d9f2328403127deeba124fc3ba2d2d9f7c3cb8c"),nil),nil) in
                let rec distinct_hoas_2 m n d =
                  match m with
                  | TmH(h) when nil_p h ->
                     begin
                       match n with
                       | Ap(Ap(TmH(h),n1),n2) when pair_p h ->
                          PPfAp(PTmAp(PTmAp(Known(neq_nil_pair),n1),n2),d)
                       | Ap(TmH(h),Lam(Set,TmH(k))) when bind_p h && nil_p k ->
                          PPfAp(Known(neq_nil_bind_nil),d)
                       | Ap(TmH(h),Lam(Set,Ap(Ap(TmH(k),n1),n2))) when bind_p h && pair_p k ->
                          PPfAp(PTmAp(PTmAp(Known(neq_nil_bind_pair),Lam(Set,n1)),Lam(Set,n2)),d)
                       | Ap(TmH(h),Lam(Set,Ap(TmH(k),n1))) when bind_p h && bind_p k ->
                          PPfAp(PTmAp(Known(neq_nil_bind_bind),Lam(Set,n1)),d)
                       | _ -> raise (Failure "distinct failed nil vs ?")
                     end
                  | Ap(Ap(TmH(h),m1),m2) when pair_p h ->
                     begin
                       match n with
                       | TmH(h) when nil_p h ->
                          PPfAp(PTmAp(PTmAp(Known(neq_pair_nil),m1),m2),d)
                       | Ap(Ap(TmH(h),n1),n2) when pair_p h ->
                          if m1 = n1 then
                            distinct_hoas_2 m2 n2 (PPfAp(PTmAp(PTmAp(PTmAp(PTmAp(Known(pair_inj_2),m1),m2),n1),n2),d))
                          else
                            distinct_hoas_2 m1 n1 (PPfAp(PTmAp(PTmAp(PTmAp(PTmAp(Known(pair_inj_1),m1),m2),n1),n2),d))
                       | Ap(TmH(h),n1) when bind_p h ->
                          PPfAp(PTmAp(PTmAp(PTmAp(Known(pair_not_bind),m1),m2),n1),d)
                       | _ -> raise (Failure "distinct failed pair vs ?")
                     end
                  | Ap(TmH(h),(Lam(Set,m1b) as m1)) when bind_p h ->
                     begin
                       match n with
                       | TmH(h) when nil_p h ->
                          begin
                            match m1b with
                            | TmH(h) when nil_p h ->
                               PPfAp(Known(neq_bind_nil_nil),d)
                            | Ap(Ap(TmH(h),m2),m3) when pair_p h ->
                               PPfAp(PTmAp(PTmAp(Known(neq_bind_pair_nil),Lam(Set,m2)),Lam(Set,m3)),d)
                            | Ap(TmH(h),m2) when bind_p h ->
                               PPfAp(PTmAp(Known(neq_bind_bind_nil),Lam(Set,m2)),d)
                            | _ -> raise (Failure "distinct failed bind ? vs nil")
                          end
                       | Ap(Ap(TmH(h),n1),n2) when pair_p h ->
                          PPfAp(PTmAp(PTmAp(PTmAp(Known(bind_not_pair),m1),n1),n2),d)
                       | Ap(TmH(h),(Lam(Set,n1b) as n1)) when bind_p h ->
                          let m1c = tmsubst m1b 0 nil in
                          let n1c = tmsubst n1b 0 nil in
                          if m1c = n1c then
                            let m1c = tmsubst m1b 0 nil2 in
                            let n1c = tmsubst n1b 0 nil2 in
                            if m1c = n1c then
                              raise (Failure "distinct failed in an impossible way")
                            else
                              distinct_hoas_2 m1c n1c
                                (PPfAp(PTmAp(PTmAp(PTmAp(Known(bind_inj_ap),m1),n1),nil2),d))
                          else
                            distinct_hoas_2 m1c n1c
                              (PPfAp(PTmAp(PTmAp(PTmAp(Known(bind_inj_ap),m1),n1),nil),d))
                       | _ -> raise (Failure "distinct failed bind vs ?")
                     end
                  | _ -> raise (Failure "distinct failed ? vs _")
                in
                let distinct_hoas m n =
                  let d = PLam(Ap(Ap(TpAp(TmH("5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a"),Set),m),n),distinct_hoas_2 m n (Hyp(0))) in
                  let endpos = Some(!lineno,!charno) in
                  let currprooffun = !prooffun in
                  prooffun := (fun dl -> currprooffun ((endpos,d)::dl));
                  pfstate := pfstr
                in
                match claimtm with
                | Ap(Ap(TpAp(TmH(h),Set),m),n) when h = "7966a66a9bb198103c2a540ccd5ebebdff33c10843cc10eebfc98715e142989c" && not (m = n) ->
                   distinct_hoas m n
                | Imp(Ap(Ap(TpAp(TmH(h),Set),m),n),TmH(k)) when h = "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a" && k = !fal && not (m = n) ->
                   distinct_hoas m n
                | Imp(Ap(Ap(TpAp(TmH(h),Set),m),n),All(Prop,DB(0))) when h = "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a" && not (m = n) ->
                   distinct_hoas m n
                | _ -> raise (Failure "distinct tactic requires goal to be diseqn")
              end
           | _ -> raise (Failure "distinct tactic requires a goal")
         end
       else if !pfgtheory = Egal then
         begin
           match !pfstate with
           | PfStateGoal(startpos,claimtm,cxtm,cxpf)::pfstr ->
              begin
                let empty = "e2a83319facad3a3d8ff453f4ef821d9da495e56a623695546bb7d7ac333f3fe" in
                let ordsucc = "9db634daee7fc36315ddda5f5f694934869921e9c5f55e8b25c91c0a07c5cbec" in
                let ap = "58c1782da006f2fb2849c53d5d8425049fad551eb4f8025055d260f0c9e1fe40" in
                let seqcons = "7a7fd30507c2156eeace3d2784ada104fee81316a9d6f02db384ad7f0a180e26" in
                let ordsucc_inj_contra = "c14fd6fe2e5850baa4c1ccd03bdaba358bff7548a20bfc48adeaa2b0e25f954a" in
                let omega_0 = "bbcf0e220bcdf977752b81f9870f771a8f4c40280650ea2d6db27815db42a076" in
                let omega_1 = "e72d3a03fe620df3b005cd8f14e3371c74198d7831c51a5aa8fe55579b3b27e1" in
                let omega_2 = "1debfa007905ce354ac9ae49484625ee7b38559c01f9dde9f65da732bd66c17c" in
                let omega_3 = "16487b74fc6769a27b41420352ff54c3910af996d931abd293e56e9052adce24" in
                let omega_4 = "c7e3e0042f8c0b1465a73053ba5334d188c2c5b5788b5d62176e5253855105ff" in
                let omega_5 = "3aef5fcf45d766379ba44b1d68757bb530afad3889f68f958f3c75e691d6ac1c" in
                let omega_6 = "776254dacdcd5305a2d088e32f35349284ac9469a48d75d6c42c0ca30b0f41a8" in
                let omega_7 = "dab4795d867a70ec3aeb2e69527fd0c5a2b046f2e0651b0bc81ace97b9223a78" in
                let omega_8 = "9ed3fe2c43815cc21075da094e596727c1075e6cd0d9837197cf5f9fd8362b76" in
                let omega_9 = "440819f34c1019a1ea2d5a73690079ffe9a34e9bd2bfb22fcbbf3d0e8ac014c8" in
                let neq_0_1 = "2a012236fc59f277a006afea6589576917b98079dfa3b365b27050d0e9d91f80" in
                let neq_1_0 = "a96636a83cef72bedda13177ba1f197ac6b6dab4613cc8062584e25c143b84fa" in
                let neq_2_0 = "76555b2fee92c2ef5efd3b1992a67dc11fd63bdea9e5147e490c7e1ae4ee037b" in
                let neq_2_1 = "135568bce4957f8ff275fe7875a26c3a288753a68ac4c21f361d110205b652b1" in
                let neq_3_0 = "6bc86ccb84fb960ec861595b19cca0513d4d04fa60f52d048d03bf4db383b0b9" in
                let neq_3_1 = "bbf0a972daf94de44ca9e6714156288860c0ee07faddced2a33a85d436ce3a85" in
                let neq_3_2 = "ddf0ba7e2399c5fdeb0b501ea721f58182b15ac29fdf19dfe797bb25c4b9d419" in
                let neq_4_0 = "45b3a962a198a7091fb2788ad6766dee9ff53d745ce48abdc56a15a3205bcd09" in
                let neq_4_1 = "78b075d44317f00feb434db7dd5d19ad03a97cc90231e81c2bb7c6e392ceff0e" in
                let neq_4_2 = "9728fc1c149dfd2b4011120ea562b36537741ea5e113b683baaae09b8f631c15" in
                let neq_4_3 = "2a2127eee38e3aea9338de549dbabe0bdbdc1313ca911e3a4fa85ad4692976e4" in
                let neq_5_0 = "659c883887b5b2348a98be074c4f7198381d197b7976fa7f4401683d65ee328f" in
                let neq_5_1 = "3fafec5ee2d00ed3e6dbd318e58d8f869d482a57bc398bc941ffa3ee7d9b4482" in
                let neq_5_2 = "ac3a8a725a92461e10265875c0dd4faa6ac70a45646a02a43c26ef9602edb367" in
                let neq_5_3 = "b57ba763b444014afea17778d853859c8bc75d2c82396d2de346e491c7f0942e" in
                let neq_5_4 = "70bc8cbf0960ef0a1d6db3bd2f26a3815844a96214810b428fb78503bd686b4f" in
                let neq_6_0 = "bfad1824a78e812e31f842faa26d565c7aa43da9fc3a955812cf51a8ecec21bc" in
                let neq_6_1 = "26640fd5441a57a61669bc1ae992569b73e739e9214215a28039aa5d04cd1cad" in
                let neq_6_2 = "41fa60d271f99cad3c1cb11c0430cddbb657c03a3c9dcb7facc96d0137fac8c8" in
                let neq_6_3 = "ff0841068e1303a6ee65eed594b7f9f8c22d5fc19da35436fba58b8d8bd16ad6" in
                let neq_6_4 = "7135026aaf75491aad27a55a73486ca9db35da4d97b1f152d26dd4866624e1df" in
                let neq_6_5 = "ee2feea2a607ac27e097cf82c74c2ac3239ebe9b39d1ca4841b108680ec60bdd" in
                let neq_7_0 = "036f041c0fa6749260db7745cd709fb3641acbed368f22cd76a2343d587bc049" in
                let neq_7_1 = "4df9782c7ce6454e4b5b8c6916468843ce1f45b87831c521fabd85057e7a4da7" in
                let neq_7_2 = "6d1921aea0ca49ec01a2e2b83bb9fed901466d18eb4aafc4217f64508474808a" in
                let neq_7_3 = "16130c0707547c532c8bde3a5f9333d003707b9c05f8fb2bb987447c6fe6df0f" in
                let neq_7_4 = "d21557722bb427617660a8620a34c204e7f35ba10d69d3bcb5f76b2867c126eb" in
                let neq_7_5 = "6a50d61b0a6a158130d45abfd1d3f55b910591868ba88b6dcda3e099693422b2" in
                let neq_7_6 = "50e31bdb74debec57e94dbfd0e2b3d9c10adc76d6db45470e7d600f319bd098f" in
                let neq_8_0 = "58432f5a9025e83c0e98a97fdac4250f42c78ca43fd4e5a3f5ba935f740fb07d" in
                let neq_8_1 = "4fef6b56e6a29a11789695843cd65d75589e723894d09024730575403a385066" in
                let neq_8_2 = "4a3f78215e3ab72f328439a7a3aa0638de35309642508ee69891e8828f594e30" in
                let neq_8_3 = "42e18bc47b79fdd696990d53f07c8f936465d0a9cb9bc2a9118971e3994fdbef" in
                let neq_8_4 = "3fcba92db38e6b18020633e43a169bc0ff5a7a98bd01a0e042ed65b9e3177423" in
                let neq_8_5 = "12a63db797bf7dc38ebcc8182c323495e47839c8f56c53c3a96f4e61fa2f356c" in
                let neq_8_6 = "3c1c85cfb0a576724c0fd7548fa2ed36e5b747f4e51357a041bb6f6d3fcf4b59" in
                let neq_8_7 = "4f278419d05a30316178e195b67eba36793a0c3b0f5f215288bfd9bfac34086e" in
                let neq_9_0 = "7023756fd839c4b7ebf30b02c856f5ad1fc3c359701f79904bff48841ddadf38" in
                let neq_9_1 = "2c30786dd7e2b3eb7a8b816bd7b28f8398817fe880fa18bde3cff8efc4aa57af" in
                let neq_9_2 = "72898cc3b39b91929f3a6e08863d33547bd20d213b6a6e55dae72803c156a44d" in
                let neq_9_3 = "9c36f33d36433469e3f69e512396362343c2492967143dfb16eab54d7d20afd5" in
                let neq_9_4 = "1983e8af533cd22d8688a303f19a7557a6024a0e20ef7a380fbceafd85f24b71" in
                let neq_9_5 = "5a746a843ef271ad2dd35d629d1a24a38497b1fc29dc3458edec02ad672490db" in
                let neq_9_6 = "bbe50369f94f084e124f71804a36dcfd3428283c447f07e42d955800bdd13ce0" in
                let neq_9_7 = "b6be74e8405fd99ec9fe15fca804e40902963bbf03738c5c0b0ba79cafc289bd" in
                let neq_9_8 = "9afd8e465b5919eeac913849640e4e8192964f11e9b31f59d2c8966910c2d262" in
                let neq_0_ordsucc = "cd16045e375d4af84d5e4935492f9372af2c1df516250653f67f2eabce3e1a96" in
                let neq_ordsucc_0 = "10d9661442ca65e01bc41935f4cb9aa6a33342df51d9e7dd2fd94e6c575e9dda" in
                let neq_i_sym = "5975ea0d667ef81890db1136e825d1bda7a0dec6bacfabb8f8c03bae6c9d6bde" in
                let ap_const_0 = "af2119ddb02d9f2271a6b2b76c6f50827be8080ea4aa8e4f3c6a91c17dd873a3" in
		let neq0_ap0 = "4803f585e97b1d8fdd5d35d0ad0e9a3a2bb64a7a3e3d79ce9f5c45f8a99cdca8" in
                let seq_cons_0 = "194a4a83e17384dc5acafa81e964161d02bd5bff0e2b087e0f02d19431dfde61" in
                let seq_cons_S_tra = "7e021728a91828d3f12899d2d7ed342ae7db555450d2138904d8a2ab21d9401d" in
                let omega_ordsucc = "f88efc1bceb13c969121ead8cc2c43f0ce2f1c2aeeab14ec80e7cbae241b81b8" in
                let rec unary_nat m =
                  if m > 0 then
                    Ap(TmH(ordsucc),unary_nat (m-1))
                  else
                    TmH(empty)
                in
                let rec omega_nat m =
                  if m > 9 then
                    PPfAp(PTmAp(Known(omega_ordsucc),unary_nat (m-1)),omega_nat (m-1))
                  else if m = 0 then
                    Known(omega_0)
                  else if m = 1 then
                    Known(omega_1)
                  else if m = 2 then
                    Known(omega_2)
                  else if m = 3 then
                    Known(omega_3)
                  else if m = 4 then
                    Known(omega_4)
                  else if m = 5 then
                    Known(omega_5)
                  else if m = 6 then
                    Known(omega_6)
                  else if m = 7 then
                    Known(omega_7)
                  else if m = 8 then
                    Known(omega_8)
                  else if m = 9 then
                    Known(omega_9)
                  else
                    raise (Failure "distinct failed")
                in
                let rec unary_nat_p m =
                  match m with
                  | TmH(h) when h = empty -> true
                  | Ap(TmH(h),m1) when h = ordsucc -> unary_nat_p m1
                  | _ -> false
                in
                let rec seq_over_p p m = (** this includes bytes when p = unary_nat_p and includes strings when p = seq_over_p unary_nat_p **)
                  match m with
                  | TmH(h) when h = empty -> true
                  | Ap(Ap(TmH(h),x),s) when h = seqcons -> p x && seq_over_p p s
                  | _ -> false
                in
                let rec eval_unary_nat m =
                  match m with
                  | TmH(h) when h = empty -> 0
                  | Ap(TmH(h),m1) when h = ordsucc -> 1+eval_unary_nat m1
                  | _ -> raise (Failure "distinct failed")
                in
                let unary_nat_special_case m n =
                  if m = 1 && n = 0 then
                    neq_1_0
                  else if m = 2 && n = 0 then
                    neq_2_0
                  else if m = 2 && n = 1 then
                    neq_2_1
                  else if m = 3 && n = 0 then
                    neq_3_0
                  else if m = 3 && n = 1 then
                    neq_3_1
                  else if m = 3 && n = 2 then
                    neq_3_2
                  else if m = 4 && n = 0 then
                    neq_4_0
                  else if m = 4 && n = 1 then
                    neq_4_1
                  else if m = 4 && n = 2 then
                    neq_4_2
                  else if m = 4 && n = 3 then
                    neq_4_3
                  else if m = 5 && n = 0 then
                    neq_5_0
                  else if m = 5 && n = 1 then
                    neq_5_1
                  else if m = 5 && n = 2 then
                    neq_5_2
                  else if m = 5 && n = 3 then
                    neq_5_3
                  else if m = 5 && n = 4 then
                    neq_5_4
                  else if m = 6 && n = 0 then
                    neq_6_0
                  else if m = 6 && n = 1 then
                    neq_6_1
                  else if m = 6 && n = 2 then
                    neq_6_2
                  else if m = 6 && n = 3 then
                    neq_6_3
                  else if m = 6 && n = 4 then
                    neq_6_4
                  else if m = 6 && n = 5 then
                    neq_6_5
                  else if m = 7 && n = 0 then
                    neq_7_0
                  else if m = 7 && n = 1 then
                    neq_7_1
                  else if m = 7 && n = 2 then
                    neq_7_2
                  else if m = 7 && n = 3 then
                    neq_7_3
                  else if m = 7 && n = 4 then
                    neq_7_4
                  else if m = 7 && n = 5 then
                    neq_7_5
                  else if m = 7 && n = 6 then
                    neq_7_6
                  else if m = 8 && n = 0 then
                    neq_8_0
                  else if m = 8 && n = 1 then
                    neq_8_1
                  else if m = 8 && n = 2 then
                    neq_8_2
                  else if m = 8 && n = 3 then
                    neq_8_3
                  else if m = 8 && n = 4 then
                    neq_8_4
                  else if m = 8 && n = 5 then
                    neq_8_5
                  else if m = 8 && n = 6 then
                    neq_8_6
                  else if m = 8 && n = 7 then
                    neq_8_7
                  else if m = 9 && n = 0 then
                    neq_9_0
                  else if m = 9 && n = 1 then
                    neq_9_1
                  else if m = 9 && n = 2 then
                    neq_9_2
                  else if m = 9 && n = 3 then
                    neq_9_3
                  else if m = 9 && n = 4 then
                    neq_9_4
                  else if m = 9 && n = 5 then
                    neq_9_5
                  else if m = 9 && n = 6 then
                    neq_9_6
                  else if m = 9 && n = 7 then
                    neq_9_7
                  else if m = 9 && n = 8 then
                    neq_9_8
                  else
                    raise (Failure "distinct failed")
                in
                let rec distinct_egal_unary_nat_r m m1 n n1 =
                  if m1 = 0 && n1 = 1 then
                    Known(neq_0_1)
                  else if m1 > n1 && m1 < 10 then
                    Known(unary_nat_special_case m1 n1)
                  else if n1 > m1 && n1 < 10 then
                    PPfAp(PTmAp(PTmAp(Known(neq_i_sym),n),m),Known(unary_nat_special_case n1 m1))
                  else
                    match (m,n) with
                    | (Ap(_,mp),Ap(_,np)) ->
                       PPfAp(PTmAp(PTmAp(Known(ordsucc_inj_contra),mp),np),distinct_egal_unary_nat_r mp (m1-1) np (n1-1))
                    | (TmH(h),Ap(_,np)) when h = empty ->
                       PTmAp(Known(neq_0_ordsucc),np)
                    | (Ap(_,mp),TmH(h)) when h = empty ->
                       PTmAp(Known(neq_ordsucc_0),mp)
                    | _ -> raise (Failure "distinct failed")
                in
                let distinct_egal_unary_nat m n =
                  let m1 = eval_unary_nat m in
                  let n1 = eval_unary_nat n in
                  distinct_egal_unary_nat_r m m1 n n1
                in
                let distinct_egal_unary_nat_ne m =
                  let m1 = eval_unary_nat m in
                  distinct_egal_unary_nat_r m m1 (TmH(empty)) 0
                in
                let rec distinguishing_elt m n i =
                  match (m,n) with
                  | (Ap(Ap(_,x),mr),Ap(Ap(_,y),nr)) ->
                     if x = y then
                       distinguishing_elt mr nr (1+i)
                     else
                       (i,Some(x),Some(y))
                  | (Ap(Ap(TmH(_),x),_),TmH(h)) when h = empty ->
                     (i,Some(x),None)
                  | (TmH(h),Ap(Ap(TmH(_),y),_)) when h = empty ->
                     (i,None,Some(y))
                  | _ ->
                     (i,None,None)
                in
                let rec seq_at_eq_0 m i =
                  match m with
                  | TmH(h) when h = empty -> PTmAp(Known(ap_const_0),unary_nat i)
                  | Ap(Ap(TmH(h),x),mr) when h = seqcons ->
                     if i > 0 then
                       let d = seq_at_eq_0 mr (i-1) in
                       PPfAp(PPfAp(PTmAp(PTmAp(PTmAp(PTmAp(Known(seq_cons_S_tra),x),mr),TmH(empty)),unary_nat (i-1)),omega_nat (i-1)),d)
                     else
                       raise (Failure "distinct failed")
                  | _ -> raise (Failure "distinct failed")
                in
                let rec seq_at_eq m i x =
                  match m with
                  | Ap(Ap(TmH(h),y),mr) when h = seqcons ->
                     if i > 0 then
                       PPfAp(PPfAp(PTmAp(PTmAp(PTmAp(PTmAp(Known(seq_cons_S_tra),y),mr),x),unary_nat (i-1)),omega_nat (i-1)),seq_at_eq mr (i-1) x)
                     else
                       PTmAp(PTmAp(Known(seq_cons_0),x),mr)
                  | _ -> raise (Failure "distinct failed")
                in
                let distinct_egal_seq_over_ne dne m =
                  match m with
                  | Ap(Ap(TmH(h),x),mr) when h = seqcons ->
                     let dnex = dne x in (** pf of x <> 0 **)
                     let dm0x = seq_at_eq m 0 x in (** pf of m 0 = x **)
                     (** pf of m <> 0 **)
                     PPfAp(PPfAp(PTmAp(PTmAp(PTmAp(Known(neq0_ap0),m),TmH(empty)),x),dm0x),dnex)
                  | _ -> raise (Failure "distinct failed")
                in
                let distinct_egal_seq_over d dne m n =
                  match distinguishing_elt m n 0 with
                  | (i,Some(x),Some(y)) ->
                     let dmix = seq_at_eq m i x in (** pf of m i = x **)
                     let dniy = seq_at_eq n i y in (** pf of n i = y **)
                     let ddif = d x y in (** pf of x <> y **)
                     (** pf of m <> n **)
                     PLam(Ap(Ap(TpAp(TmH("5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a"),Set),m),n),PPfAp(ddif,PPfAp(PTmAp(PPfAp(PTmAp(Hyp(0),Lam(Set,Lam(Set,Ap(Ap(TpAp(TmH("5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a"),Set),Ap(Ap(TmH(ap),DB(1)),unary_nat i)),x)))),dmix),Lam(Set,Lam(Set,Ap(Ap(TpAp(TmH("5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a"),Set),DB(1)),y)))),dniy)))
                  | (i,Some(x),None) ->
                     let dmix = seq_at_eq m i x in (** pf of m i = x **)
                     let dni0 = seq_at_eq_0 n i in (** pf of n i = 0 **)
                     let dnex = dne x in (** pf of x <> 0 **)
                     PLam(Ap(Ap(TpAp(TmH("5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a"),Set),m),n),PPfAp(dnex,PPfAp(PTmAp(PPfAp(PTmAp(Hyp(0),Lam(Set,Lam(Set,Ap(Ap(TpAp(TmH("5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a"),Set),Ap(Ap(TmH(ap),DB(1)),unary_nat i)),x)))),dmix),Lam(Set,Lam(Set,Ap(Ap(TpAp(TmH("5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a"),Set),DB(1)),TmH(empty))))),dni0)))
                  | (i,None,Some(y)) ->
                     let dmi0 = seq_at_eq_0 m i in (** pf of m i = 0 **)
                     let dniy = seq_at_eq n i y in (** pf of n i = y **)
                     let dney = dne y in (** pf of y <> 0 **)
                     PLam(Ap(Ap(TpAp(TmH("5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a"),Set),m),n),PPfAp(dney,PPfAp(PTmAp(PPfAp(PTmAp(Hyp(0),Lam(Set,Lam(Set,Ap(Ap(TpAp(TmH("5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a"),Set),Ap(Ap(TmH(ap),DB(0)),unary_nat i)),y)))),dniy),Lam(Set,Lam(Set,Ap(Ap(TpAp(TmH("5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a"),Set),DB(1)),TmH(empty))))),dmi0)))
                  | (i,None,None) -> raise (Failure "distinct failed")
                in
                let distinct_egal_1 m n =
                  if unary_nat_p m && unary_nat_p n then
                    distinct_egal_unary_nat m n
                  else if seq_over_p unary_nat_p m && seq_over_p unary_nat_p n then
                    distinct_egal_seq_over distinct_egal_unary_nat distinct_egal_unary_nat_ne m n
                  else if seq_over_p (seq_over_p unary_nat_p) m && seq_over_p (seq_over_p unary_nat_p) n then
                    distinct_egal_seq_over
                      (distinct_egal_seq_over distinct_egal_unary_nat distinct_egal_unary_nat_ne)
                      (distinct_egal_seq_over_ne distinct_egal_unary_nat_ne)
                      m n
                  else
                    raise (Failure "distinct failed")
                in
                let distinct_egal m n =
                  let d = distinct_egal_1 m n in
                  let endpos = Some(!lineno,!charno) in
                  let currprooffun = !prooffun in
                  prooffun := (fun dl -> currprooffun ((endpos,d)::dl));
                  pfstate := pfstr
                in
                match claimtm with
                | Ap(Ap(TpAp(TmH(h),Set),m),n) when h = "7966a66a9bb198103c2a540ccd5ebebdff33c10843cc10eebfc98715e142989c" && not (m = n) ->
                   distinct_egal m n
                | Imp(Ap(Ap(TpAp(TmH(h),Set),m),n),TmH(k)) when h = "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a" && k = !fal && not (m = n) ->
                   distinct_egal m n
                | Imp(Ap(Ap(TpAp(TmH(h),Set),m),n),All(Prop,DB(0))) when h = "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a" && not (m = n) ->
                   distinct_egal m n
                | _ -> raise (Failure "distinct tactic requires goal to be diseqn")           
              end
           | _ -> raise (Failure "distinct tactic requires a goal")
         end
       else
         raise (Failure "distinct tactic is only implemented for HOAS and Egal")
     end
  | SpecialTac(x,[]) when x = "reflexivity" ->
     begin
       match !pfstate with
       | PfStateGoal(startpos,claimtm,cxtm,cxpf)::pfstr ->
          begin
            match claimtm with
            | Ap(Ap(TpAp(TmH(h),a),m),n) when h = "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a" ->
               begin
                 match conv m n sigdelta !deltaset with
                 | Some(dl) ->
                    deltaset := dl;
                    let reflp = TLam(Ar(a,Ar(a,Prop)),PLam(Ap(Ap(DB(0),tmshift 0 1 m),tmshift 0 1 n),Hyp(0))) in
                    let endpos = Some(!lineno,!charno) in
		    let currprooffun = !prooffun in
                    prooffun := (fun dl -> currprooffun ((endpos,reflp)::dl));
                    pfstate := pfstr
                 | None -> raise (Failure("reflexivity failed"))
               end
            | _ -> raise (Failure("reflexivity tactic cannot be used when there is not an equation"))
          end
       | _ -> raise (Failure("reflexivity tactic cannot be used when there is no claim"))
     end
  | SpecialTac(x,[]) when x = "symmetry" ->
     begin
       match !pfstate with
       | PfStateGoal(startpos,claimtm,cxtm,cxpf)::pfstr ->
          begin
            match claimtm with
            | Ap(Ap(TpAp(TmH(h),a),m),n) when h = "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a" ->
               begin
		 let currprooffun = !prooffun in
                 prooffun := (fun dl -> match dl with (endpos,d)::dr -> currprooffun ((endpos,TLam(Ar(a,Ar(a,Prop)),PTmAp(pftmshift 0 1 d,Lam(a,Lam(a,Ap(Ap(DB(2),DB(0)),DB(1)))))))::dr) | [] -> raise (Failure "no pf of symmetric eqn"));
                 pfstate := PfStateGoal(startpos,Ap(Ap(TpAp(TmH(h),a),n),m),cxtm,cxpf)::pfstr;
               end
            | _ -> raise (Failure("symmetry tactic cannot be used when there is not an equation"))
          end
       | _ -> raise (Failure("symmetry tactic cannot be used when there is no claim"))
     end
  | SpecialTac(x,(a2::al)) when x = "transitivity" ->
     begin
       match !pfstate with
       | PfStateGoal(startpos,claimtm,cxtm,cxpf)::pfstr ->
          begin
            match claimtm with
            | Ap(Ap(TpAp(TmH(h),a),lhs),rhs) when h = "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a" ->
		let q = TpAp(TmH(h),a) in
		let rhs2 = tmshift 0 1 rhs in
		let prhs = Ap(DB(0),rhs2) in
		let rleib_imp_sleib =
		  TLam(a,TLam(a,PLam(All(Ar(a,Prop),Imp(Ap(DB(0),DB(1)),Ap(DB(0),DB(2)))),TLam(Ar(a,Ar(a,Prop)),PPfAp(PTmAp(Hyp(0),Lam(a,Imp(Ap(Ap(DB(1),DB(0)),DB(2)),Ap(Ap(DB(1),DB(2)),DB(0))))),PLam(Ap(Ap(DB(0),DB(1)),DB(1)),Hyp(0)))))))
		in
		let pfun = !prooffun in
		let rec transitivity_tac lhs al =
		  match al with
		  | [] ->
		      let pfst2 = PfStateGoal(startpos,Ap(Ap(q,lhs),rhs),cxtm,cxpf)::pfstr in
		      let pfun2 dl =
			match dl with
			| (endpos,d1)::dr -> (PPfAp(PTmAp(pfshift 0 1 (pftmshift 0 1 d1),Lam(a,DB(1))),Hyp(0)),dr)
			| _ -> raise (Failure "missing proof of eqn in transitivity")
		      in
		      (pfun2,pfst2)
		  | a2::ar ->
		      let a2 = ltree_to_atree a2 in
		      let m2 = check_tm a2 a !polytm sigtmof !sigtm !ctxtp cxtm in
		      let (pfun2,pfst2) = transitivity_tac m2 ar in
		      let pfun3 dl =
			match dl with
			  (endpos1,d1)::dr ->
			   let (d2,dr2) = pfun2 dr in
			   (PPfAp(PTmAp(pfshift 0 1 (pftmshift 0 1 d1),Lam(a,DB(1))),d2),dr2)
			| _ -> raise (Failure "mssing proof of eqn in transitivity")
		      in
		      let pfst3 = PfStateGoal(startpos,Ap(Ap(q,lhs),m2),cxtm,cxpf)::pfst2 in
		      (pfun3,pfst3)
		in
		let (pfun2,pfst2) = transitivity_tac lhs (a2::al) in
                let endpos = Some(!lineno,!charno) in
		let pfun3 dl =
		  let (d,dr) = pfun2 dl in
		  pfun ((endpos,PPfAp(PTmAp(PTmAp(rleib_imp_sleib,lhs),rhs),TLam(Ar(a,Prop),PLam(prhs,d))))::dr)
		in
		prooffun := pfun3;
		pfstate := pfst2
	    | _ -> raise (Failure("transitivity tactic cannot be used when there is not an equation"))
	  end
       | _ -> raise (Failure("transitivity tactic cannot be used when there is no claim"))
     end
  | SpecialTac(x,[]) when x = "f_equal" ->
     begin
       match !pfstate with
       | PfStateGoal(startpos,claimtm,cxtm,cxpf)::pfstr ->
          begin
            match claimtm with
            | Ap(Ap(TpAp(TmH(h),a),lhs),rhs) when h = "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a" ->
               let q = TpAp(TmH(h),a) in
	       let rhs2 = tmshift 0 1 rhs in
	       let prhs = Ap(DB(0),rhs2) in
	       let rleib_imp_sleib =
		 TLam(a,TLam(a,PLam(All(Ar(a,Prop),Imp(Ap(DB(0),DB(1)),Ap(DB(0),DB(2)))),TLam(Ar(a,Ar(a,Prop)),PPfAp(PTmAp(Hyp(0),Lam(a,Imp(Ap(Ap(DB(1),DB(0)),DB(2)),Ap(Ap(DB(1),DB(2)),DB(0))))),PLam(Ap(Ap(DB(0),DB(1)),DB(1)),Hyp(0)))))))
	       in
	       let pfun = !prooffun in
               let rec f_equal_intermediates lhs rhs f r =
                 if lhs = rhs then
                   r
                 else
                   match (lhs,rhs) with
                   | (Ap(lf,la),Ap(rf,ra)) ->
                      let la4 = tmshift 0 4 la in
                      if la = ra then
                        f_equal_intermediates lf rf (fun m -> f (Ap(m,la4))) r
                      else
                        let rf4 = tmshift 0 4 rf in
                        f_equal_intermediates lf rf (fun m -> f (Ap(m,la4))) ((la,ra,(fun m -> f (Ap(rf4,m))))::r)
                   | _ -> raise (Failure "f_equal does not apply here")
               in
               let mnl = f_equal_intermediates lhs rhs (fun m -> m) [] in
               let lift_eqn_pf d f =
                 TLam(Ar(a,Ar(a,Prop)),PTmAp(pftmshift 0 1 d,Lam(a,Lam(a,Ap(Ap(DB(2),f (DB(1))),f (DB(0)))))))
               in
	       let rec f_equal_tac lhs mnl =
		 match mnl with
		 | [] ->
		    ((fun dl -> (Hyp(0),dl)),pfstr)
		 | (m,n,f)::mnr ->
		    let (pfun2,pfst2) = f_equal_tac (tmshift 0 (-4) (f (tmshift 0 4 n))) mnr in
		    let pfun3 dl =
		      match dl with
		      | (endpos,d1)::dr ->
			 let (d2,dr2) = pfun2 dr in
                         let d1a = pfshift 0 1 (pftmshift 0 1 d1) in
                         let d1f = lift_eqn_pf d1a f in
			 (PPfAp(PTmAp(d1f,Lam(a,DB(1))),d2),dr2)
		      | _ -> raise (Failure "mssing proof of eqn in f_equal")
		    in
		    let pfst3 = PfStateGoal(startpos,Ap(Ap(q,m),n),cxtm,cxpf)::pfst2 in
		    (pfun3,pfst3)
	       in
	       let (pfun2,pfst2) = f_equal_tac lhs mnl in
               let endpos = Some(!lineno,!charno) in
	       let pfun3 dl =
		 let (d,dr) = pfun2 dl in
		 pfun ((endpos,PPfAp(PTmAp(PTmAp(rleib_imp_sleib,lhs),rhs),TLam(Ar(a,Prop),PLam(prhs,d))))::dr)
	       in
	       prooffun := pfun3;
	       pfstate := pfst2
	    | _ -> raise (Failure("f_equal tactic cannot be used when there is not an equation"))
	  end
       | _ -> raise (Failure("f_equal tactic cannot be used when there is no claim"))
     end
  | _ ->
      raise (Failure("Unknown proof tactic")));
  !megawiki_target

let rec evaluate_pftac_2 () =
  match !pfstate with
  | PfStateSep(j,false)::pfstr ->
      begin
        List.iter
          (fun hc -> output_pftacitem_html (html_context ()) hc (PfStruct(j)) sigtmh sigknh 3)
          (pftac_html_channels ())
      end;
      begin
	match !latex with
	| Some hc -> output_pftacitem_latex hc (PfStruct(j)) sigtmh sigknh 3
	| None -> ()
      end;
      pfstate := pos_fst_pfst pfstr;
      evaluate_pftac_2 ()
  | _ -> ()

let evaluate_pftac pitem thmname i gpgtm gphv pfggphv =
  if !verbosity > 19 then (Printf.printf "pre1 pfstruct %d\nLength of pfstate stack: %d\n" i (List.length !pfstate); print_pfstate (); flush stdout);
  begin
    match !sexprallsubgoals with
    | None -> ()
    | Some(seaspre,seasincl,_) ->
       match !pfstate with
       | PfStateGoal(startpos,atm,ctxtm,ctxpf)::_ ->
          let f = open_out (Printf.sprintf "%s_%d_%d.lisp" seaspre !lineno !charno) in
          if not (seasincl = "") then Printf.fprintf f "(INCLUDE \"%s\")\n" seasincl;
          List.iter (fun (y,q) -> Printf.fprintf f "(HYP \"%s\" %s)\n" y (tm_to_sexpr q)) ctxpf;
          List.iter
            (fun (x,(a,od)) ->
              match od with
              | None -> Printf.fprintf f "(VAR \"%s\" %s)\n" x (tp_to_sexpr a)
              | Some(d) -> Printf.fprintf f "(LET \"%s\" %s %s)\n" x (tp_to_sexpr a) (tm_to_sexpr d))
            ctxtm;
          Printf.fprintf f "(GOAL %s)\n" (tm_to_sexpr atm);
          close_out f
       | _ -> ()
  end;
  let megawiki_target = evaluate_pftac_1 pitem thmname i gpgtm gphv pfggphv in
  begin
(*    if pitem = Qed || pitem = Admitted then
      begin
        match !inchan with
        | Some(c) -> buffer_to_line_char c pftext inchanline inchanchar !lineno !charno
        | None -> ()
      end; *)
    List.iter
      (fun hc -> output_pftacitem_html (html_context ()) hc pitem sigtmh sigknh !laststructaction)
      (pftac_html_channels ())
  end;
  begin
    match !latex with
    | Some hc ->
(*	if pitem = Qed || pitem = Admitted then
	  begin
	    match !inchan with
	    | Some(c) -> buffer_to_line_char c pftext inchanline inchanchar !lineno !charno
	    | None -> ()
	  end; *)
	output_pftacitem_latex hc pitem sigtmh sigknh !laststructaction
    | None -> ()
  end;
  if !verbosity > 19 then (Printf.printf "pre2 pfstruct %d\nLength of pfstate stack: %d\n" i (List.length !pfstate); print_pfstate (); flush stdout);
  evaluate_pftac_2 ();
  begin
    match megawiki_target with
    | Some(b) -> finalize_megawiki_theorem b
    | None -> ()
  end

let init_env () =
  ctxtp := [];
  ctxtm := [];
  ctxpf := [];
  tparclos := (fun a -> a);
  tmallclos := (fun m -> m);
  tmlamclos := (fun m -> m);
  pflamclos := (fun d -> d);
  aptmloc := (fun m cxtp cxtm -> m);
  appfloc := (fun d cxtp cxtm cxpf -> d);
  secstack := [];
  popfn := (fun () -> ())
	
(*** Function for checking if a file solves a problem file in addition to checking the solution file for correctness. ***)
let mgchecksolves probc solnc =
  init_env ();
  let ptl = ref (TokStrRest(Lexer.token,Lexing.from_channel probc)) in
  let stl = ref (TokStrRest(Lexer.token,Lexing.from_channel solnc)) in
  let currentthm = ref "" in
  let inadmitted = ref false in
  let linenop = ref 1 in
  let charnop = ref 0 in
  let linenos = ref 1 in
  let charnos = ref 0 in
  try
    while true do
      match !proving with
      | None ->
	  begin
	    lineno := !linenop;
	    charno := !charnop;
	    let (pditem,ptr) =
	      try
		parse_docitem !ptl
	      with Lexer.Eof ->
		let _ = parse_docitem !stl in
		raise (Failure("Problem file ended prematurely"))
	    in
	    linenop := !lineno;
	    charnop := !charno;
	    lineno := !linenos;
	    charno := !charnos;
	    authors := [];
	    title := None;
	    let (sditem,str) =
	      try
		parse_docitem !stl
	      with Lexer.Eof ->
		raise (Failure("Solution file ended prematurely"))
	    in
	    linenos := !lineno;
	    charnos := !charno;
	    ptl := ptr;
	    stl := str;
	    evaluate_docitem sditem;
	    if pditem <> sditem then
	      raise (Failure("Solution document differs from problem document at line " ^ (string_of_int !linenop) ^ " and char " ^ (string_of_int !charnop) ^ " / line " ^ (string_of_int !linenos) ^ " and char " ^ (string_of_int !charnos)));
	    match sditem with
	    | ThmDecl(_,x,_) -> currentthm := x
	    | _ -> ()
	  end
      | Some (thmname,i,gpgtm,gphv,pfggphv) -> (*** reading a proof in the solution file ***)
	  begin
	    if !inadmitted then
	      begin
		lineno := !linenos;
		charno := !charnos;
		let (spftac,str) =
		  try
		    parse_pftacitem !stl
		  with Lexer.Eof ->
		    raise (Failure("Solution file ended prematurely"))
		in
		stl := str;
		linenos := !lineno;
		charnos := !charno;
		evaluate_pftac spftac thmname i gpgtm gphv pfggphv;
		if spftac = Qed then
		  inadmitted := false
		else if spftac = Admit || spftac = Admitted then
		  raise (Failure("Incomplete proof in solution file"))
	      end
	    else
	      begin
		lineno := !linenop;
		charno := !charnop;
		let (ppftac,ptr) =
		  try
		    parse_pftacitem !ptl
		  with Lexer.Eof ->
		    let _ = parse_pftacitem !stl in
		    raise (Failure("Problem file ended prematurely"))
		in
		linenop := !lineno;
		charnop := !charno;
		lineno := !linenos;
		charno := !charnos;
		let (spftac,str) =
		  try
		    parse_pftacitem !stl
		  with Lexer.Eof ->
		    raise (Failure("Solution file ended prematurely"))
		in
		linenos := !lineno;
		charnos := !charno;
		ptl := ptr;
		stl := str;
		evaluate_pftac spftac thmname i gpgtm gphv pfggphv;
		if spftac = Admit || spftac = Admitted then
		  raise (Failure("Incomplete proof in solution file"));
		if ppftac <> spftac then
		  begin
		    if ppftac = Admitted then
		      begin
			exercises := !currentthm :: !exercises;
			if spftac <> Qed then
			  inadmitted := true
		      end
		    else
		      raise (Failure("Solution document differs from problem document in proof at line " ^ (string_of_int !linenop) ^ " and char " ^ (string_of_int !charnop) ^ " / line " ^ (string_of_int !linenos) ^ " and char " ^ (string_of_int !charnos)))
		  end
	      end
	  end
    done
  with
  | Lexer.Eof ->
      ()
  | ParsingError(x,l1,c1,l2,c2) ->
      if !webout then
	begin
          Printf.printf "AS%d:%d:%d:%d\n"  l1 c1 l2 c2;
	  Printf.printf "<div class='documentfail'>Syntax error between line %d char %d and line %d char %d:<br/>%s</div>" l1 c1 l2 c2 x;
	  exit 1
	end
      else
	begin
	  Printf.printf "Syntax error between line %d char %d and line %d char %d:\n%s\n" l1 c1 l2 c2 x;
	  exit 1
	end
  | Failure(x) ->
      if !webout then
	begin
          Printf.printf "AF%d:%d\n"  !lineno !charno;
	  Printf.printf "<div class='documentfail'>Failure at line %d char %d: %s</div>" !lineno !charno x; flush stdout;
	  exit 1
	end
      else
	begin
	  Printf.printf "Failure at line %d char %d: %s\n" !lineno !charno x; flush stdout;
	  exit 1
	end

let mgcheck_ajax c =
  let tl = ref (TokStrRest(Lexer.token,Lexing.from_channel c)) in
  lineno := 1;
  charno := 0;
  verbosity := 1;
  try
    while true do
      if !verbosity > 59 then (Printf.printf "Main Loop Start\n"; flush stdout);
      match !proving with
      | None ->
	  ignore (parse_docitem !tl); (*** hopefully this raises End_of_file ***)
	  raise (Failure("The content must not continue beyond the proof."))
      | Some (thmname,i,gpgtm,gphv,pfggphv) -> (*** reading a proof ***)
	  let (pitem,tr) = parse_pftacitem !tl in
	  tl := tr;
	  evaluate_pftac pitem thmname i gpgtm gphv pfggphv
    done
  with
  | Lexer.Eof ->
      begin
	match !proving with
	| None -> () (* OK *)
	| Some(thmname,i,gpgtm,gphv,pfggphv) -> (* pretend there is a Qed at the end *)
	    try
	      evaluate_pftac Qed thmname i gpgtm gphv pfggphv
	    with
	    | Failure(x) ->
		Printf.printf "F %d %d$%s" !lineno !charno x
	    | ParsingError(x,l1,c1,l2,c2) ->
		Printf.printf "E %d %d %d %d$%s" l1 c1 l2 c2 x
      end
  | Failure(x) ->
      Printf.printf "F %d %d$%s" !lineno !charno x
  | ParsingError(x,l1,c1,l2,c2) ->
      Printf.printf "E %d %d %d %d$%s" l1 c1 l2 c2 x

(*** Main function for checking a file ***)
let mgcheck c =
  init_env ();
  let tl = ref (TokStrRest(Lexer.token,Lexing.from_channel c)) in
  lineno := 1;
  charno := 0;
  try
    while true do
      if !verbosity > 59 then (Printf.printf "Main Loop Start\n"; flush stdout);
      match !proving with
      | None ->
          Syntax.set_html_item_start_line !lineno;
	  let (ditem,tr) = parse_docitem !tl in
	  tl := tr;
	  evaluate_docitem ditem
      | Some (thmname,i,gpgtm,gphv,pfggphv) -> (*** reading a proof ***)
          Syntax.set_html_item_start_line !lineno;
	  let (pitem,tr) = parse_pftacitem !tl in
	  tl := tr;
          if pitem = Qed then
            begin
              match !removepfs with
              | None -> ()
              | Some(_) ->
                 let (l1,c1) = !thmstart in
                 let (l2,c2) = !thmend in
                 pfposinfo := (l1,c1,l2,c2+1,!lineno,!charno+1)::!pfposinfo
            end;
	  evaluate_pftac pitem thmname i gpgtm gphv pfggphv
    done
  with
  | Lexer.Eof ->
    begin
      if !ajax then (*** we should be expecting a proof which can be read from the given proof file ***)
	if not !includingsigfile then
	  begin
	    ajaxactive := true;
	    let ca = open_in !ajaxpffile in
	    mgcheck_ajax ca
	  end
      else
	if (!verbosity > 9) then (Printf.printf "done.\n"; flush stdout)
    end
  | ParsingError(x,l1,c1,l2,c2) ->
      finalize_megawiki_theorem false;
      if !webout then
	begin
          Printf.printf "AS%d:%d:%d:%d\n"  l1 c1 l2 c2;
	  Printf.printf "<div class='documentfail'>Syntax error between line %d char %d and line %d char %d:<br/>%s</div>" l1 c1 l2 c2 x;
	  exit 1
	end
      else if !ajax then
	begin
	  Printf.printf "f\n"; (*** this indicates a fundamental problem, not a problem with the ajax input ***)
	  exit 1
	end
      else
	begin
	  Printf.printf "Syntax error between line %d char %d and line %d char %d:\n%s\n" l1 c1 l2 c2 x;
	  exit 1
	end
  | Failure(x) ->
      finalize_megawiki_theorem false;
      if !webout then
	begin
          Printf.printf "AF%d:%d\n"  !lineno !charno;
	  Printf.printf "<div class='documentfail'>Failure at line %d char %d: %s</div>" !lineno !charno x; flush stdout;
	  exit 1
	end
      else if !ajax then
	begin
	  Printf.printf "f\n"; (*** this indicates a fundamental problem, not a problem with the ajax input ***)
	  exit 1
	end
      else
	begin
	  Printf.printf "Failure at line %d char %d: %s\n" !lineno !charno x; flush stdout;
	  exit 1
	end

let rec sql_docpresentation docsha c i =
  try
    let l = input_line c in
    sql_docpresentation_0 docsha c l i
  with End_of_file -> ()
and sql_docpresentation_0 docsha c l i =
  if String.length l > 0 && l.[0] = '$' then
    begin
      if String.length l > 1 then
	if l.[1] = 'x' then
	  begin
	    Printf.printf "INSERT INTO `docpresentationpart` (`docsha`,`docpresentationpartno`,`docpresentationpartexercise`) VALUES ('%s',%d,'%s');\n" docsha i (String.sub l 2 (String.length l - 2));
	    if not !presentationonly then (Printf.printf "INSERT INTO `docexercise` (`docsha`,`termid`) VALUES ('%s','%s');\n" docsha (String.sub l 2 (String.length l - 2)));
	  end
	else
	  Printf.printf "INSERT INTO `docpresentationpart` (`docsha`,`docpresentationpartno`,`docpresentationparttreasure`) VALUES ('%s',%d,'%s');\n" docsha i (String.sub l 1 (String.length l - 1));
      sql_docpresentation docsha c (i+10)
    end
  else
    begin
      Printf.printf "INSERT INTO `docpresentationpart` (`docsha`,`docpresentationpartno`,`docpresentationparttext`) VALUES ('%s',%d,'" docsha i;
      try
	sql_docpresentation_1 docsha c l (i+10)
      with End_of_file ->
	Printf.printf "');\n";
    end
and sql_docpresentation_1 docsha c l i =
  if String.length l > 0 && l.[0] = '$' then
    begin
      Printf.printf "');\n";
      sql_docpresentation_0 docsha c l i
    end
  else
    begin
      for j = 0 to String.length l - 1 do
	let z = l.[j] in
	if z = '\'' then
	  (output_char stdout z; output_char stdout z)
	else if z = '\\' then
	  (output_char stdout '\\'; output_char stdout '\\')
	else
	  output_char stdout z
      done;
      output_char stdout '\n';
      let l = input_line c in
      sql_docpresentation_1 docsha c l i
    end

let preset_ptm_lam_id (m:ptm) : string =
  let h = ptm_lam_id m sigtmof sigdelta in
(*  Hashtbl.add sigdelta h m; *)
  h

let preset_ptm_all_id (m:ptm) : string =
  let h = ptm_all_id m sigtmof sigdelta in
  Hashtbl.add sigdelta h m;
  h

let preset_hf_index () =
  Hashtbl.add indextms "174b78e53fc239e8c2aab4ab5a996a27e3e5741e88070dad186e05fb13f275e5" (Ar(Ar(Set,Prop),Set));
  Hashtbl.add indextms "431fc21268bb816a6863cbbc67e0dc2f464b853f3de702356377e69622c53662" (Ar(Ar(Prop,Prop),Prop));
  Hashtbl.add indextms "767ba9d76b6e9cc3ee2d3ac565970dc8696692d69668566e6bdcd383d2e1f319" (Ar(Ar(Ar(Set,Prop),Prop),Ar(Set,Prop)));
  Hashtbl.add indextms "ed85eff40ecc0b8787005cbd9d54b5db6c35246db186aed964f3b6f89cd015f8" (Ar(Ar(Ar(Set,Set),Prop),Ar(Set,Set)));
  Hashtbl.add indextms "7e81600038c894130f4e1811dfec03dc034a88423cec5eb9361221c65e3c34c0" (Ar(Ar(Ar(Set,Ar(Set,Prop)),Prop),Ar(Set,Ar(Set,Prop))));
  Hashtbl.add indexknowns "6b41a6c708fbf6811d82e5779931513ec2038aa89c75ec1a738314de9939f8be" ();
  Hashtbl.add indexknowns "45d19dce8d55f80220047e45e62aa10f87457fe7f5f0c0a60961bb71e690d938" ();
  Hashtbl.add indexknowns "c320b7c9632bf47e1605efb7cbc88128e349c429d23c94453b8ba70ed2edbfcd" ();
  Hashtbl.add indexknowns "005fb5ab278291afee47d8d4167d5b5579bcd703b8238809af60a9972e1fb94b" ();
  Hashtbl.add indextms "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87" Prop;
  Hashtbl.add indextms "5867641425602c707eaecd5be95229f6fd709c9b58d50af108dfe27cb49ac069" Prop;
  Hashtbl.add indextms "058f630dd89cad5a22daa56e097e3bdf85ce16ebd3dbf7994e404e2a98800f7f" (Ar(Prop,Prop));
  Hashtbl.add indextms "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738" (Ar(Prop,Ar(Prop,Prop)));
  Hashtbl.add indextms "cfe97741543f37f0262568fe55abbab5772999079ff734a49f37ed123e4363d7" (Ar(Prop,Ar(Prop,Prop)));
  Hashtbl.add indextms "9c60bab687728bc4482e12da2b08b8dbc10f5d71f5cab91acec3c00a79b335a3" (Ar(Prop,Ar(Prop,Prop)));
  Hashtbl.add indextms "8a8e36b858cd07fc5e5f164d8075dc68a88221ed1e4c9f28dac4a6fdb2172e87" (Ar(Set,Ar(Set,Prop)));
  Hashtbl.add indextms "e7493d5f5a73b6cb40310f6fcb87d02b2965921a25ab96d312adf7eb8157e4b3" (Ar(Set,Prop));
  Hashtbl.add indextms "384d9f66d8806a02ebe28da535de6ad3715d7edbe784c055e3c70df3ad888708" (Ar(Set,Prop));
  Hashtbl.add indextms "bb3da8f6f3861e950e002517b27fe9407103f6d9bfacf8e3d7600f2396cc1059" (Ar(Set,Prop));
  Hashtbl.add indextms "dcde207b36b2fb5f060060582bf079763feaf495d2165b7092e20cd10daf7a99" (Ar(Set,Prop));
  Hashtbl.add indextms "7c09f0cab3d30d5ff3c2ec8c2cff61e158c82ce67d886c8b6a8763990b8a0515" (Ar(Set,Prop));
  Hashtbl.add indextms "c59022da27533d1a9c86144e1d2afd1512d11dfffd04a979887af2e1ee5f6e59" (Ar(Set,Prop));
  Hashtbl.add indextms "c7df083c7cf25a97335c4c9d8dc333551ed272dcab0c9c75bdb57679962006f5" (Ar(Set,Prop));
  Hashtbl.add indextms "06a9db6a163cde1bda5ecbfee9ca49f646ff205577687d3f603d53e0c58aefb5" (Ar(Set,Prop));
  Hashtbl.add indextms "3c3963fd1d3e8a801895ec2bc1bdd6c0d1f64c3f6bee436c56b146112890c357" (Ar(Set,Prop));
  Hashtbl.add indextms "f73cdba5a4e557a8f57fbba8517c0f7593a0b36795e8f51b63ba62b37035c3d0" (Ar(Set,Prop));
  Hashtbl.add indextms "67f7963d11a96caa6d857a801e3a87a49e63de70c1a4d3f1be82810c5ca7eca7" (Ar(Ar(Set,Prop),Prop));
  Hashtbl.add indextms "161886ed663bc514c81ed7fe836cca71861bfe4dfe4e3ede7ef3a48dbc07d247" (Ar(Ar(Set,Ar(Set,Prop)),Prop));
  Hashtbl.add indextms "3e5bc5e85f7552688ed0ced52c5cb8a931e179c99646161ada3249216c657566" (Ar(Ar(Set,Ar(Set,Prop)),Prop));
  Hashtbl.add indextms "591ebe2d703dc011fd95f000dd1ad77b0dca9230146d2f3ea2cb96d6d1fba074" (Ar(Ar(Set,Ar(Set,Prop)),Prop));
  Hashtbl.add indextms "e66ec047c09acdc1e824084ea640c5c9a30ab00242f4c1f80b83c667c930e87e" (Ar(Ar(Set,Ar(Set,Prop)),Prop));
  Hashtbl.add indextms "8f39e0d849db8334a6b514454a2aef6235afa9fc2b6ae44712b4bfcd7ac389cc" (Ar(Ar(Set,Ar(Set,Prop)),Prop));
  Hashtbl.add indextms "0609dddba15230f51d1686b31544ff39d4854c4d7f71062511cc07689729b68d" (Ar(Ar(Set,Ar(Set,Prop)),Prop));
  Hashtbl.add indextms "4a0f686cd7e2f152f8da5616b417a9f7c3b6867397c9abde39031fa0217d2692" (Ar(Ar(Set,Ar(Set,Prop)),Prop));
  Hashtbl.add indextms "4267a4cfb6e147a3c1aa1c9539bd651e22817ab41fd8ab5d535fbf437db49145" (Ar(Ar(Set,Ar(Set,Prop)),Prop));
  Hashtbl.add indextms "f3818d36710e8c0117c589ed2d631e086f82fbcbf323e45d2b12a4eaddd3dd85" (Ar(Ar(Set,Ar(Set,Prop)),Prop));
  Hashtbl.add indextms "5057825a2357ee2306c9491a856bb7fc4f44cf9790262abb72d8cecde03e3df4" (Ar(Ar(Set,Ar(Set,Prop)),Prop));
  Hashtbl.add indextms "f3976896fb7038c2dd6ace65ec3cce7244df6bf443bacb131ad83c3b4d8f71fb" (Ar(Ar(Set,Ar(Set,Prop)),Prop));
  Hashtbl.add indextms "35f61b92f0d8ab66d988b2e71c90018e65fc9425895b3bae5d40ddd5e59bebc1" (Ar(Ar(Set,Ar(Set,Prop)),Prop));
  Hashtbl.add indextms "b90ec130fa720a21f6a1c02e8b258f65af5e099282fe8b3927313db7f25335ed" (Ar(Ar(Set,Ar(Set,Prop)),Prop));
  Hashtbl.add indextms "8c8f550868df4fdc93407b979afa60092db4b1bb96087bc3c2f17fadf3f35cbf" (Ar(Prop,Ar(Set,Ar(Set,Set))));
  Hashtbl.add indextms "3578b0d6a7b318714bc5ea889c6a38cf27f08eaccfab7edbde3cb7a350cf2d9b" (Ar(Prop,Ar(Prop,Prop)));
  Hashtbl.add indextms "d2a0e4530f6e4a8ef3d5fadfbb12229fa580c2add302f925c85ede027bb4b175" (Ar(Prop,Ar(Prop,Ar(Prop,Prop))));
  Hashtbl.add indextms "2f8b7f287504f141b0f821928ac62823a377717763a224067702eee02fc1f359" (Ar(Set,Ar(Set,Prop)));
  Hashtbl.add indextms "f275e97bd8920540d5c9b32de07f69f373d6f93ba6892c9e346254a85620fa17" (Ar(Set,Ar(Set,Prop)));
  Hashtbl.add indextms "80aea0a41bb8a47c7340fe8af33487887119c29240a470e920d3f6642b91990d" (Ar(Set,Ar(Set,Set)));
  Hashtbl.add indextms "158bae29452f8cbf276df6f8db2be0a5d20290e15eca88ffe1e7b41d211d41d7" (Ar(Set,Set));
  Hashtbl.add indextms "0a445311c45f0eb3ba2217c35ecb47f122b2301b2b80124922fbf03a5c4d223e" (Ar(Set,Ar(Set,Set)));
  Hashtbl.add indextms "153bff87325a9c7569e721334015eeaf79acf75a785b960eb1b46ee9a5f023f8" (Ar(Set,Ar(Set,Set)));
  Hashtbl.add indextms "d772b0f5d472e1ef525c5f8bd11cf6a4faed2e76d4eacfa455f4d65cc24ec792" (Ar(Set,Ar(Ar(Set,Set),Set)));
  Hashtbl.add indextms "f7e63d81e8f98ac9bc7864e0b01f93952ef3b0cbf9777abab27bcbd743b6b079" (Ar(Set,Ar(Ar(Set,Prop),Set)));
  Hashtbl.add indextms "f627d20f1b21063483a5b96e4e2704bac09415a75fed6806a2587ce257f1f2fd" (Ar(Set,Ar(Ar(Set,Prop),Ar(Ar(Set,Set),Set))));
  Hashtbl.add indextms "8cf6b1f490ef8eb37db39c526ab9d7c756e98b0eb12143156198f1956deb5036" (Ar(Set,Ar(Set,Set)));
  Hashtbl.add indextms "cc569397a7e47880ecd75c888fb7c5512aee4bcb1e7f6bd2c5f80cccd368c060" (Ar(Set,Ar(Set,Set)));
  Hashtbl.add indextms "2ce94583b11dd10923fde2a0e16d5b0b24ef079ca98253fdbce2d78acdd63e6e" (Ar(Set,Ar(Set,Ar(Ar(Set,Set),Prop))));
  Hashtbl.add indextms "9ef333480205115fcb54535d5d8de44756eee80867000051222280db0c9646e4" (Ar(Set,Ar(Set,Ar(Ar(Set,Set),Prop))));
  Hashtbl.add indextms "6f4d9bb1b2eaccdca0b575e1c5e5a35eca5ce1511aa156bebf7a824f08d1d69d" (Ar(Set,Ar(Set,Prop)));
  Hashtbl.add indextms "7b717effbbdb47e1c3b6b0b11d8afebd925fdf397e15abe9de1d5ea74224420c" (Ar(Set,Ar(Set,Prop)));
  Hashtbl.add indextms "ee2e1f36ccc047af9077fcfe6de79d6c9574876b02cae0b4b919e11461760f0d" (Ar(Ar(Set,Ar(Ar(Set,Set),Set)),Ar(Set,Ar(Set,Prop))));
  Hashtbl.add indextms "f97da687c51f5a332ff57562bd465232bc70c9165b0afe0a54e6440fc4962a9f" (Ar(Ar(Set,Ar(Ar(Set,Set),Set)),Ar(Set,Set)));
  Hashtbl.add indextms "9db634daee7fc36315ddda5f5f694934869921e9c5f55e8b25c91c0a07c5cbec" (Ar(Set,Set));
  Hashtbl.add indextms "25c483dc8509e17d4b6cf67c5b94c2b3f3902a45c3c34582da3e29ab1dc633ab" (Ar(Set,Prop));
  Hashtbl.add indextms "9161ec45669e68b6f032fc9d4d59e7cf0b3f5f860baeb243e29e767a69d600b1" (Ar(Set,Ar(Ar(Set,Ar(Set,Set)),Ar(Set,Set))));
  Hashtbl.add indextms "e4d45122168d3fb3f5723ffffe4d368988a1be62792f272e949c6728cec97865" (Ar(Set,Ar(Set,Set)));
  Hashtbl.add indextms "7a45b2539da964752f7e9409114da7fc18caef138c5d0699ec226407ece64991" (Ar(Set,Ar(Set,Set)));
  Hashtbl.add indextms "dab6e51db9653e58783a3fde73d4f2dc2637891208c92c998709e8795ba4326f" (Ar(Set,Prop));
  Hashtbl.add indextms "dc688de6dbfa5c75bd45f1eb198583d07be144f0cdabb44def09da1c0976495b" (Ar(Set,Set));
  Hashtbl.add indextms "fb5286197ee583bb87a6f052d00fee2b461d328cc4202e5fb40ec0a927da5d7e" (Ar(Set,Set));
  Hashtbl.add indextms "3585d194ae078f7450f400b4043a7820330f482343edc5773d1d72492da8d168" (Ar(Set,Set));
  Hashtbl.add indextms "d3f7df13cbeb228811efe8a7c7fce2918025a8321cdfe4521523dc066cca9376" (Ar(Set,Set));
  Hashtbl.add indextms "f0267e2cbae501ea3433aecadbe197ba8f39c96e80326cc5981a1630fda29909" (Ar(Set,Ar(Set,Ar(Ar(Set,Set),Ar(Ar(Set,Set),Ar(Set,Set))))));
  Hashtbl.add indextms "b260cb5327df5c1f762d4d3068ddb3c7cc96a9cccf7c89cee6abe113920d16f1" (Ar(Set,Ar(Set,Set)));
  Hashtbl.add indextms "877ee30615a1a7b24a60726a1cf1bff24d7049b80efb464ad22a6a9c9c4f6738" (Ar(Set,Set));
  Hashtbl.add indextms "dc75c4d622b258b96498f307f3988491e6ba09fbf1db56d36317e5c18aa5cac6" (Ar(Set,Set));
  Hashtbl.add indextms "d744bcd791713cf88021ce34168c3e2d109a8a6c45637d74541d94007e3139ca" (Ar(Set,Ar(Set,Set)));
  Hashtbl.add indextms "93592da87a6f2da9f7eb0fbd449e0dc4730682572e0685b6a799ae16c236dcae" (Ar(Set,Ar(Ar(Set,Set),Set)));
  Hashtbl.add indextms "ecef5cea93b11859a42b1ea5e8a89184202761217017f3a5cdce1b91d10b34a7" (Ar(Set,Ar(Set,Set)));
  Hashtbl.add indextms "58c1782da006f2fb2849c53d5d8425049fad551eb4f8025055d260f0c9e1fe40" (Ar(Set,Ar(Set,Set)));
  Hashtbl.add indextms "dac986a57e8eb6cc7f35dc0ecc031b9ba0403416fabe2dbe130edd287a499231" (Ar(Set,Prop));
  Hashtbl.add indextms "091d1f35158d5ca6063f3c5949e5cbe3d3a06904220214c5781c49406695af84" (Ar(Set,Ar(Set,Prop)));
  Hashtbl.add indextms "8ab5fa18b3cb4b4b313a431cc37bdd987f036cc47f175379215f69af5977eb3b" (Ar(Set,Ar(Ar(Set,Set),Set)));
  Hashtbl.add indextms "fcd77a77362d494f90954f299ee3eb7d4273ae93d2d776186c885fc95baa40dc" (Ar(Set,Ar(Set,Set)));
  Hashtbl.add indextms "0775ebd23cf37a46c4b7bc450bd56bce8fc0e7a179485eb4384564c09a44b00f" (Ar(Set,Ar(Ar(Set,Set),Ar(Ar(Set,Ar(Set,Prop)),Set))));
  Hashtbl.add indextms "04c0176f465abbde82b7c5c716ac86c00f1b147c306ffc6b691b3a5e8503e295" (Ar(Set,Prop));
  Hashtbl.add indextms "dc7715ab5114510bba61a47bb1b563d5ab4bbc08004208d43961cf61a850b8b5" (Ar(Set,Ar(Ar(Set,Set),Ar(Ar(Set,Ar(Set,Set)),Set))));
  Hashtbl.add indextms "ac96e86902ef72d5c44622f4a1ba3aaf673377d32cc26993c04167cc9f22067f" (Ar(Set,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Prop))));
  Hashtbl.add indextms "f36b5131fd375930d531d698d26ac2fc4552d148f386caa7d27dbce902085320" (Ar(Set,Ar(Ar(Set,Prop),Ar(Ar(Set,Prop),Prop))));
  Hashtbl.add indextms "2336eb45d48549dd8a6a128edc17a8761fd9043c180691483bcf16e1acc9f00a" (Ar(Set,Ar(Ar(Set,Prop),Ar(Set,Ar(Ar(Set,Prop),Prop)))));
  Hashtbl.add indextms "f91c31af54bc4bb4f184b6de34d1e557a26e2d1c9f3c78c2b12be5ff6d66df66" (Ar(Set,Ar(Ar(Set,Prop),Ar(Set,Ar(Ar(Set,Prop),Prop)))));
  Hashtbl.add indextms "e59af381b17c6d7665103fc55f99405c91c5565fece1832a6697045a1714a27a" (Ar(Ar(Set,Ar(Ar(Set,Prop),Prop)),Ar(Set,Ar(Ar(Set,Prop),Prop))));
  Hashtbl.add indextms "eb5699f1770673cc0c3bfaa04e50f2b8554934a9cbd6ee4e9510f57bd9e88b67" (Ar(Ar(Set,Ar(Ar(Set,Prop),Prop)),Ar(Set,Ar(Ar(Set,Prop),Prop))));
  Hashtbl.add indextms "1e55e667ef0bb79beeaf1a09548d003a4ce4f951cd8eb679eb1fed9bde85b91c" (Ar(Set,Set));
  Hashtbl.add indextms "3bbf071b189275f9b1ce422c67c30b34c127fdb067b3c9b4436b02cfbe125351" (Ar(Set,Ar(Set,Prop)));
  Hashtbl.add indextms "89e534b3d5ad303c952b3eac3b2b69eb72d95ba1d9552659f81c57725fc03350" (Ar(Set,Ar(Ar(Set,Prop),Set)));
  Hashtbl.add indextms "87d7604c7ea9a2ae0537066afb358a94e6ac0cd80ba277e6b064422035a620cf" (Ar(Set,Prop));
  Hashtbl.add indextms "bf1decfd8f4025a2271f2a64d1290eae65933d0f2f0f04b89520449195f1aeb8" (Ar(Set,Set));
  Hashtbl.add indextms "6f17daea88196a4c038cd716092bd8ddbb3eb8bddddfdc19e65574f30c97ab87" (Ar(Set,Ar(Set,Ar(Set,Prop))));
  Hashtbl.add indextms "0d574978cbb344ec3744139d5c1d0d90336d38f956e09a904d230c4fa06b30d1" (Ar(Set,Ar(Set,Prop)));
  Hashtbl.add indextms "09cdd0b9af76352f6b30bf3c4bca346eaa03d280255f13afb2e73fe8329098b6" (Ar(Set,Ar(Set,Prop)));
  Hashtbl.add indextms "c271c80f80f5f72a61f48aa63abcf552ccb5c1c1455890804f46f810f52c1725" (Ar(Set,Ar(Ar(Set,Ar(Set,Set)),Prop)));
  Hashtbl.add indextms "8aee977f39b94de3060d4e641f09019ff1a3f86f5572cb3093ec9aa4a0a4c21b" (Ar(Set,Ar(Ar(Set,Ar(Set,Set)),Ar(Ar(Set,Ar(Set,Set)),Ar(Ar(Set,Ar(Set,Set)),Ar(Set,Prop))))));
  Hashtbl.add indextms "65c0daed14d78ada9e0321a2b41d12cc9f628aacc67d8a940c28f08abf25f617" (Ar(Set,Ar(Ar(Set,Ar(Set,Set)),Ar(Ar(Set,Ar(Set,Set)),Ar(Ar(Set,Ar(Set,Set)),Ar(Set,Ar(Ar(Set,Ar(Set,Set)),Ar(Ar(Set,Ar(Set,Ar(Set,Set))),Ar(Ar(Set,Ar(Set,Set)),Ar(Ar(Set,Ar(Set,Ar(Set,Set))),Ar(Ar(Set,Ar(Set,Ar(Set,Set))),Ar(Ar(Set,Ar(Set,Set)),Ar(Ar(Set,Ar(Set,Set)),Ar(Ar(Set,Ar(Set,Set)),Ar(Ar(Set,Ar(Set,Set)),Prop)))))))))))))));
  Hashtbl.add indextms "c309fccae6f2952d12a16bfffc197737f9a1e290345afcd106428e646f9cbd2e" (Ar(Set,Ar(Ar(Set,Ar(Set,Set)),Ar(Ar(Set,Ar(Set,Set)),Ar(Ar(Set,Ar(Set,Set)),Ar(Set,Ar(Ar(Set,Ar(Set,Set)),Ar(Ar(Set,Ar(Set,Ar(Set,Set))),Ar(Ar(Set,Ar(Set,Set)),Ar(Ar(Set,Ar(Set,Ar(Set,Set))),Ar(Ar(Set,Ar(Set,Ar(Set,Set))),Ar(Ar(Set,Ar(Set,Set)),Ar(Ar(Set,Ar(Set,Set)),Ar(Ar(Set,Ar(Set,Set)),Ar(Ar(Set,Ar(Set,Set)),Prop)))))))))))))));
  Hashtbl.add indextms "cbf428d60d780d655f1b7593b16f52a9cbc57bf95a866db8389c330113d406f3" (Ar(Set,Ar(Ar(Set,Ar(Set,Set)),Ar(Ar(Set,Ar(Set,Set)),Ar(Ar(Set,Ar(Set,Set)),Ar(Set,Ar(Ar(Set,Ar(Set,Set)),Ar(Ar(Set,Ar(Set,Ar(Set,Set))),Ar(Ar(Set,Ar(Set,Set)),Ar(Ar(Set,Ar(Set,Ar(Set,Set))),Ar(Ar(Set,Ar(Set,Ar(Set,Set))),Ar(Ar(Set,Ar(Set,Set)),Ar(Ar(Set,Ar(Set,Set)),Ar(Ar(Set,Ar(Set,Set)),Ar(Ar(Set,Ar(Set,Set)),Prop)))))))))))))));
  Hashtbl.add indextms "f152c3f1281bd34cf1c2b19b596c7883b3995533b2fcccc0eaa6048037ebe4d3" (Ar(Set,Prop));
  Hashtbl.add indextms "4bc888f121f3c8defd33607bf8c316d9626aeb31d9d8b49058dc19828f9be72b" (Ar(Set,Ar(Set,Prop)));
  Hashtbl.add indextms "dff028b00391bf89df7db2deea89f2e8932114cc819135e93697f3555f1f256d" (Ar(Set,Ar(Set,Ar(Set,Prop))));
  Hashtbl.add indexknowns "4d0b1b3ca489073915e8701e021a09da22887f41f83e407df8eafe040825db18" ();
  Hashtbl.add indexknowns "e4b03c310442ae760be9945e176494db51515dfb952ee60fbd42e05527752af0" ();
  Hashtbl.add indexknowns "d8c32d0ac70c5760222c9adf1a3ca90f3cb6b5182b0f70a5d82cb9000abc77ef" ();
  Hashtbl.add indexknowns "5189b0389a1efe35ba744aa1436bb23541e75e8a85658313375e1e0b3321128f" ();
  Hashtbl.add indexknowns "920f955f033a1286fcaba96c8eb55d2079812a3041ff6b812df4cc2636156b59" ();
  Hashtbl.add indexknowns "0b67fbe4188c03468f8cd69c462ea8e5fb2269bf1fd67125a6456853d4ab7c74" ();
  Hashtbl.add indexknowns "b492ab96942311595fd53c93243cb7ab5314986bb8460d580d9382dfab90f7d1" ();
  Hashtbl.add indexknowns "c10976371705fb97042c207e4021721b0543188b170452fb918fb78d30b85c02" ();
  Hashtbl.add indexknowns "de0eaf5d33c0b573d63cc09df92572f243045babd3e3cb9aa49e72d618f6c7c9" ();
  Hashtbl.add indexknowns "73fa935250c44cafb3971bffe3b0cdef8869cd5693da6149f81741261543e04d" ();
  Hashtbl.add indexknowns "d163e2ba8be4862ce0d5ac17697ba5682d8de00436463bf450e9125489dacfc3" ();
  Hashtbl.add indexknowns "0c00a11817788d01d6282959a65fb640cd29eeecb21451696ae86d2c972ea6a1" ();
  Hashtbl.add indexknowns "81edf453007e75af3d93a8839c342755cf567e7e6a5013d8f463cb4140ccad71" ();
  Hashtbl.add indexknowns "6cb883a59e6fddeb39d4eebbe83417eba32939a89eb03700ed2435b07d6f31a5" ();
  Hashtbl.add indexknowns "06e53f495fbacecf847dbc5190516b217f2f92565fe8bfc4615d85e44cc77999" ();
  Hashtbl.add indexknowns "9b82b58da0e4095efc581051714ee0393eb423e395ec31dc00ec6d95c8e77b64" ();
  Hashtbl.add indexknowns "565012fb49695bbe133012328479877f4cead41cd3716f3772f3913917b21c27" ();
  Hashtbl.add indexknowns "8ad26e31e3f38cfdf8779e1d676300e70c868404a4fdeb018dd56527642ecee1" ();
  Hashtbl.add indexknowns "3ad2cd53af6e886067f36cf5d7a6686fb057b11e0af8ccb3ae491fce5213f516" ();
  Hashtbl.add indexknowns "7db945208f1c44134b64f1d6aa93463fa0c8bc5f1e02c9723c1a6c807e17bcc2" ();
  Hashtbl.add indexknowns "1e4e84c130e0882f993ba6d0725e5ce537488f3e04aeede384a09f2d1b06719d" ();
  Hashtbl.add indexknowns "5fded9d5ec7a3d33bfb840dc4a879fc85216375a19e401f04514b20635bf0648" ();
  Hashtbl.add indexknowns "87271e863c44798c3e4de1b8f94789072942588da2226bb4b8ab30dfd7954f42" ();
  Hashtbl.add indexknowns "1a6dfbf6bce4731c157b95653ed76d6f804db2aafca2c0924e438e0da6c4838e" ();
  Hashtbl.add indexknowns "d85840034f85eb9ab4e3d0362277ac520974920f971983d1894a834be2f58be4" ();
  Hashtbl.add indexknowns "bf0e9190cbf189b369083df40a90fa3be75393b0cdc894a6e7624bf15b71eae3" ();
  Hashtbl.add indexknowns "e1493c8264407ce4977f743da708af28f3e1817238c5e6a4df6fe74e4eac3608" ();
  Hashtbl.add indexknowns "cf0ceafc8c7e1c575b546e37d09bd7dc2acbed4fd47e5e5c6367777dce26e23d" ();
  Hashtbl.add indexknowns "02c002c28b5539eb457a8c7fcd1690a4459c1bfec19149160d3068bdebb8ab2d" ();
  Hashtbl.add indexknowns "03ef95824c9d27c385abd2cbf383f74dd9055886882b365893f0308b44a54a6a" ();
  Hashtbl.add indexknowns "b3f7f55079aa75828bfd3546160e7e051546d8bb9c652e454240c24b2953a703" ();
  Hashtbl.add indexknowns "bb7b109b6d194e6019b5ed8f268daa4a5944b43e2861d9c77bc9c90a26a6546f" ();
  Hashtbl.add indexknowns "b5e97e5c479a400f15307f87ad7213febacf085aca1fcffe72dc9b606b43b224" ();
  Hashtbl.add indexknowns "7fdf10edf434392f083f83041d690be73abf737b4349f00e2439155761461a53" ();
  Hashtbl.add indexknowns "255284955fa857314ff4caa3fb1f74c8c002da18d1dcb5dc7e42e903c456d5e9" ();
  Hashtbl.add indexknowns "406886eb8ba2e63fd142e06f6d7776bd0ac252db18f45614976726ccbeada812" ();
  Hashtbl.add indexknowns "03b8444fc49f5ce909b97c84648b4538c4bc9f6968e92a8a9243fc06db320dcf" ();
  Hashtbl.add indexknowns "7ee92353533ddf535d642b2bef129c16c883c14d39afce96770747278152c535" ();
  Hashtbl.add indexknowns "ad12f6917e0ca69c133ca56a02d806067620494392a4e55a3ac777c23bcf2ecb" ();
  Hashtbl.add indexknowns "ecefebac8563a68cbfce793120303743637d5819451daffc181b33f630a438b6" ();
  Hashtbl.add indexknowns "db908632cbf11771ec4744480ece7a038138cfb412c4002ac4861a544f7f9bc6" ();
  Hashtbl.add indexknowns "b6e249245c9d96bc7c87682fa4b263749fd50f89ced60ddba233249143b17ec6" ();
  Hashtbl.add indexknowns "b6fb7dfd3a4e7e4d40d079a52242724a194378edcb1723c9194906bdb983e7de" ();
  Hashtbl.add indexknowns "3c031eb9b813b10c973c2e405a449509495e89954b4927372175bde6a43672bb" ();
  Hashtbl.add indexknowns "0cb1eb090a19596f321d88b63bd310023ff30f1e55f649589c9dc7ad04918219" ();
  Hashtbl.add indexknowns "721e592a599e6ae4f540013ca4dff30ccb24f5a8279aecf7a527d3fdd365713e" ();
  Hashtbl.add indexknowns "1013258a7dd03314edde209dc3ed607693e989cd51567ee2b3770f70512a100c" ();
  Hashtbl.add indexknowns "fe0137795d3e0bb93daba2e7871618d0878ea87235765eda5ccfe10d795c4028" ();
  Hashtbl.add indexknowns "84ce1720f201517b5d7d0a55cf867ad2e1830c370df9f00103f3b8f4ede18442" ();
  Hashtbl.add indexknowns "1d313c5de18d746735e9bfa92b8e6f0bc60d8718fac1e198635080d3d0a330f1" ();
  Hashtbl.add indexknowns "d7d6188fe9d1029409ee6a37626f85d97049d246e0c58ce03256c1ba25c90b59" ();
  Hashtbl.add indexknowns "77e29ee5b23b44e015f7012c4a3d9fbe416b26f56b7d575c1c972d8fb7ae1d8e" ();
  Hashtbl.add indexknowns "80f19f3c9c089aeb52c61db93aac8c5865260969594e036dcae075b48816d85e" ();
  Hashtbl.add indexknowns "70181fda3cd0f3a49f0e332fffc1b82c7f3db1dea2b54ed28b6eea1422b3a0df" ();
  Hashtbl.add indexknowns "84847918a6f1940ec36a1b45fa4b2ae22fbd7db41d15edc80e45d7873aef54ff" ();
  Hashtbl.add indexknowns "6e58b31079ecf8bae23a9c138e685957465c6669ebd5614fe1de151266aca30b" ();
  Hashtbl.add indexknowns "61134abe2d03ac1a882ca1f6cb15a30302faf8a83dda486152c15415b76431eb" ();
  Hashtbl.add indexknowns "c7c71a691305af81552e17d4bddd97e45146ffae2dff038ee57c0e33239e8165" ();
  Hashtbl.add indexknowns "d52ab71745969a7954a3a9dff4f816cfa80f40893dc58cdbf7215538f7db6801" ();
  Hashtbl.add indexknowns "d98b8cabfcd1585ea3aed5e4341aa3efe311c5c234cfa49859f97f7d338267d6" ();
  Hashtbl.add indexknowns "ae80637a1c6842749a6b25cd0fb423826edeb06aa9ab471bcb1786a2417e9383" ();
  Hashtbl.add indexknowns "5d85ec0b61383a7f30ded95d038e36ade33f73733216927e94a6d3a6f29a7297" ();
  Hashtbl.add indexknowns "a548d12e16f10ede54e57981b037b682eafb7989b4b8fa8de01ef56bfa63f472" ();
  Hashtbl.add indexknowns "a548d12e16f10ede54e57981b037b682eafb7989b4b8fa8de01ef56bfa63f472" ();
  Hashtbl.add indexknowns "e21218f4f9fe181cc79122ffa00ecd0a9ab89d5c268eab61884d227cb092804c" ();
  Hashtbl.add indexknowns "8ae304381145ad470bcb5884f94b55179f2d878015514d28fb1fec556d6b9e8b" ();
  Hashtbl.add indexknowns "a662bd9f0cf9e8ac9a23debeebfe19b66bd11f19173953cea8e6470be043b9af" ();
  Hashtbl.add indexknowns "28c7a81eb6ad33b10da0764d900b05a10fd1dd2bcc5ed5e58bf75fa8a89d03b6" ();
  Hashtbl.add indexknowns "1cccbbadd044ffae74c0982aeadf97372aa58997086cc64bc5c256b36b3ea7fa" ();
  Hashtbl.add indexknowns "1263d8ba94ef9d0d6f7f2b39151f12d28d2d8c71ba57de61f6ac8cc6b355f701" ();
  Hashtbl.add indexknowns "4a22d56a44f5a868129999956374ce814c29898709c8dfc5c00040cdecb23ce6" ();
  Hashtbl.add indexknowns "6965cb1b0e7c2d05180bbda0d02badf5449f148f0012a7bb2c9ac88f6f71c940" ();
  Hashtbl.add indexknowns "44c2f2efdcb9da22db222a641a49682addeb32ed8efb2a51bfcd49ebb4ea1a45" ();
  Hashtbl.add indexknowns "5be13590762e2d145538955a6f24bcb3a5ad7c280d517cb99ade95547629db2a" ();
  Hashtbl.add indexknowns "26b135d99afcfe8c2658d9b6d4bd2ef9c7f18c6b3e9778ec8a094e1f7e9efcbc" ();
  Hashtbl.add indexknowns "b14a1577984678c7ad7c87c6bbb9ff2b176b0ad0eb46b57f8a7e05a97ac6640e" ();
  Hashtbl.add indexknowns "4eafc37373118a9f1243cba3928f3c40a9f0ac0526c943d0c7d25224eebc54ff" ();
  Hashtbl.add indexknowns "27ca9823a62a4121fe1658d93efca87de1c55324f15ceee21ab4565256024dc4" ();
  Hashtbl.add indexknowns "218e38705a57200a96de46b70654e61ef9d8b37738f2c493eccbdea77df8016f" ();
  Hashtbl.add indexknowns "c5522fbe8cf04414ffb8b169c05a81601ed8e85835d65624841b68acc0395eeb" ();
  Hashtbl.add indexknowns "a680fe3e891cb25b3b41f7ae2c2e87682b19cbd9b1c7c57edcf11097c7d01f7a" ();
  Hashtbl.add indexknowns "2c345ca37c0de440610409cb7e4a0618cca967ba6399aa197f52c4dddf7a6b1b" ();
  Hashtbl.add indexknowns "579c6bcc2e49082ddbe990366347358544e408099563117cb95fd61b761acb3e" ();
  Hashtbl.add indexknowns "9edbe245b62c3afd467422d8d7d68805a9556871be26d98031aaad0eecdcd728" ();
  Hashtbl.add indexknowns "602ffb18d1bbc5843fe462e731b3f73a5a976ee46e9da6bb6b40d8509a333aa5" ();
  Hashtbl.add indexknowns "659e82bb8ae88e2b04e50f651d5446a3fdf84711bbf57106c58d8bb717cec709" ();
  Hashtbl.add indexknowns "12451cb2963ac437754f119fd700a4c871292257bf373759b7bd92287a0143c3" ();
  Hashtbl.add indexknowns "a185fe1020a787ac3f5fc232b2cdb281c3c8d79b3befbea0c4edf43a97623f29" ();
  Hashtbl.add indexknowns "35ddbe41ccf8d636bb7be09d378ebbeafa96ab247fbb22d61de52fb2ae8f7d2c" ();
  Hashtbl.add indexknowns "ecbeeaf0badaae278dd637ce4637ef85208490fc1eae35c0e79164f3f5b9fdf5" ();
  Hashtbl.add indexknowns "5b5879bfb5f5ab380758f631c5dda71fdd77a20870fc0d9ff94c46e173ce9d04" ();
  Hashtbl.add indexknowns "c5ca53a6adf517d6574675abbb5f9032ef9ad79b9b8714203f092faaa8ba0887" ();
  Hashtbl.add indexknowns "82640bea0f55be344d1e16e89f41f32887a7a47d8ee55bff12f5481d83e942b5" ();
  Hashtbl.add indexknowns "7fca94a5974ea12bc67f55a16f67dbaca0d58af6648a5661c36b0e6c572cd896" ();
  Hashtbl.add indexknowns "f030a2d2c44eabec7a4cc7446328bc1194822bd4441b8a806ebda667f414ca66" ();
  Hashtbl.add indexknowns "d20efd6ecacb0cb3079f2127a08724476d4eabf3507c95ed5457caf478e82dc0" ();
  Hashtbl.add indexknowns "ec74e0e0b43759c2e284f91d3fc896bad3dfb5b25e731877ccefe7c66e001835" ();
  Hashtbl.add indexknowns "89dc652e8e86a81513b682fa88ff665d5c7ce80f8e965051c98997954b367bf9" ();
  Hashtbl.add indexknowns "22071e7ec3d44038501eae7b845bd1fe4144e084a8985f9cc2d5dbdabd2f5592" ();
  Hashtbl.add indexknowns "5d04957e5d383065e03c72e5f6f126c0dfebf4f039551609c1be24d94cf2b447" ();
  Hashtbl.add indexknowns "95d047b09ce188d473c5e7498669c05fbe6529fc7483ec34f11eec9f9eb9a361" ();
  Hashtbl.add indexknowns "89bdea0aa616a43a477ff5a2b8f8d93ffd0e81538b14f1e3acf287a190a89ddd" ();
  Hashtbl.add indexknowns "cbb07c2a4d089aafb664d96f12f4bb4d73181a7d7b6079750a8b1f00ffa3b378" ();
  Hashtbl.add indexknowns "a9f7dddd1e068a3c747980f5d0555f105b6f79bf8350ae9f2a610b1ad88118a6" ();
  Hashtbl.add indexknowns "bf9e3955698cfdd47596df01c71e1cf03ac8e02f35e01b8b2560828b931bf3b6" ();
  Hashtbl.add indexknowns "72fb3b732d20df7b10a7d845367a5d455a600ffaad98f8e89af0d369750d36ee" ();
  Hashtbl.add indexknowns "85ddba6a7609c822f37b453fe65991931570c7b63ba128a986dba37ced7bbcf1" ();
  Hashtbl.add indexknowns "047aee660e1a13eb74426c75dbc197f437b5b8efbb63d3fb3c4fe31dfaa6eb61" ();
  Hashtbl.add indexknowns "822a836127ce60e878d67d66e2b4a46ea0b813f9f55cc8ff810951d073cc1dbc" ();
  Hashtbl.add indexknowns "aa9ee728af378f05d9eb99b00d097d784ce116396b9b970397b723582e0352eb" ();
  Hashtbl.add indexknowns "77dc3318ff617828477b0a91f762ed88177211d91054f972756c52eddaba4efc" ()

let preset_mizar_index () =
  Hashtbl.clear indextms;
  Hashtbl.clear indexknowns;
  (** In is already Prim 1 and Union is already Prim 3 **)
  Hashtbl.add indextms "174b78e53fc239e8c2aab4ab5a996a27e3e5741e88070dad186e05fb13f275e5" (Ar(Ar(Set,Prop),Set));
  Hashtbl.add indextms "73c9efe869770ab42f7cde0b33fe26bbc3e2bd157dad141c0c27d1e7348d60f5" (Ar(Set,Ar(Set,Prop)));
  Hashtbl.add indextms "f55f90f052decfc17a366f12be0ad237becf63db26be5d163bf4594af99f943a" (Ar(Set,Ar(Set,Set)));
  Hashtbl.add indextms "844774016d959cff921a3292054b30b52f175032308aa11e418cb73f5fef3d54" (Ar(Set,Set))

let preset_setmm_index () =
  Hashtbl.clear indextms;
  Hashtbl.clear indexknowns;
  ()

let preset_hoas_index () =
  Hashtbl.clear indextms;
  Hashtbl.clear indexknowns;
  Hashtbl.add indextms "d58762d200971dcc7f1850726d9f2328403127deeba124fc3ba2d2d9f7c3cb8c" (Ar(Set,Ar(Set,Set)));
  Hashtbl.add indextms "73c9efe869770ab42f7cde0b33fe26bbc3e2bd157dad141c0c27d1e7348d60f5" (Ar(Ar(Set,Set),Set))

let read_all fn =
  let c = open_in fn in
  try
    let n = in_channel_length c in
    let s = really_input_string c n in
    close_in c;
    s
  with e ->
    close_in_noerr c;
    raise e

let audit_vampire_cert_v1_source_context cert source_map =
  let external_definition_names = vampire_source_map_external_symbol_names source_map in
  let bindings =
    Vampire_cert_v1.native_certificate_source_bindings
      ~source_map
      ~external_definition_names
      cert
  in
  let standalone_local_hypotheses =
    let rec add seen acc = function
      | [] -> List.rev acc
      | binding :: rest ->
          if binding.Vampire_cert_v1.core_native_source_map_kind = "local_fact"
             && binding.Vampire_cert_v1.core_native_source_name <> ""
             && not (List.mem binding.Vampire_cert_v1.core_native_source_name seen)
          then
            add
              (binding.Vampire_cert_v1.core_native_source_name :: seen)
              ((binding.Vampire_cert_v1.core_native_source_name,
                binding.Vampire_cert_v1.core_native_source_proposition) :: acc)
              rest
          else add seen acc rest
    in
    add [] [] bindings
  in
  let context =
    {
      Vampire_source_context.proof_delta =
        vampire_source_context_delta_with_source_map source_map;
      known_table = sigknh;
      symbol_table = vampire_source_context_symbol_table_with_source_map source_map;
      term_context = [];
      local_term_projection = [];
      local_terms = [];
      local_hypotheses = standalone_local_hypotheses;
      local_definitions = [];
    }
  in
  let audit = Vampire_source_context.resolve context bindings in
  let local_or_unhashed =
    audit.Vampire_source_context.local_checked
    + audit.Vampire_source_context.local_missing
    + audit.Vampire_source_context.local_mismatch
    + audit.Vampire_source_context.local_definition_matched
    + audit.Vampire_source_context.generated_checked
    + audit.Vampire_source_context.conjecture_checked
    + audit.Vampire_source_context.unresolved
  in
  Printf.printf
    "Vampire certificate v1 source context audited total=%d known_checked=%d known_missing=%d known_mismatch=%d local_checked=%d local_missing=%d local_mismatch=%d definition_resolved=%d local_definition_matched=%d definition_missing=%d generated_checked=%d conjecture_checked=%d unresolved=%d local_or_unhashed=%d.\n"
    audit.Vampire_source_context.total
    audit.Vampire_source_context.known_checked
    audit.Vampire_source_context.known_missing
    audit.Vampire_source_context.known_mismatch
    audit.Vampire_source_context.local_checked
    audit.Vampire_source_context.local_missing
    audit.Vampire_source_context.local_mismatch
    audit.Vampire_source_context.definition_resolved
    audit.Vampire_source_context.local_definition_matched
    audit.Vampire_source_context.definition_missing
    audit.Vampire_source_context.generated_checked
    audit.Vampire_source_context.conjecture_checked
    audit.Vampire_source_context.unresolved
    local_or_unhashed;
  let issue_count = List.length audit.Vampire_source_context.issues in
  let rec take n = function
    | _ when n <= 0 -> []
    | [] -> []
    | x :: xs -> x :: take (n - 1) xs
  in
  let issue_summary =
    audit.Vampire_source_context.issues
    |> take 5
    |> List.map
         (fun issue ->
            Printf.sprintf
              "%s:%s:%s:%s:%s"
              issue.Vampire_source_context.issue_reason
              issue.Vampire_source_context.issue_step
              issue.Vampire_source_context.issue_kind
              issue.Vampire_source_context.issue_name
              issue.Vampire_source_context.issue_hash)
    |> String.concat ","
  in
  Printf.printf
    "Vampire certificate v1 source context issues count=%d sample=%s.\n"
    issue_count
    issue_summary;
  if !vampirecertv1sourcecontextstrict
     && (audit.Vampire_source_context.known_missing > 0
         || audit.Vampire_source_context.known_mismatch > 0
         || audit.Vampire_source_context.definition_missing > 0
         || audit.Vampire_source_context.unresolved > 0) then
    raise
      (Vampire_cert_v1.Error
         "strict source-context audit failed: at least one source did not resolve to a checked proof in the loaded Megalodon context");
  let external_hypotheses = List.map snd standalone_local_hypotheses in
  audit.Vampire_source_context.source_proofs, external_hypotheses

let check_vampire_cert_v1_file fn =
  try
    let cert = Vampire_cert_v1.parse_certificate (read_all fn) in
    begin if !vampirecertv1coreclosed then
      let core_count = Vampire_cert_v1.validate_certificate_core_fragment cert in
      Printf.printf "Vampire certificate v1 core fragment checked %d step%s.\n"
        core_count
        (if core_count = 1 then "" else "s")
    end;
    let checked =
      if !vampirecertv1strict || !vampirecertv1closed then Vampire_cert_v1.check_certificate_strict cert
      else Vampire_cert_v1.check_certificate cert
    in
    let source_map_for_emit = ref [] in
    let source_origin_for_emit = ref None in
    let source_proofs_for_native = ref [] in
    let source_external_hypotheses_for_native = ref [] in
    begin match !vampirecertv1source with
    | None ->
        if !vampirecertv1corepfcheck || !vampirecertv1preprocesspfcheck then
          raise
            (Vampire_cert_v1.Error
               "native proof-term checking requires -vampirecertv1source with Megalodon origin metadata");
        if (!vampirecertv1strict || !vampirecertv1closed)
           && Vampire_cert_v1.certificate_source_count cert > 0 then
          raise (Vampire_cert_v1.Error "strict certificate v1 requires -vampirecertv1source for source-backed inputs")
    | Some source_fn ->
        let source_content = read_all source_fn in
        let source_map = Vampire_cert_v1.parse_source_map source_content in
        begin match Vampire_cert_v1.parse_source_origin source_content with
        | Some origin ->
            source_origin_for_emit := Some origin;
            let pos =
              match origin.Vampire_cert_v1.source_origin_line, origin.Vampire_cert_v1.source_origin_char with
              | Some line, Some chr -> Printf.sprintf " line %d char %d" line chr
              | Some line, None -> Printf.sprintf " line %d" line
              | None, Some chr -> Printf.sprintf " char %d" chr
              | None, None -> ""
            in
            Printf.printf "Vampire certificate v1 source origin %s%s (%s).\n"
              origin.Vampire_cert_v1.source_origin_file
              pos
              origin.Vampire_cert_v1.source_origin_kind
        | None ->
            if !vampirecertv1corepfcheck || !vampirecertv1preprocesspfcheck then
              raise
                (Vampire_cert_v1.Error
                   "native proof-term checking requires Megalodon origin metadata in -vampirecertv1source")
        end;
        source_map_for_emit := source_map;
        let source_audit =
          Vampire_cert_v1.audit_certificate_sources
            ~require_formula_match:(!vampirecertv1strict || !vampirecertv1closed)
            source_map
            cert
        in
        let source_count =
          source_audit.Vampire_cert_v1.source_obligations_total
        in
        Printf.printf "Vampire certificate v1 source map checked %d source%s.\n"
          source_count
          (if source_count = 1 then "" else "s");
        if !vampirecertv1sourcecontext || !vampirecertv1sourcecontextstrict then
          begin
            let source_proofs, external_hypotheses =
              audit_vampire_cert_v1_source_context cert source_map
            in
            source_proofs_for_native := source_proofs;
            source_external_hypotheses_for_native := external_hypotheses
          end;
        if !vampirecertv1sourceaudit then
          Printf.printf
            "Vampire certificate v1 source obligations audited total=%d formula_checked=%d formula_unsupported=%d formula_missing=%d equality_checked=%d set_reflexivity_checked=%d true_checked=%d.\n"
            source_audit.Vampire_cert_v1.source_obligations_total
            source_audit.Vampire_cert_v1.source_obligations_formula_checked
            source_audit.Vampire_cert_v1.source_obligations_formula_unsupported
            source_audit.Vampire_cert_v1.source_obligations_formula_missing
            source_audit.Vampire_cert_v1.source_obligations_equality_checked
            source_audit.Vampire_cert_v1.source_obligations_set_reflexivity_checked
            source_audit.Vampire_cert_v1.source_obligations_true_checked
    end;
    Printf.printf "Vampire certificate v1%s checked %d step%s.\n"
      (if !vampirecertv1coreclosed then " core closed"
       else if !vampirecertv1closed then " closed"
       else if !vampirecertv1strict then " strict"
       else "")
      (List.length checked)
      (if List.length checked = 1 then "" else "s");
    let native_certificate_sgdelta native =
      let merged = Hashtbl.copy sigdelta in
      Hashtbl.iter
        (fun h v ->
           Hashtbl.replace merged h v)
        (Vampire_cert_v1.approved_native_sgdelta ());
      Hashtbl.iter
        (fun h v ->
           if not (Hashtbl.mem merged h) then Hashtbl.add merged h v)
        native.Vampire_cert_v1.core_native_delta_table;
      Hashtbl.iter
        (fun h v ->
           if not (Hashtbl.mem merged h) then
             Hashtbl.add merged h v
           else if not (valid_id_p h) then
             Hashtbl.replace merged h v)
        (vampire_source_context_delta_with_source_map !source_map_for_emit);
      merged
    in
    let native_certificate_sgtmof native =
      let merged = Hashtbl.copy sigtmof in
      Hashtbl.iter
        (fun h v ->
           if not (Hashtbl.mem merged h) then Hashtbl.add merged h v)
        native.Vampire_cert_v1.core_native_symbol_table;
      merged
    in
    let check_native_certificate_proof native =
      let rec peel cxtm proof prop =
        match proof, prop with
        | TLam (proof_tp, proof_body), All (prop_tp, prop_body)
            when proof_tp = prop_tp ->
            peel (proof_tp :: cxtm) proof_body prop_body
        | _ ->
            check_propofpf
              (native_certificate_sgdelta native)
              (native_certificate_sgtmof native)
              cxtm
              !source_external_hypotheses_for_native
              proof
              prop
              []
      in
      peel
        []
        native.Vampire_cert_v1.core_native_proof
        native.Vampire_cert_v1.core_native_proposition
    in
    begin if !vampirecertv1corepfcheck then
      let external_definition_names =
        vampire_source_map_external_symbol_names !source_map_for_emit
      in
      let native_core =
        Vampire_cert_v1.elaborate_core_resolution_refutation_native
          ~source_map:!source_map_for_emit
          ~source_proofs:!source_proofs_for_native
          ~external_hypotheses:!source_external_hypotheses_for_native
          ~external_delta_table:
            (vampire_source_context_delta_with_source_map !source_map_for_emit)
          ~external_definition_names
          cert
      in
      match check_native_certificate_proof native_core with
      | Some _ ->
          Printf.printf
            "Vampire certificate v1 native core proof term checked %d step%s.\n"
            native_core.Vampire_cert_v1.core_native_steps
            (if native_core.Vampire_cert_v1.core_native_steps = 1 then "" else "s");
          Printf.printf
            "Vampire certificate v1 native core source bindings checked %d assumption%s.\n"
            (List.length native_core.Vampire_cert_v1.core_native_source_bindings)
            (if List.length native_core.Vampire_cert_v1.core_native_source_bindings = 1 then "" else "s");
          Printf.printf
            "Vampire certificate v1 native core source assumptions remaining %d.\n"
            native_core.Vampire_cert_v1.core_native_source_assumptions;
          vampire_print_remaining_source_summary
            "Vampire certificate v1 native core"
            !source_proofs_for_native
            native_core.Vampire_cert_v1.core_native_source_assumption_bindings;
          Printf.printf
            "Vampire certificate v1 native core source propositions recorded %d assumption%s.\n"
            (List.length
               (List.filter
                  (fun binding ->
                     binding.Vampire_cert_v1.core_native_source_proposition
                     <> TmH "")
                  native_core.Vampire_cert_v1.core_native_source_bindings))
            (if List.length native_core.Vampire_cert_v1.core_native_source_bindings = 1 then "" else "s");
          begin match
            vampire_reconstruct_final_conjecture_from_native_core
              !source_map_for_emit
              !source_proofs_for_native
              native_core
          with
          | Some _ ->
              Printf.printf
                "Vampire certificate v1 native core final conjecture proof term checked.\n"
          | None -> ()
          end
      | None ->
          raise (Vampire_cert_v1.Error "native core proof term does not prove its proposition")
    end;
    begin if !vampirecertv1preprocesspfcheck then
      let external_definition_names =
        vampire_source_map_external_symbol_names !source_map_for_emit
      in
      let native_preprocess =
        Vampire_cert_v1.elaborate_preprocess_refutation_native
          ~source_map:!source_map_for_emit
          ~source_proofs:!source_proofs_for_native
          ~external_hypotheses:!source_external_hypotheses_for_native
          ~external_delta_table:
            (vampire_source_context_delta_with_source_map !source_map_for_emit)
          ~external_definition_names
          cert
      in
      match check_native_certificate_proof native_preprocess with
      | Some _ ->
          Printf.printf
            "Vampire certificate v1 native preprocess proof term checked %d step%s.\n"
            native_preprocess.Vampire_cert_v1.core_native_steps
            (if native_preprocess.Vampire_cert_v1.core_native_steps = 1 then "" else "s");
          Printf.printf
            "Vampire certificate v1 native preprocess source bindings checked %d assumption%s.\n"
            (List.length native_preprocess.Vampire_cert_v1.core_native_source_bindings)
            (if List.length native_preprocess.Vampire_cert_v1.core_native_source_bindings = 1 then "" else "s");
          Printf.printf
            "Vampire certificate v1 native preprocess source assumptions remaining %d.\n"
            native_preprocess.Vampire_cert_v1.core_native_source_assumptions;
          vampire_print_remaining_source_summary
            "Vampire certificate v1 native preprocess"
            !source_proofs_for_native
            native_preprocess.Vampire_cert_v1.core_native_source_assumption_bindings;
          Printf.printf
            "Vampire certificate v1 native preprocess source propositions recorded %d assumption%s.\n"
            (List.length
               (List.filter
                  (fun binding ->
                     binding.Vampire_cert_v1.core_native_source_proposition
                     <> TmH "")
                  native_preprocess.Vampire_cert_v1.core_native_source_bindings))
            (if List.length native_preprocess.Vampire_cert_v1.core_native_source_bindings = 1 then "" else "s");
          begin match
            vampire_reconstruct_final_conjecture_from_native_core
              !source_map_for_emit
              !source_proofs_for_native
              native_preprocess
          with
          | Some _ ->
              Printf.printf
                "Vampire certificate v1 native preprocess final conjecture proof term checked.\n"
          | None -> ()
          end
      | None ->
          raise (Vampire_cert_v1.Error "native preprocess proof term does not prove its proposition")
    end;
    begin match !vampirecertv1emit with
    | None -> ()
    | Some out_fn ->
        let content =
          Vampire_cert_v1.emit_simple_megalodon
            ~source_map:!source_map_for_emit
            ?source_origin:!source_origin_for_emit
            ~closed:!vampirecertv1closed
            cert
        in
        let ch = open_out out_fn in
        output_string ch content;
        close_out ch;
        Printf.printf "Vampire certificate v1 emitted simple Megalodon proof to %s.\n" out_fn
    end
  with Vampire_cert_v1.Error msg ->
    raise (Failure ("Vampire certificate v1 check failed: " ^ msg))

(*** "main" ***)
let _ =
  (*** There are some global names I need before getting started to make the proof tactics work, so they are precomputed here. ***)
  fal := preset_ptm_lam_id (0,All(Prop,DB(0)));
  fale := preset_ptm_all_id (0,Imp(TmH(!fal),All(Prop,DB(0))));
  eqPoly := preset_ptm_lam_id (1,Lam(TpVar(0),Lam(TpVar(0),All(Ar(TpVar(0),Ar(TpVar(0),Prop)),Imp(Ap(Ap(DB(0),DB(2)),DB(1)),Ap(Ap(DB(0),DB(1)),DB(2)))))));
  conj := preset_ptm_lam_id (0,Lam(Prop,Lam(Prop,All(Prop,Imp(Imp(DB(2),Imp(DB(1),DB(0))),DB(0))))));
  disj := preset_ptm_lam_id (0,Lam(Prop,Lam(Prop,All(Prop,Imp(Imp(DB(2),DB(0)),Imp(Imp(DB(1),DB(0)),DB(0)))))));
  expoly := preset_ptm_lam_id (1,Lam(Ar(TpVar(0),Prop),All(Prop,Imp(All(TpVar(0),Imp(Ap(DB(2),DB(0)),DB(1))),DB(0)))));
  expolyI := preset_ptm_all_id (1,All(Ar(TpVar(0),Prop),All(TpVar(0),Imp(Ap(DB(1),DB(0)),Ap(TpAp(TmH(!expoly),TpVar(0)),DB(1))))));
  preset_mizar_index();
  stm := string_of_float (Unix.time());
  let i = Array.length Sys.argv in
  if i = 1 then
    mgcheck stdin (*** if no arguments are given, read and check from stdin ***)
  else (*** otherwise, assume the last argument is the main file from which to read and check ***)
    begin
      (*** Process command line arguments including reading signature input files ***)
      let j = ref 0 in
      while (!j < i - 2) do
	incr j;
	if Sys.argv.(!j) = "-I" then
	  begin
	    match !latex with
	    | Some(_) -> raise (Failure("-I must come before -latex"))
	    | None -> includingsigfile := true
          end
        else if Sys.argv.(!j) = "-legend" then
          begin
            if !j < i-2 then
	      begin
		incr j;
		let f = open_in (Sys.argv.(!j)) in
                try
                  while true do
                    let l = input_line f in
                    if l = "Term" then
                       let l1 = input_line f in
                       let l2 = input_line f in
                       Hashtbl.add tmh_legend l1 l2
                    else if l = "Known" then
                       let l1 = input_line f in
                       let l2 = input_line f in
                       Hashtbl.add knownh_legend l1 l2
                    else if l = "Prim" then
                       let l1 = input_line f in
                       let l2 = input_line f in
                       Hashtbl.add prim_legend (int_of_string l1) l2
                  done
                with End_of_file -> close_in f
	      end
          end
        else if Sys.argv.(!j) = "-latex" then
          begin
	    if !j < i-2 then
	      begin
		incr j;
		latex := Some(open_out (Sys.argv.(!j)))
	      end
	    else
	      raise (Failure("Expected -latex <filename>"))
          end
        else if Sys.argv.(!j) = "-globalhrefs" then
          globalhrefs := true
        else if Sys.argv.(!j) = "-preambleassig" then
          preambleassig := true
        else if Sys.argv.(!j) = "-htmlonlypfgsupp" then
          begin
            if !j < i-2 then
              begin
                incr j;
                read_pfg_supp (Sys.argv.(!j));
                htmlonlypfgsupp := true;
              end
            else
              raise (Failure "-htmlonlypfgsupp should be followed by a pfg summary2 file")
          end
        else if Sys.argv.(!j) = "-html" then
          begin
	    if !j < i-2 then
	      begin
		incr j;
                let hc = open_out (Sys.argv.(!j)) in
		html := Some(hc);
                Printf.fprintf hc "<html><head>\n";
                Printf.fprintf hc "<link rel=\"stylesheet\" href=\"mg.css\">\n";
                Printf.fprintf hc "</head><body>\n";
	      end
	    else
	      raise (Failure("Expected -html <filename>"))
          end
        else if Sys.argv.(!j) = "-megawiki" then
          begin
            if !j < i-2 then
              begin
                incr j;
                megawiki := Some(setup_megawiki (Sys.argv.(!j)))
              end
            else
              raise (Failure("Expected -megawiki <directory>"))
          end
        else if Sys.argv.(!j) = "-eagerdeltas" then
          eagerdeltas := true
        else if Sys.argv.(!j) = "-nodoublecheck" then
          doublecheckpf := false
        else if Sys.argv.(!j) = "-archivefile" then
          begin
	    if !j < i-2 then
	      begin
		incr j;
                archivefile := Some(Sys.argv.(!j))
	      end
	    else
	      raise (Failure("Expected -archivefile <outfile>"))
          end
        else if Sys.argv.(!j) = "-removepfs" then
          begin
	    if !j < i-2 then
	      begin
		incr j;
                removepfs := Some(Sys.argv.(!j))
	      end
	    else
	      raise (Failure("Expected -removepfs <outfile>"))
          end
        else if Sys.argv.(!j) = "-allowincompleteqed" then
          allowincompleteqed := true
        else if Sys.argv.(!j) = "-trustdeclaredaxioms" then
          trustdeclaredaxioms := true
        else if Sys.argv.(!j) = "-fof" then
          begin
	    if !j < i-2 then
	      begin
		incr j;
                fof := Some(Sys.argv.(!j))
	      end
	    else
	      raise (Failure("Expected -fof <fileprefix>"))
          end
        else if Sys.argv.(!j) = "-th0" then
          begin
	    if !j < i-2 then
	      begin
		incr j;
                th0 := Some(Sys.argv.(!j))
	      end
	    else
	      raise (Failure("Expected -th0 <fileprefix>"))
          end
        else if Sys.argv.(!j) = "-createabyprobs" then
          begin
	    if !j < i-2 then
	      begin
		incr j;
                createabyprobs := true;
                th0 := Some(Sys.argv.(!j));
                fof := Some(Sys.argv.(!j))
	      end
	    else
	      raise (Failure("Expected -createabyprobs <fileprefix>"))
          end
        else if Sys.argv.(!j) = "-vampireaby" then
          begin
	    if !j < i-2 then
	      begin
		incr j;
                vampireaby := Some(Sys.argv.(!j))
	      end
	    else
	      raise (Failure("Expected -vampireaby <vampire-binary>"))
          end
        else if Sys.argv.(!j) = "-vampireabyoutdir" then
          begin
	    if !j < i-2 then
	      begin
		incr j;
                vampireabyoutdir := Sys.argv.(!j)
	      end
	    else
	      raise (Failure("Expected -vampireabyoutdir <directory>"))
          end
        else if Sys.argv.(!j) = "-vampireabytimeout" then
          begin
	    if !j < i-2 then
	      begin
		incr j;
                vampireabytimeout := int_of_string (Sys.argv.(!j))
	      end
	    else
	      raise (Failure("Expected -vampireabytimeout <seconds>"))
          end
        else if Sys.argv.(!j) = "-vampireabyschedule" then
          begin
	    if !j < i-2 then
	      begin
		incr j;
                vampireabyschedule := Sys.argv.(!j)
	      end
	    else
	      raise (Failure("Expected -vampireabyschedule <schedule>"))
          end
        else if Sys.argv.(!j) = "-vampireabyproof" then
          begin
	    if !j < i-2 then
	      begin
		incr j;
                vampireabyproof := Sys.argv.(!j)
	      end
	    else
	      raise (Failure("Expected -vampireabyproof <tptp|leancheck|megalodon>"))
          end
        else if Sys.argv.(!j) = "-vampireabynative" then
          begin
            vampireabynative := true
          end
        else if Sys.argv.(!j) = "-vampireabynativestrict" then
          begin
            vampireabynative := true;
            vampireabynativestrict := true
          end
        else if Sys.argv.(!j) = "-vampireabyqualifying" then
          begin
            vampireabynative := true;
            vampireabynativestrict := true;
            vampireabyqualifying := true;
            vampireabyproof := "megalodon";
            if !vampireabytimeout > 10 then vampireabytimeout := 10
          end
        else if Sys.argv.(!j) = "-vampireabytarget" then
          begin
	    if !j < i-3 then
	      begin
                vampireabytarget := Some(int_of_string (Sys.argv.(!j+1)),int_of_string (Sys.argv.(!j+2)));
                j := !j + 2
	      end
	    else
	      raise (Failure("Expected -vampireabytarget <lineno> <charno>"))
          end
        else if Sys.argv.(!j) = "-vampireabytargetstop" then
          begin
            vampireabytargetstop := true
          end
        else if Sys.argv.(!j) = "-vampirecertv1" then
          begin
	    if !j < i-2 then
	      begin
		incr j;
                vampirecertv1 := Some(Sys.argv.(!j))
	      end
	    else
	      raise (Failure("Expected -vampirecertv1 <certificate.sexp>"))
          end
        else if Sys.argv.(!j) = "-vampirecertv1strict" then
          vampirecertv1strict := true
        else if Sys.argv.(!j) = "-vampirecertv1closed" then
          begin
            vampirecertv1strict := true;
            vampirecertv1closed := true
          end
        else if Sys.argv.(!j) = "-vampirecertv1coreclosed" then
          begin
            vampirecertv1strict := true;
            vampirecertv1closed := true;
            vampirecertv1coreclosed := true
          end
        else if Sys.argv.(!j) = "-vampirecertv1corepfcheck" then
          begin
            vampirecertv1strict := true;
            vampirecertv1closed := true;
            vampirecertv1coreclosed := true;
            vampirecertv1corepfcheck := true
          end
        else if Sys.argv.(!j) = "-vampirecertv1preprocesspfcheck" then
          begin
            vampirecertv1strict := true;
            vampirecertv1closed := true;
            vampirecertv1preprocesspfcheck := true
          end
        else if Sys.argv.(!j) = "-vampirecertv1source" then
          begin
	    if !j < i-2 then
	      begin
		incr j;
                vampirecertv1source := Some(Sys.argv.(!j))
	      end
	    else
	      raise (Failure("Expected -vampirecertv1source <problem.th0.p>"))
          end
        else if Sys.argv.(!j) = "-vampirecertv1sourceaudit" then
          vampirecertv1sourceaudit := true
        else if Sys.argv.(!j) = "-vampirecertv1sourcecontext" then
          vampirecertv1sourcecontext := true
        else if Sys.argv.(!j) = "-vampirecertv1sourcecontextstrict" then
          begin
            vampirecertv1sourcecontext := true;
            vampirecertv1sourcecontextstrict := true
          end
        else if Sys.argv.(!j) = "-vampirecertv1emit" then
          begin
	    if !j < i-2 then
	      begin
		incr j;
                vampirecertv1emit := Some(Sys.argv.(!j))
	      end
	    else
	      raise (Failure("Expected -vampirecertv1emit <out.mg>"))
          end
        else if Sys.argv.(!j) = "-vampirechecklivepropchoice" then
          vampirechecklivepropchoice := true
        else if Sys.argv.(!j) = "-fofallsubgoals" then
          begin
	    if !j < i-2 then
	      begin
		incr j;
                fof := Some(Sys.argv.(!j));
                fofallsubgoals := true;
	      end
	    else
	      raise (Failure("Expected -fofallsubgoals <fileprefix>"))
          end
        else if Sys.argv.(!j) = "-fofpostsubgoals" then
          begin
	    if !j < i-2 then
	      begin
		incr j;
                fof := Some(Sys.argv.(!j));
                fofpostsubgoals := true;
	      end
	    else
	      raise (Failure("Expected -fofpostsubgoals <fileprefix>"))
          end
        else if Sys.argv.(!j) = "-th0single" then
          begin
	    if !j < i-4 then
	      begin
		incr j;
                th0 := Some(Sys.argv.(!j));
                th0singlesubgoal := Some(int_of_string (Sys.argv.(!j+1)),int_of_string (Sys.argv.(!j+2)));
                j := !j + 2;
	      end
	    else
	      raise (Failure("Expected -th0single <fileprefix> <lineno> <charno>"))
          end
        else if Sys.argv.(!j) = "-th0allsubgoals" then
          begin
	    if !j < i-2 then
	      begin
		incr j;
                th0 := Some(Sys.argv.(!j));
                th0allsubgoals := true;
	      end
	    else
	      raise (Failure("Expected -th0allsubgoals <fileprefix>"))
          end
        else if Sys.argv.(!j) = "-th0postsubgoals" then
          begin
	    if !j < i-2 then
	      begin
		incr j;
                th0 := Some(Sys.argv.(!j));
                th0postsubgoals := true;
	      end
	    else
	      raise (Failure("Expected -th0postsubgoals <fileprefix>"))
          end
        else if Sys.argv.(!j) = "-sexprinfo" then
          begin
            sexprinfo := true
          end
        else if Sys.argv.(!j) = "-reportbushydeps" then
          begin
	    if !j < i-2 then
	      begin
		incr j;
                reportbushydeps := Some(open_out (Sys.argv.(!j)));
	      end
	    else
	      raise (Failure("Expected -reportbushydeps <file>"))
          end
        else if Sys.argv.(!j) = "-usebushydeps" then
          begin
	    if !j < i-2 then
	      begin
		incr j;
                bushy := true;
                let ch = open_in Sys.argv.(!j) in
                try
                  while true do
                    let l = input_line ch in
                    if l.[0] = 'K' then
                      Hashtbl.add bushykdeps (String.sub l 2 (String.length l - 2)) ()
                    else if l.[0] = 'H' then
                      Hashtbl.add bushyhdeps (int_of_string (String.sub l 2 (String.length l - 2))) ()
                  done
                with End_of_file -> close_in ch
	      end
	    else
	      raise (Failure("Expected -usebushydeps <file>"))
          end
        else if Sys.argv.(!j) = "-th0ps1" then
          begin
	    if !j < i-2 then
	      begin
		incr j;
                th0ps1 := true;
                th0 := Some(Sys.argv.(!j))
	      end
	    else
	      raise (Failure("Expected -th0ps1 <fileprefix>"))
          end
        else if Sys.argv.(!j) = "-sexprallsubgoals" then
          begin
	    if !j < i-2 then
	      begin
		incr j;
                sexprallsubgoals := Some(Sys.argv.(!j),"",0)
	      end
	    else
	      raise (Failure("Expected -sexprallsubgoals <fileprefix>"))
          end
	else if Sys.argv.(!j) = "-s" then
	  begin
	    includingsigfile := false;
	    if !j < i-2 then
	      begin
		incr j;
		match !sigoutfile with
		| Some _ -> raise (Failure("Cannot use -s twice"))
		| None -> sigoutfile := Some (open_out (Sys.argv.(!j)))
	      end
	    else
	      raise (Failure("Expected -s <outsigfilename>"))
	  end
        else if Sys.argv.(!j) = "-normalizepf" then
          normalizepf := true
        else if Sys.argv.(!j) = "-optimizepf1" then
          optimizepf1 := true
        else if Sys.argv.(!j) = "-optimizepf2" then
          begin
            optimizepf2 := true;
            if !j < i-3 then
              begin
                incr j;
                optimizepf2tc := int_of_string (Sys.argv.(!j));
                incr j;
                optimizepf2pc := int_of_string (Sys.argv.(!j));
              end
            else
              raise (Failure("Expected -optimizepf2 <int> <int>"))
          end
        else if Sys.argv.(!j) = "-hf" then
          begin
            pfgtheory := HF;
            preset_hf_index();
          end
        else if Sys.argv.(!j) = "-mizar" then
          begin
            pfgtheory := Mizar;
            preset_mizar_index();
          end
        else if Sys.argv.(!j) = "-setmm" then
          begin
            pfgtheory := SetMM;
            preset_setmm_index();
          end
        else if Sys.argv.(!j) = "-hoas" then
          begin
            pfgtheory := HOAS;
            preset_hoas_index();
          end
	else if Sys.argv.(!j) = "-pfg" then
	  begin
	    pfgout := true;
	  end
	else if Sys.argv.(!j) = "-pfgsummary" then
	  begin
	    pfgsummary := true;
	  end
	else if Sys.argv.(!j) = "-pfgsummary2" then
	  begin
            pfgout := true;
	    pfgsummary2 := true;
	  end
	else if Sys.argv.(!j) = "-nopfglinks" then
	  begin
	    Syntax.set_show_pfglinks false;
	  end	    
        else if Sys.argv.(!j) = "-warnaboutreproven" then
          warnaboutreproven := true
        else if Sys.argv.(!j) = "-warnaboutleadingspaces" then
          warnaboutleadingspaces := true
	else if Sys.argv.(!j) = "-indout" then
	  begin
	    includingsigfile := false;
	    if !j < i-2 then
	      begin
		incr j;
		match !indoutfile with
		| Some _ -> raise (Failure("Cannot use -indout twice"))
		| None -> indoutfile := Some (Sys.argv.(!j))
	      end
	    else
	      raise (Failure("Expected -indout <indoutfilename>"))
	  end
	else if Sys.argv.(!j) = "-ind" then
	  begin
	    includingsigfile := false;
	    if !j < i-2 then
	      begin
		incr j;
		let c = open_in (Sys.argv.(!j)) in
		read_indexfile c;
		close_in c;
	      end
	    else
	      raise (Failure("Expected -ind <indexfilename>"))
	  end
	else if Sys.argv.(!j) = "-ownedout" then
	  begin
	    includingsigfile := false;
	    if !j < i-2 then
	      begin
		incr j;
		match !ownedoutfile with
		| Some _ -> raise (Failure("Cannot use -ownedout twice"))
		| None -> ownedoutfile := Some (Sys.argv.(!j))
	      end
	    else
	      raise (Failure("Expected -ownedout <ownedoutfilename>"))
	  end
	else if Sys.argv.(!j) = "-owned" then
	  begin
	    includingsigfile := false;
	    if !j < i-2 then
	      begin
		incr j;
		let c = open_in (Sys.argv.(!j)) in
		read_ownedfile c;
		close_in c;
	      end
	    else
	      raise (Failure("Expected -owned <ownedfilename>"))
	  end
	else if Sys.argv.(!j) = "-solves" then
	  begin
	    includingsigfile := false;
	    if !j < i-2 then
	      begin
		incr j;
		solvesproblemfile := Some (Sys.argv.(!j))
	      end
	    else
	      raise (Failure("Expected -solves <indexfilename>"))
	  end
	else if Sys.argv.(!j) = "-reportpfcomplexity" then
	  begin
	    includingsigfile := false;
	    reportpfcomplexity := true
	  end
	else if Sys.argv.(!j) = "-reporteachitem" then
	  begin
	    includingsigfile := false;
	    reporteachitem := true
	  end
	else if Sys.argv.(!j) = "-webout" then
	  begin
	    includingsigfile := false;
	    webout := true;
	  end
	else if Sys.argv.(!j) = "-ajax" then
	  begin
	    includingsigfile := false;
	    if !j < i-2 then
	      begin
		ajax := true;
		incr j;
		ajaxpffile := Sys.argv.(!j);
		verbosity := 0;
	      end
	    else
	      raise (Failure("Expected -ajax <pffile>"))
	  end
	else if Sys.argv.(!j) = "-sqltermout" then (*** this should only be used when -sqlout is already being used ***)
	  begin
	    includingsigfile := false;
	    sqltermout := true;
	  end
	else if Sys.argv.(!j) = "-presentationonly" then
	  begin
	    includingsigfile := false;
	    presentationonly := true;
	  end
	else if Sys.argv.(!j) = "-thmsasexercises" then
	  begin
	    verbosity := 0;
	    includingsigfile := false;
	    thmsasexercises := true;
	  end
	else if Sys.argv.(!j) = "-masl" then
	  begin
	    if !j < i-2 then
	      begin
		incr j;
		megaautosaltlimit := int_of_string (Sys.argv.(!j))
	      end
	    else
	      raise (Failure("Expected -masl <int>"))
	  end
	else if Sys.argv.(!j) = "-v" then
	  begin
	    if !j < i-2 then
	      begin
		incr j;
		verbosity := int_of_string (Sys.argv.(!j))
	      end
	    else
	      raise (Failure("Expected -v <verbositynumber>"))
	  end
	else if Sys.argv.(!j) = "-maxbottlenecksreport" then
	  begin
	    if !j < i-2 then
	      begin
		incr j;
		maxbottlenecksreport := int_of_string (Sys.argv.(!j))
	      end
	    else
	      raise (Failure("Expected -v <verbositynumber>"))
	  end
	else if Sys.argv.(!j) = "-explorerurl" then
	  begin
	    if !j < i-2 then
	      begin
		incr j;
		explorerurl := Sys.argv.(!j);
	      end
	    else
	      raise (Failure("Expected -v <verbositynumber>"))
	  end
	else if !includingsigfile then
	  let c = open_in (Sys.argv.(!j)) in
          begin
            match !sexprallsubgoals with
            | None -> mgcheck c
            | Some(seaspre,seasincl,i) ->
               let fn = Printf.sprintf "%s_incl_%d.lisp" seaspre i in
               let f = open_out fn in
               if not (seasincl = "") then Printf.fprintf f "(INCLUDE \"%s\")\n" seasincl;
               sexprallsubgoals_inclfile := Some(f);
               mgcheck c;
               close_out f;
               sexprallsubgoals := Some(seaspre,fn,i+1)
          end;
	  title := None;
	  authors := [];
	  includedsigfiles := Sys.argv.(!j)::!includedsigfiles
	else
	  raise (Failure("Cannot understand command line argument " ^ (Sys.argv.(!j))))
      done;
      includingsigfile := false;
      if !vampireabytargetstop && !vampireabytarget = None then
        raise (Failure("-vampireabytargetstop requires -vampireabytarget <lineno> <charno>"));
      if !vampireabyqualifying && !allowincompleteqed then
        raise (Failure("-vampireabyqualifying cannot be combined with -allowincompleteqed"));
      if !vampireabyqualifying && !vampireabytargetstop then
        raise (Failure("-vampireabyqualifying cannot be combined with -vampireabytargetstop"));
      if !vampireabyqualifying && !vampireabyproof <> "megalodon" then
        raise (Failure("-vampireabyqualifying requires -vampireabyproof megalodon"));
      if !vampireabyqualifying && !vampireabytimeout > 10 then
        raise (Failure("-vampireabyqualifying requires -vampireabytimeout <= 10"));
      if !vampireabyqualifying
         && Sys.getenv_opt "MEGALODON_CERT_ALLOW_TRANSITIONAL_PREPROCESS_KNOWN" = Some "1" then
        raise
          (Failure
             ("-vampireabyqualifying cannot be combined with "
              ^ "MEGALODON_CERT_ALLOW_TRANSITIONAL_PREPROCESS_KNOWN=1"));
      if !vampireabyqualifying
         && Sys.getenv_opt "MEGALODON_CERT_KEEP_QED_DELTA" = Some "1" then
        raise
          (Failure
             ("-vampireabyqualifying cannot be combined with "
              ^ "MEGALODON_CERT_KEEP_QED_DELTA=1"));
      let checkfile () =
        let c = open_in (Sys.argv.(i-1)) in
        current_input_file := Some (Sys.argv.(i-1));
        begin
          match !sexprallsubgoals with
          | None ->
	     if !preambleassig then includingsigfile := true;
	     mgcheck c
          | Some(seaspre,seasincl,i) ->
             let fn = Printf.sprintf "%s_incl_%d.lisp" seaspre i in
             let f = open_out fn in
             if not (seasincl = "") then Printf.fprintf f "(INCLUDE \"%s\")\n" seasincl;
             sexprallsubgoals_inclfile := Some(f);
	     if !preambleassig then includingsigfile := true;
             mgcheck c;
             close_out f
        end;
	close_in c;
        begin
          match !removepfs with
          | None -> ()
          | Some(outfn) ->
             pfposinfo := List.rev !pfposinfo;
             let infn = ref (Sys.argv.(i-1)) in
             let tmpname = ref false in
             if !infn = outfn then
               begin
                 tmpname := true;
                 let tmstmp = ref (int_of_float (Unix.time ())) in
                 try
                   while true do
                     let tmpfn = Printf.sprintf "%s.%d" !infn !tmstmp in
                     if Sys.file_exists tmpfn then
                       incr tmstmp
                     else
                       begin
                         Sys.rename !infn tmpfn;
                         infn := tmpfn;
                         raise Exit
                       end
                   done
                 with Exit -> ()
               end;
	     let c = open_in !infn in
             lineno := 1;
             charno := 0;
             let d = open_out outfn in
             let triggerlineno1 = ref 0 in
             let triggercharno1 = ref 0 in
             let triggerlineno2 = ref 0 in
             let triggercharno2 = ref 0 in
             let triggerlineno3 = ref 0 in
             let triggercharno3 = ref 0 in
             let removepfphase = ref 0 in
             let pop_pfposinfo () =
               match !pfposinfo with
               | (l1,c1,l2,c2,l3,c3)::r ->
                  triggerlineno1 := l1;
                  triggercharno1 := c1;
                  triggerlineno2 := l2;
                  triggercharno2 := c2;
                  triggerlineno3 := l3;
                  triggercharno3 := c3;
                  pfposinfo := r
               | [] -> removepfphase := 3
             in
             pop_pfposinfo ();
             try
               let skipuntilspace = ref false in
               let skipuntilendpf = ref false in
               let getchar () =
                 let ch = input_char c in
                 if ch = '\n' then
                   (incr lineno; charno := 0)
                 else
                   incr charno;
                 ch
               in
               let past_trigger triglineno trigcharno =
                 !lineno > triglineno || (!lineno = triglineno && !charno >= trigcharno)
               in
               while true do
                 let ch = getchar () in
                 if !skipuntilspace && ch = ' ' then skipuntilspace := false;
                 if !removepfphase = 0 && past_trigger !triggerlineno1 !triggercharno1 then
                   begin
                     removepfphase := 1;
                     if ch = '\n' then Printf.fprintf d "%c" ch;
                     (match !archivefile with Some(x) -> Printf.fprintf d "// Proof in %s\n" x | None -> ());
                     Printf.fprintf d "ProofArchived";
                     skipuntilspace := true;
                   end
                 else if !removepfphase = 1 && past_trigger !triggerlineno2 !triggercharno2 then
                   begin
                     removepfphase := 2;
                     skipuntilendpf := true;
                     incr countremovedpfs;
                   end
                 else if !removepfphase = 2 && past_trigger !triggerlineno3 !triggercharno3 then
                   begin
                     removepfphase := 0;
                     skipuntilendpf := false;
                     pop_pfposinfo ();
                   end;
                 if not !skipuntilspace && not !skipuntilendpf then
                   output_char d ch;
                 (*                 if !skipuntilendpf && ch = '\n' then (output_char d '/'; output_char d '/') *)
               done
             with
             | End_of_file ->
                close_in c;
                close_out d;
                if !tmpname then Sys.remove !infn
        end;
        if !pfgout then
          begin
            begin
              match !pfgtheory with
              | HF -> Printf.printf "Document 6ffc9680fbe00a58d70cdeb319f11205ed998131ce51bb96f16c7904faf74a3d\nBase set\n"
              | Egal -> Printf.printf "Document 29c988c5e6c620410ef4e61bcfcbe4213c77013974af40759d8b732c07d61967\nBase set\n"
              | Mizar -> Printf.printf "Document 5ab3df7b0b4ef20889de0517a318df8746940971ad9b2021e54c820eb9e74dce\nBase set\n"
              | HOAS -> Printf.printf "Document 513140056e2032628f48d11e221efe29892e9a03a661d3b691793524a5176ede\nBase syn\n"
              | SetMM -> Printf.printf "Document 85ecfdcf26657b94532af5af2393c6945cee05c4aabccb8a819f793a7dbc4acf\nBase set\n"
            end;
            List.iter
              (fun i ->
                match i with
                | PfgParam(xhv,x,agtp) ->
                   if not (pfg_prim_id_p xhv) then
                     begin
                       try
                         if !pfgsummary2 then
                           Printf.printf "Param:%s\n" xhv
                         else
                           let pfghv = Hashtbl.find pfgtmhh xhv in
                           Printf.printf "Param %s %s : %s\n" (Hash.hashval_hexstring pfghv) x (tp_pfg_str agtp);
                           Hashtbl.add pfgtmh xhv x
                       with Not_found ->
                         Printf.printf "%% ERROR: No pfg id for %s [%s] obj\n" x xhv
                     end
                | PfgDef(xhv,x,a,m) ->
                   begin
                     tm_pfg_decl pfgdelta pfgtmph m;
                     if !pfgsummary2 then
                       Printf.printf "Def:%s\n" xhv
                     else
                       begin
                         Printf.printf "Def %s : %s\n := %s\n" x (tp_pfg_str a) (tm_pfg_str m);
                         Hashtbl.add pfgtmh xhv x
                       end
                   end
                | PfgKnown(xhv,x,p) ->
                   begin
                     tm_pfg_decl pfgdelta pfgtmph p;
                     if !pfgsummary2 then
                       Printf.printf "Known:%s\n" xhv
                     else
                       begin
                         Printf.printf "Known %s : %s\n" x (tm_pfg_str p);
	                 Hashtbl.add pfgknh xhv x;
                         Hashtbl.add pfgknph xhv p;
                       end
                   end
                | PfgConj(xhv,x,p) ->
                   begin
                     if !pfgsummary2 then
                       Printf.printf "Conj:%s\n" xhv
                     else
                       begin
                         tm_pfg_decl pfgdelta pfgtmph p;
                         Printf.printf "Conj %s : %s\n" x (tm_pfg_str p);
	                 Hashtbl.add pfgknh xhv x;
                       end
                   end
                | PfgThm(xhv,x,p,d) ->
                   begin
                     tm_pfg_decl pfgdelta pfgtmph p;
                     pf_pfg_decl pfgdelta pfgtmph pfgknph d;
                     let d1 = if !optimizepf1 then optimize_pf_1 d else d in
                     let d2 = if !optimizepf2 then optimize_pf_2 sigdelta sigtmof d1 !optimizepf2tc !optimizepf2pc else d1 in
                     if !pfgsummary2 then
                       Printf.printf "Thm:%s\n" xhv
                     else
                       begin
                         Printf.printf "Thm %s : %s\n := %s\n" x (tm_pfg_str p) (pf_pfg_str d2);
	                 Hashtbl.add pfgknh xhv x;
                         Hashtbl.add pfgknph xhv p;
                       end
                   end)
              (List.rev !pfgmain)
          end;
	begin
	  match !sigoutfile with
	  | Some(soc) -> close_out soc
	  | None -> ()
	end;
	begin
	  match !inchan with
	  | Some(c) -> close_in c
	  | None -> ()
	end;
      in
      let check_vampirecertv1_if_requested () =
        match !vampirecertv1 with
        | None -> ()
        | Some fn -> check_vampire_cert_v1_file fn
      in
      let check_main_file () =
        match !solvesproblemfile with
	| None -> checkfile ()
	| Some probf ->
	    let p = open_in probf in
	    let c = open_in (Sys.argv.(i-1)) in
	    mgchecksolves p c;
	    close_in c;
	    close_in p;
	    if !verbosity > 1 then (Printf.printf "%s completely solves %s\n" Sys.argv.(i-1) probf; flush stdout)
      in
      if !vampirecertv1sourcecontext || !vampirecertv1sourcecontextstrict then
        begin
          check_main_file ();
          check_vampire_live_prop_choice_if_requested ();
          check_vampirecertv1_if_requested ()
        end
      else if !vampirechecklivepropchoice then
        begin
          check_main_file ();
          check_vampire_live_prop_choice_if_requested ();
          check_vampirecertv1_if_requested ()
        end
      else
        begin
          check_vampirecertv1_if_requested ();
          check_main_file ()
        end
    end;
  begin
    match !reportbushydeps with
    | Some(ch) -> close_out ch
    | None -> ()
  end;
  finalize_megawiki_theorem false;
  begin
    match !html with
    | Some hc ->
       Printf.fprintf hc "</body></html>\n";
       close_out hc
    | None -> ()
  end;
  begin
    match !latex with
    | Some hc ->
	close_out hc
    | None -> ()
  end;
  if !webout then
    begin
      Printf.printf "<div class='documentcorrect'>The document in its current form is correct.</div>\n";
    end;
  begin
    match !ownedoutfile with
    | Some(f) ->
       let c = open_out f in
       Hashtbl.iter (fun h _ -> Printf.fprintf c "Obj fake fake %s\n" (Hash.hashval_hexstring h)) ownedobj;
       Hashtbl.iter (fun h _ -> Printf.fprintf c "Prop fake fake %s\n" (Hash.hashval_hexstring h)) ownedprop;
       close_out c
    | None ->
       ()
  end;
  if (!reportids) then
    begin
      match !indoutfile with
      | Some(f) ->
	  let c = open_out f in
	  Hashtbl.iter (fun h a -> Printf.fprintf c "\"%s\" %s.\n" h (tp_to_str a)) indextms;
	  Hashtbl.iter (fun x _ -> Printf.fprintf c "Known \"%s\".\n" x) indexknowns;
	  close_out c
      | None ->
	  ()
    end;
  Printf.printf "Everything looks good.\n";
  if !countremovedpfs > 0 then
    Printf.printf "%d completed proof%s been removed for efficiency.\n" !countremovedpfs (if !countremovedpfs = 1 then " has" else "s have");
  let admittedthmsrecdeps : (string,string list) Hashtbl.t = Hashtbl.create 10 in
  let rec union xl yl =
    match xl with
    | [] -> yl
    | x::xr -> if List.mem x yl then union xr yl else union xr (x::yl)
  in
  let rec recdeps xl r =
    match xl with
    | [] -> r
    | x::xr ->
       if List.mem x r then
         recdeps xr r
       else
         try
           let r2 = Hashtbl.find admittedthmsrecdeps x in
           recdeps xr (x::union r2 r)
         with Not_found ->
           let dl = Hashtbl.find_all admittedthmsdeps x in
           let r2 = recdeps dl [] in
           Hashtbl.replace admittedthmsrecdeps x r2;
           recdeps xr (x::union r2 r)
  in
  let topbottlenecks = ref [] in
  let rec filter_len n l =
    if n <= 0 then
      []
    else
      match l with
      | z::lr -> z::filter_len (n-1) lr
      | [] -> []
  in
  let rec insert_sort_and_filter n (x,rl) l =
    if n <= 0 then
      []
    else
      match l with
      | (_,yrl)::lr when rl > yrl -> (x,rl)::filter_len (n-1) l
      | (y,yrl)::lr -> (y,yrl)::insert_sort_and_filter (n-1) (x,rl) lr
      | [] -> [(x,rl)]
  in
  Hashtbl.iter
    (fun x () ->
      try
        let r = Hashtbl.find admittedthmsrecdeps x in
        topbottlenecks := insert_sort_and_filter !maxbottlenecksreport (x,List.length r) !topbottlenecks
      with
      | Not_found ->
         let r = recdeps (Hashtbl.find_all admittedthmsdeps x) [] in
         Hashtbl.replace admittedthmsrecdeps x r;
         topbottlenecks := insert_sort_and_filter !maxbottlenecksreport (x,List.length r) !topbottlenecks)
    admittedthms;
  let bottlenecksl = List.length !topbottlenecks in
  if bottlenecksl > 0 then
    begin
      Printf.printf "The top unproven theorem%s" (if bottlenecksl = 1 then " is\n" else "s are\n");
      List.iter (fun (x,rl) -> Printf.printf "%s which is used in %d future proof%s so far.\n" x rl (if rl = 1 then "" else "s")) !topbottlenecks
    end;
;;
