(*** Native strict Vampire/Megalodon certificate v1 importer. ***)

open Syntax

type sexpr =
  | Atom of string
  | Str of string
  | List of sexpr list

exception Error of string

type source =
  | SourceAxiom of string
  | SourceNegatedConjecture of string
  | SourceDefinition of string
  | SourceSetReflexivity of string

type literal =
  | Pos of tm
  | Neg of tm

type clause = literal list

type step =
  | Input of string * source * clause
  | Resolve of string * string * string * int * int * clause
  | Contradiction of string * string

type certificate = {
  problem : string option;
  steps : step list;
}

let error msg = raise (Error msg)

let is_space = function
  | ' ' | '\n' | '\r' | '\t' -> true
  | _ -> false

let is_delim = function
  | '(' | ')' | '"' -> true
  | c -> is_space c

let parse_sexpr text =
  let len = String.length text in
  let rec skip i =
    if i < len && is_space text.[i] then skip (i + 1) else i
  in
  let rec parse_string buf i =
    if i >= len then error "unterminated string";
    match text.[i] with
    | '"' -> (Str (Buffer.contents buf), i + 1)
    | '\\' when i + 1 < len ->
        let c =
          match text.[i + 1] with
          | 'n' -> '\n'
          | 'r' -> '\r'
          | 't' -> '\t'
          | c -> c
        in
        Buffer.add_char buf c;
        parse_string buf (i + 2)
    | c ->
        Buffer.add_char buf c;
        parse_string buf (i + 1)
  and parse_atom start i =
    if i >= len || is_delim text.[i] then
      if i = start then error "expected atom" else (Atom (String.sub text start (i - start)), i)
    else parse_atom start (i + 1)
  and parse_list acc i =
    let i = skip i in
    if i >= len then error "unterminated list";
    if text.[i] = ')' then (List (List.rev acc), i + 1)
    else
      let item, j = parse_one i in
      parse_list (item :: acc) j
  and parse_one i =
    let i = skip i in
    if i >= len then error "expected S-expression";
    match text.[i] with
    | '(' -> parse_list [] (i + 1)
    | ')' -> error "unexpected ')'"
    | '"' -> parse_string (Buffer.create 16) (i + 1)
    | _ -> parse_atom i i
  in
  let parsed, i = parse_one 0 in
  if skip i <> len then error "trailing input after S-expression";
  parsed

let atom = function
  | Atom x -> x
  | Str x -> x
  | List _ -> error "expected atom"

let int_atom sexpr =
  try int_of_string (atom sexpr) with Failure _ -> error "expected integer"

let rec parse_tp = function
  | List [Atom "PROP"] -> Prop
  | List [Atom "SET"] -> Set
  | List [Atom "TPVAR"; n] -> TpVar (int_atom n)
  | List [Atom "AR"; a; b] -> Ar (parse_tp a, parse_tp b)
  | _ -> error "expected Megalodon type S-expression"

let rec parse_tm = function
  | List [Atom "DB"; n] -> DB (int_atom n)
  | List [Atom "TMH"; h] -> TmH (atom h)
  | List [Atom "PRIM"; n] -> Prim (int_atom n)
  | List [Atom "TPAP"; m; a] -> TpAp (parse_tm m, parse_tp a)
  | List [Atom "AP"; m; n] -> Ap (parse_tm m, parse_tm n)
  | List [Atom "LAM"; a; m] -> Lam (parse_tp a, parse_tm m)
  | List [Atom "IMP"; m; n] -> Imp (parse_tm m, parse_tm n)
  | List [Atom "ALL"; a; m] -> All (parse_tp a, parse_tm m)
  | _ -> error "expected Megalodon term S-expression"

let parse_source = function
  | List [Atom "source"; Atom "axiom"; name] -> SourceAxiom (atom name)
  | List [Atom "source"; Atom "negated_conjecture"; name] -> SourceNegatedConjecture (atom name)
  | List [Atom "source"; Atom "definition"; name] -> SourceDefinition (atom name)
  | List [Atom "source"; Atom "set_reflexivity"; name] -> SourceSetReflexivity (atom name)
  | List (Atom "source" :: Atom bad :: _) when String.length bad >= 8 && String.sub bad 0 8 = "vampire_" ->
      error ("strict certificate v1 rejects source " ^ bad)
  | List (Atom "source" :: _) -> error "unsupported certificate source"
  | _ -> error "expected certificate source"

let parse_literal = function
  | List [Atom "pos"; tm] -> Pos (parse_tm tm)
  | List [Atom "neg"; tm] -> Neg (parse_tm tm)
  | _ -> error "expected clause literal"

let parse_clause = function
  | List (Atom "clause" :: literals) -> List.map parse_literal literals
  | _ -> error "expected clause"

let parse_parents = function
  | List [Atom "parents"; a; b] -> (atom a, atom b)
  | _ -> error "expected two parents"

let parse_pivot = function
  | List [Atom "pivot"; a; b] -> (int_atom a, int_atom b)
  | _ -> error "expected pivot"

let parse_result = function
  | List [Atom "result"; clause] -> parse_clause clause
  | _ -> error "expected result clause"

let parse_step = function
  | List [Atom "input"; id; source; clause] ->
      Input (atom id, parse_source source, parse_clause clause)
  | List [Atom "resolve"; id; parents; pivot; result] ->
      let a, b = parse_parents parents in
      let i, j = parse_pivot pivot in
      Resolve (atom id, a, b, i, j, parse_result result)
  | List [Atom "contradiction"; id; parent] ->
      Contradiction (atom id, atom parent)
  | List (Atom rule :: _) ->
      error ("strict certificate v1 importer does not support rule " ^ rule)
  | _ -> error "expected certificate step"

let step_id = function
  | Input (id, _, _) -> id
  | Resolve (id, _, _, _, _, _) -> id
  | Contradiction (id, _) -> id

let check_duplicate_ids steps =
  let seen = Hashtbl.create 17 in
  List.iter
    (fun step ->
      let id = step_id step in
      if Hashtbl.mem seen id then error ("duplicate certificate step id " ^ id);
      Hashtbl.add seen id ())
    steps

let parse_problem = function
  | List [Atom "problem"; name] -> Some (atom name)
  | _ -> None

let parse_certificate text =
  match parse_sexpr text with
  | List (Atom "certificate" :: Atom "vampire-megalodon" :: Atom "1" :: rest) ->
      let problem, step_forms =
        match rest with
        | first :: tail ->
            begin match parse_problem first with
            | Some _ as problem -> (problem, tail)
            | None -> (None, rest)
            end
        | [] -> (None, [])
      in
      let steps = List.map parse_step step_forms in
      check_duplicate_ids steps;
      { problem; steps }
  | _ -> error "expected (certificate vampire-megalodon 1 ...)"
