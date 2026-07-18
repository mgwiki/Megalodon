(* File: lexer.mll *)
(* Author: Chad E Brown *)
(* Created: September 2011 (Scavanaged from holitmus; Changed to Coq syntax) *)
(* Copyright (c) 2026 AI4REASON *)

{
open Parser        (* The type token is defined in parser.mli *)
exception Eof

let skip_next_proof = ref false
let proof_checking_enabled = ref true

let request_proof_skip () = skip_next_proof := true
let reset_proof_pragmas () =
  skip_next_proof := false;
  proof_checking_enabled := true
let proofs_enabled () = !proof_checking_enabled

let process_line_comment lxm =
  let n = String.length lxm in
  let last = if n > 0 && lxm.[n-1] = '\n' then n-1 else n in
  let body =
    if last <= 2 then ""
    else String.trim (String.sub lxm 2 (last - 2))
  in
  if body = "$P-" then proof_checking_enabled := false
  else if body = "$P+" then proof_checking_enabled := true
}
rule normal_token = parse
| [' ' '\t' '\r']     { incr charno; normal_token lexbuf }     (* skip white space *)
| ['\n']         { incr lineno; charno := 0; normal_token lexbuf }     (* skip white space *)
| "//" [^'\n']* ['\n'] as lxm { process_line_comment lxm; update_pos lxm; normal_token lexbuf } (* skip one line comment *)
| "//" [^'\n']* as lxm { process_line_comment lxm; update_pos lxm; normal_token lexbuf }
| ['(']['*']['*']['*']*[^'*']*['*']+[')'] as lxm { update_pos lxm; normal_token lexbuf }     (* skip comments *)
| "(*" as lxm          { update_char_pos lxm; OPENCOM }
| "*)" as lxm          { update_char_pos lxm; CLOSECOM }
| ['"'][^'"']*['"'] as lxm           { update_char_pos lxm; STRING(String.sub lxm 1 (String.length lxm - 2)) }
| ['?'][^'?']*['?'] as lxm           { update_char_pos lxm; QUESTIONSTRING(String.sub lxm 1 (String.length lxm - 2)) }
| '('           { incr charno; LPAREN }
| ')'           { incr charno; RPAREN }
| '['           { incr charno; LBRACK }
| ']'           { incr charno; RBRACK }
| '{'           { incr charno; LCBRACE }
| '}'           { incr charno; RCBRACE }
| '|'           { incr charno; VBAR }
| '.'           { incr charno; DOT }
| ':'           { incr charno; COLON }
| '\\'          { incr charno; BACKSLASH }
| "="           { incr charno; NAM("=") }
| "<>" as lxm           { update_char_pos lxm; NAM(lxm) }
| ":e" as lxm           { update_char_pos lxm; MEM }
| "/:e" as lxm           { update_char_pos lxm; NAM(lxm) }
| "c=" as lxm           { update_char_pos lxm; SUBEQ }
| "/c=" as lxm           { update_char_pos lxm; NAM(lxm) }
| '~'           { incr charno; NAM("~") }
| '+'           { incr charno; NAM("+") }
| '*'           { incr charno; NAM("*") }
| '^'          { incr charno; NAM("^") }
| '-'           { incr charno; NAM("-") }
| ';'            { incr charno; SEMICOLON }
| ','            { incr charno; COMMA }
| '!'                     { incr charno; NAM("!") }
| "at" as lxm          { update_char_pos lxm; AT }
| "if" as lxm          { update_char_pos lxm; IF }
| "then" as lxm        { update_char_pos lxm; THEN }
| "else" as lxm        { update_char_pos lxm; ELSE }
| "let" as lxm         { update_char_pos lxm; LET }
| "assume" as lxm         { update_char_pos lxm; ASSUME }
| "apply" as lxm         { update_char_pos lxm; APPLY }
| "claim" as lxm         { update_char_pos lxm; CLAIM }
| "prove" as lxm         { update_char_pos lxm; PROVE }
| ":=" as lxm          { update_char_pos lxm; DEQ }
| "in" as lxm         { update_char_pos lxm; IN }
| "=>" as lxm          { update_char_pos lxm; DARR }
| "exists!" as lxm           { update_char_pos lxm; NAM("exists!") }
| "some" as lxm           { update_char_pos lxm; NAM("some") }
| "/\\" as lxm         { update_char_pos lxm; NAM(lxm) }
| "\\/" as lxm           { update_char_pos lxm; NAM(lxm) }
| "/\\_" as lxm         { update_char_pos lxm; NAM(lxm) }
| "\\/_" as lxm           { update_char_pos lxm; NAM(lxm) }
| "<->" as lxm           { update_char_pos lxm; NAM(lxm) }
| "<=>" as lxm           { update_char_pos lxm; NAM(lxm) }
| "fun" as lxm         { update_char_pos lxm; NAM(lxm) }
| "->" as lxm          { update_char_pos lxm; NAM(lxm) }
| "<-" as lxm          { update_char_pos lxm; NAM(lxm) }
| '>'          { incr charno; NAM(">") }
| '<'          { incr charno; NAM("<") }
| ">=" as lxm          { update_char_pos lxm; NAM(lxm) }
| "<=" as lxm          { update_char_pos lxm; NAM(lxm) }
| "'"          { incr charno; NAM("'") }
| "Section" as lxm         { warn_about_leading_spaces lxm; update_char_pos lxm; SECTION }
| "End" as lxm         { warn_about_leading_spaces lxm; update_char_pos lxm; END }
| "Let" as lxm         { warn_about_leading_spaces lxm; update_char_pos lxm; LETDEC }
| "Variable" as lxm         { warn_about_leading_spaces lxm; update_char_pos lxm; VAR }
| "Hypothesis" as lxm         { warn_about_leading_spaces lxm; update_char_pos lxm; HYP }
| "Parameter" as lxm       { update_char_pos lxm; PARAM }
| "Axiom" as lxm       { warn_about_leading_spaces lxm; update_char_pos lxm; AXIOM }
| "ProofArchived" as lxm       { warn_about_leading_spaces lxm; update_char_pos lxm; AXIOM }
| "Lemma" as lxm       { warn_about_leading_spaces lxm; update_char_pos_thm lxm; THEOREM(lxm) }
| "Theorem" as lxm       { warn_about_leading_spaces lxm; update_char_pos_thm lxm; THEOREM(lxm) }
| "Example" as lxm       { warn_about_leading_spaces lxm; update_char_pos_thm lxm; THEOREM(lxm) }
| "Fact" as lxm       { warn_about_leading_spaces lxm; update_char_pos_thm lxm; THEOREM(lxm) }
| "Remark" as lxm       { warn_about_leading_spaces lxm; update_char_pos_thm lxm; THEOREM(lxm) }
| "Corollary" as lxm       { warn_about_leading_spaces lxm; update_char_pos_thm lxm; THEOREM(lxm) }
| "Proposition" as lxm       { warn_about_leading_spaces lxm; update_char_pos_thm lxm; THEOREM(lxm) }
| "Property" as lxm       { warn_about_leading_spaces lxm; update_char_pos_thm lxm; THEOREM(lxm) }
| "exact" as lxm       { update_char_pos lxm; EXACT }
| "Qed" as lxm       { warn_about_leading_spaces lxm; update_char_pos lxm; QED }
| "Axiom" as lxm       { warn_about_leading_spaces lxm; update_char_pos lxm; AXIOM }
| "Conjecture" as lxm       { warn_about_leading_spaces lxm; update_char_pos lxm; CONJECTURE }
| "Definition" as lxm         { warn_about_leading_spaces lxm; update_char_pos lxm; DEF }
| "Infix" as lxm         { warn_about_leading_spaces lxm; update_char_pos lxm; INFIX }
| "Postfix" as lxm         { warn_about_leading_spaces lxm; update_char_pos lxm; POSTFIX }
| "Prefix" as lxm         { warn_about_leading_spaces lxm; update_char_pos lxm; PREFIX }
| "Binder" as lxm         { warn_about_leading_spaces lxm; update_char_pos lxm; BINDER }
| "Binder+" as lxm         { warn_about_leading_spaces lxm; update_char_pos lxm; BINDERPLUS }
| "Notation" as lxm         { warn_about_leading_spaces lxm; update_char_pos lxm; NOTATION }
| "Unicode" as lxm         { update_char_pos lxm; UNICODE }
| "Subscript" as lxm       { update_char_pos lxm; SUBSCRIPT }
| "Superscript" as lxm       { update_char_pos lxm; SUPERSCRIPT }
| "ShowProofTerms" as lxm         { update_char_pos lxm; SPECCOMM(lxm) }
| "HideProofTerms" as lxm         { update_char_pos lxm; SPECCOMM(lxm) }
| "Verbose" as lxm { update_char_pos lxm; SPECCOMM(lxm) }
| "Salt" as lxm { update_char_pos lxm; SALT }
| "Opaque" as lxm { update_char_pos lxm; OPAQUE }
| "Transparent" as lxm { update_char_pos lxm; TRANSPARENT }
| "Treasure" as lxm { update_char_pos lxm; TREASURE }
| "Title" as lxm { update_char_pos lxm; TITLE }
| "Author" as lxm { update_char_pos lxm; AUTHOR }
| "Admitted" as lxm { warn_about_leading_spaces lxm; update_char_pos lxm; ADMITTED }
| "admit" as lxm { update_char_pos lxm; ADMIT }
| "aby" as lxm { update_char_pos lxm; ABY }
| "TEXT" as lxm { update_char_pos lxm; TEXT }
| ['\'']['_''+''-''*''^''~''=''<''>''/''\\']*['\''] as lxm { update_char_pos lxm; NAM(lxm) }
| [':']['_''+''-''*''^''~''=''<''>''/''\\']*[':'] as lxm { update_char_pos lxm; NAM(lxm) }
| ['0'-'9']+ as lxm { update_char_pos lxm; num_of_string lxm }
| ['0'-'9']+['e''E']['0'-'9']+ as lxm { update_char_pos lxm; num_of_string lxm }
| ['-']['0'-'9']+ as lxm { update_char_pos lxm; num_of_string lxm }
| ['-']['0'-'9']+['e''E']['0'-'9']+ as lxm { update_char_pos lxm; num_of_string lxm }
| ['0'-'9']+['.']['0'-'9']+ as lxm { update_char_pos lxm; num_of_string lxm }
| ['0'-'9']+['.']['0'-'9']+['e''E']['0'-'9']+ as lxm { update_char_pos lxm; num_of_string lxm }
| ['-']['0'-'9']+['.']['0'-'9']+ as lxm { update_char_pos lxm; num_of_string lxm }
| ['-']['0'-'9']+['.']['0'-'9']+['e''E']['0'-'9']+ as lxm { update_char_pos lxm; num_of_string lxm }
| ['_''a'-'z''A'-'Z']['_''\'''0'-'9''a'-'z''A'-'Z']* as lxm { update_char_pos lxm; NAM(lxm) }
| eof            { raise Eof }


and skip_proof = parse
| [' ' '\t' '\r']+ as lxm { update_char_pos lxm; skip_proof lexbuf }
| ['\n'] { incr lineno; charno := 0; skip_proof lexbuf }
| "//" [^'\n']* ['\n'] as lxm { process_line_comment lxm; update_pos lxm; skip_proof lexbuf }
| "//" [^'\n']* as lxm { process_line_comment lxm; update_pos lxm; skip_proof lexbuf }
| "(*" as lxm { update_char_pos lxm; skip_block_comment 1 lexbuf; skip_proof lexbuf }
| ['"'] { incr charno; skip_string lexbuf; skip_proof lexbuf }
| ['?'] { incr charno; skip_qstring lexbuf; skip_proof lexbuf }
| ['_''a'-'z''A'-'Z']['_''\'''0'-'9''a'-'z''A'-'Z']* as lxm
    {
      update_char_pos lxm;
      if lxm = "Qed" || lxm = "Admitted" then ADMITTED
      else skip_proof lexbuf
    }
| [^' ''\t''\r''\n''/''(''"''?''_''a'-'z''A'-'Z']+ as lxm
    { update_char_pos lxm; skip_proof lexbuf }
| eof { raise (Failure("Reached end of file while skipping a proof; expected Qed. or Admitted.")) }
| _ as ch
    {
      if ch = '\n' then (incr lineno; charno := 0) else incr charno;
      skip_proof lexbuf
    }

and skip_string = parse
| ['"'] { incr charno }
| ['\n'] { incr lineno; charno := 0; skip_string lexbuf }
| eof { raise (Failure("Reached end of file inside a string while skipping a proof")) }
| _ { incr charno; skip_string lexbuf }

and skip_qstring = parse
| ['?'] { incr charno }
| ['\n'] { incr lineno; charno := 0; skip_qstring lexbuf }
| eof { raise (Failure("Reached end of file inside a question string while skipping a proof")) }
| _ { incr charno; skip_qstring lexbuf }

and skip_block_comment depth = parse
| "(*" as lxm { update_char_pos lxm; skip_block_comment (depth + 1) lexbuf }
| "*)" as lxm
    {
      update_char_pos lxm;
      if depth > 1 then skip_block_comment (depth - 1) lexbuf
    }
| ['\n'] { incr lineno; charno := 0; skip_block_comment depth lexbuf }
| eof { raise (Failure("Reached end of file inside a comment while skipping a proof")) }
| _ { incr charno; skip_block_comment depth lexbuf }

{
let token lexbuf =
  if !skip_next_proof then
    begin
      skip_next_proof := false;
      skip_proof lexbuf
    end
  else
    normal_token lexbuf
}
