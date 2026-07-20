#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/kernel_elab_unit.XXXXXX")"}
ln -sfn "$WORK_DIR" "$TMPDIR/latest_kernel_elab_unit"

if [[ ! -x "$ROOT/bin/megalodon" ]]; then
  (cd "$ROOT" && TMPDIR="$TMPDIR" ./makeopt)
fi

cat >"$WORK_DIR/test_kernel_elab.ml" <<'EOF_OCAML'
open Syntax

let expect_equal label expected actual =
  if expected <> actual then begin
    prerr_endline ("kernel_elab unit failure: " ^ label);
    exit 1
  end

let expect_bool label actual =
  if not actual then begin
    prerr_endline ("kernel_elab unit failure: " ^ label);
    exit 1
  end

let expect_error label f =
  try
    f ();
    prerr_endline ("kernel_elab unit failure: " ^ label);
    exit 1
  with
  | Vampire_kernel_check.Error _ -> ()
  | Vampire_kernel_elab.Error _ -> ()

let () =
  let choice_witness, choice_proof =
    Vampire_kernel_elab.skolem_choice_witness_proof
      ~choice_theorem:"choice_prop"
      ~eps_symbol:"eps"
      ~witness_type:Prop
      ~predicate:(Lam (Prop, Ap (DB 0, TmH "a")))
      (Hyp 0)
  in
  expect_equal
    "skolem_choice_witness_proof should build the epsilon witness"
    (Ap (TmH "eps", Lam (Prop, Ap (DB 0, TmH "a"))))
    choice_witness;
  expect_equal
    "skolem_choice_witness_proof should apply the choice theorem to an exists proof"
    (PPfAp
       (PTmAp (Known "choice_prop", Lam (Prop, Ap (DB 0, TmH "a"))),
        Hyp 0))
    choice_proof;
  expect_error
    "skolem_choice_witness_proof should reject predicate type mismatches"
    (fun () ->
       ignore
         (Vampire_kernel_elab.skolem_choice_witness_proof
            ~choice_theorem:"choice_prop"
            ~eps_symbol:"eps"
            ~witness_type:Set
            ~predicate:(Lam (Prop, DB 0))
            (Hyp 0)));
  let exists_map =
    Vampire_kernel_elab.church_exists_map_proof
      ~witness_type:Prop
      ~source_body:(Ap (TmH "P", DB 0))
      ~target_body:(Ap (TmH "Q", DB 0))
      ~pointwise_proof:(Known "PQ")
      (Hyp 0)
  in
  expect_equal
    "church_exists_map_proof should map Church-encoded existential witnesses"
    (TLam
       (Prop,
        PLam
          (All (Prop, Imp (Ap (TmH "Q", DB 0), DB 1)),
           PPfAp
             (PTmAp (pfshift 0 1 (pftmshift 0 1 (Hyp 0)), DB 0),
              TLam
                (Prop,
                 PLam
                   (Ap (TmH "P", DB 0),
                    PPfAp
                      (PTmAp (Hyp 1, DB 0),
                       PPfAp
                         (PTmAp
                            (pftmshift 0 2 (pfshift 0 2 (Known "PQ")),
                            DB 0),
                          Hyp 0))))))))
    exists_map;
  expect_equal
    "church_exists_elim_proof should apply a Church-encoded existential to a target and continuation"
    (PPfAp (PTmAp (Hyp 0, TmH "target"), Known "case"))
    (Vampire_kernel_elab.church_exists_elim_proof
       ~target_prop:(TmH "target")
       ~continuation:(Known "case")
       (Hyp 0));
  let inner_choice = Ap (TmH "eps", TmH "inner") in
  let outer_after_inner = Ap (TmH "eps", TmH "s0") in
  let outer_before_inner = Ap (TmH "eps", inner_choice) in
  let proof = PTmAp (Known "k", outer_before_inner) in
  let rewritten =
    Vampire_kernel_elab.replace_exact_terms_in_proof
      ~normalize:(fun tm -> tm)
      [inner_choice, TmH "s0"; outer_after_inner, TmH "s1"]
      proof
  in
  expect_equal
    "nested term replacement should revisit parent after rewriting children"
    (PTmAp (Known "k", TmH "s1"))
    rewritten;
  let outer_first_rewritten =
    Vampire_kernel_elab.replace_exact_terms_in_proof
      ~normalize:(fun tm -> tm)
      [inner_choice, TmH "s0"; outer_before_inner, TmH "s1"]
      proof
  in
  expect_equal
    "outer exact replacement should fire before child rewrites change the match"
    (PTmAp (Known "k", TmH "s1"))
    outer_first_rewritten;
  let lambda_proof = PLam (outer_before_inner, Hyp 0) in
  let lambda_rewritten =
    Vampire_kernel_elab.replace_exact_terms_in_proof
      ~normalize:(fun tm -> tm)
      [inner_choice, TmH "s0"; outer_after_inner, TmH "s1"]
      lambda_proof
  in
  expect_equal
    "nested replacement should also rewrite proof propositions"
    (PLam (TmH "s1", Hyp 0))
    lambda_rewritten;
  let choice_symbols = ["eps"] in
  expect_bool
    "proof_contains_term_symbol should find witness symbols"
    (Vampire_kernel_elab.proof_contains_term_symbol choice_symbols proof);
  expect_bool
    "proof_contains_exact_term should find normalized exact witness terms"
    (Vampire_kernel_elab.proof_contains_exact_term
       ~normalize:(fun tm -> tm)
       outer_before_inner
       proof);
  expect_equal
    "first_enclosing_term_with_symbol should report the enclosing application"
    (Some ("root.term.left", outer_before_inner))
    (Vampire_kernel_elab.first_enclosing_term_with_symbol choice_symbols proof);
  expect_equal
    "enclosing_terms_with_symbol should collect normalized unique enclosing terms"
    [inner_choice; outer_before_inner]
    (Vampire_kernel_elab.enclosing_terms_with_symbol
       ~normalize:(fun tm -> tm)
       choice_symbols
       proof);
  let binder_witness = Ap (TmH "eps", DB 0) in
  let binder_proof = TLam (Prop, PTmAp (Known "k", binder_witness)) in
  expect_equal
    "enclosing_terms_with_symbol_depth should track term binders"
    [1, binder_witness]
    (Vampire_kernel_elab.enclosing_terms_with_symbol_depth
       ~normalize:(fun tm -> tm)
       choice_symbols
       binder_proof);
  let free_witness = Ap (TmH "eps", DB 0) in
  let shifted_binder_proof =
    TLam (Prop, PTmAp (Known "k", Ap (TmH "eps", DB 1)))
  in
  expect_bool
    "proof_contains_exact_term should shift needles under term binders"
    (Vampire_kernel_elab.proof_contains_exact_term
       ~normalize:(fun tm -> tm)
       free_witness
       shifted_binder_proof);
  expect_equal
    "registered_witness_term_replacements should map exact witnesses to introduced symbols"
    [outer_before_inner, TmH "#s0"]
    (Vampire_kernel_elab.registered_witness_term_replacements
       ~normalize:(fun tm -> tm)
       ~witness_symbols:choice_symbols
       ["#s0", outer_before_inner]
       proof);
  expect_equal
    "registered_witness_term_replacements should not guess from symbol-only matches"
    []
    (Vampire_kernel_elab.registered_witness_term_replacements
       ~normalize:(fun tm -> tm)
       ~witness_symbols:choice_symbols
       ["#s1", Ap (TmH "eps", TmH "other")]
       proof);
  expect_equal
    "contract_backed_branch_choice_term_replacements should reject binder-dependent local templates"
    []
    (Vampire_kernel_elab.contract_backed_branch_choice_term_replacements
       ~normalize:(fun tm -> tm)
       ~choice_symbols:choice_symbols
       ~replacement_names:["#s1"]
       ~definition:(TmH "def1")
       binder_proof);
  let closed_binder_witness = Ap (TmH "eps", TmH "closed") in
  let closed_binder_proof =
    TLam (Prop, PTmAp (Known "k", closed_binder_witness))
  in
  expect_equal
    "contract_backed_branch_choice_term_replacements should collect liftable scoped local templates"
    [("#s1", closed_binder_witness, TmH "def1", closed_binder_witness)]
    (Vampire_kernel_elab.contract_backed_branch_choice_term_replacements
       ~normalize:(fun tm -> tm)
       ~choice_symbols:choice_symbols
       ~replacement_names:["#s1"]
       ~definition:(TmH "def1")
       closed_binder_proof);
  let transports =
    Vampire_kernel_elab.contract_backed_skolem_witness_transports
      ~normalize:(fun tm -> tm)
      ~choice_symbols:choice_symbols
      ~replacement_names:["#s1"]
      ~definition:(TmH "def1")
      closed_binder_proof
  in
  expect_equal
    "contract_backed_skolem_witness_transports should expose a typed transport record"
    [
      {
        Vampire_kernel_elab.skolem_transport_name = "#s1";
        skolem_transport_choice_occurrence = closed_binder_witness;
        skolem_transport_definition = TmH "def1";
        skolem_transport_local_template = closed_binder_witness;
      }
    ]
    transports;
  expect_equal
    "skolem_witness_transport_symbol_replacements should preserve legacy tuple shape"
    [("#s1", closed_binder_witness, TmH "def1", closed_binder_witness)]
    (Vampire_kernel_elab.skolem_witness_transport_symbol_replacements
       transports);
  expect_equal
    "skolem_witness_transport_term_replacements should rewrite directly to the backed definition"
    [closed_binder_witness, TmH "def1"]
    (Vampire_kernel_elab.skolem_witness_transport_term_replacements
       transports);
  expect_equal
    "skolem_witness_transport_proof_replacements should also rewrite the introduced symbol"
    [TmH "#s1", TmH "def1"; closed_binder_witness, TmH "def1"]
    (Vampire_kernel_elab.skolem_witness_transport_proof_replacements
       transports);
	  let aliases = function
	    | "#s0" -> ["#s0"; "s0"]
	    | "s0" -> ["#s0"; "s0"]
	    | "#s1" -> ["#s1"; "s1"]
	    | "s1" -> ["#s1"; "s1"]
	    | "#s2" -> ["#s2"; "s2"]
	    | "s2" -> ["#s2"; "s2"]
	    | name -> [name]
	  in
  expect_equal
    "skolem_witness_transport_proof_replacements_with_aliases should rewrite all introduced-symbol aliases"
    [TmH "#s1", TmH "def1"; TmH "s1", TmH "def1"; closed_binder_witness, TmH "def1"]
    (Vampire_kernel_elab.skolem_witness_transport_proof_replacements_with_aliases
       ~alias_names:aliases
       transports);
  expect_equal
    "prioritized_skolem_witness_transport_proof_replacements should let branch transports shadow reverse registered witnesses"
    [TmH "#s1", TmH "def1"; TmH "s1", TmH "def1"; closed_binder_witness, TmH "def1"]
    (Vampire_kernel_elab.prioritized_skolem_witness_transport_proof_replacements
       ~normalize:(fun tm -> tm)
       ~alias_names:aliases
       ~witness_symbols:choice_symbols
       ~registered_witnesses:["#s1", closed_binder_witness]
       ~transports
       closed_binder_proof);
	  expect_equal
	    "prioritized_skolem_witness_transport_proof_replacements should keep unshadowed registered witnesses"
	    [outer_before_inner, TmH "#s0"]
	    (Vampire_kernel_elab.prioritized_skolem_witness_transport_proof_replacements
	       ~normalize:(fun tm -> tm)
	       ~alias_names:aliases
	       ~witness_symbols:choice_symbols
	       ~registered_witnesses:["#s0", outer_before_inner]
	       ~transports:[]
	       proof);
	  let ambiguous_transports =
	    [
	      {
	        Vampire_kernel_elab.skolem_transport_name = "#s1";
	        skolem_transport_choice_occurrence = closed_binder_witness;
	        skolem_transport_definition = TmH "def1";
	        skolem_transport_local_template = closed_binder_witness;
	      };
	      {
	        Vampire_kernel_elab.skolem_transport_name = "#s2";
	        skolem_transport_choice_occurrence = closed_binder_witness;
	        skolem_transport_definition = TmH "def2";
	        skolem_transport_local_template = closed_binder_witness;
	      };
	    ]
	  in
	  expect_equal
	    "disambiguate_skolem_witness_transports should drop one choice occurrence with multiple definitions"
	    ([], [closed_binder_witness])
	    (Vampire_kernel_elab.disambiguate_skolem_witness_transports
	       ambiguous_transports);
	  let cleanup_plan =
	    Vampire_kernel_elab.skolem_witness_cleanup_plan
	      ~normalize:(fun tm -> tm)
	      ~alias_names:aliases
	      ~witness_symbols:choice_symbols
	      ~introduced_symbols:["s1"]
	      ~registered_witnesses:["#s1", closed_binder_witness]
	      ~transports
	      closed_binder_proof
	  in
	  expect_equal
	    "skolem_witness_cleanup_plan should expose deterministic transport-backed replacements"
	    [TmH "#s1", TmH "def1"; TmH "s1", TmH "def1"; closed_binder_witness, TmH "def1"]
	    cleanup_plan.Vampire_kernel_elab.skolem_cleanup_replacements;
	  expect_equal
	    "skolem_witness_cleanup_plan should classify introduced aliases before cleanup"
	    {
	      Vampire_kernel_elab.introduced_symbols_present = [];
	      introduced_symbols_with_direct_replacement = [];
	      introduced_symbols_without_direct_replacement = [];
	    }
	    cleanup_plan.Vampire_kernel_elab.skolem_cleanup_introduced_classification;
	  let template_plan =
	    Vampire_kernel_elab.skolem_branch_choice_template_expansion_plan
	      ~alias_names:aliases
	      ~template_limit:1
	      [
	        {
	          Vampire_kernel_elab.skolem_transport_name = "#s1";
	          skolem_transport_choice_occurrence = closed_binder_witness;
	          skolem_transport_definition = TmH "def1";
	          skolem_transport_local_template = TmH "template1";
	        };
	        {
	          Vampire_kernel_elab.skolem_transport_name = "#s2";
	          skolem_transport_choice_occurrence = outer_before_inner;
	          skolem_transport_definition = TmH "def2";
	          skolem_transport_local_template = TmH "template2";
	        };
	      ]
	  in
	  expect_equal
	    "skolem_branch_choice_template_expansion_plan should collect aliases and obey the template limit"
	    {
	      Vampire_kernel_elab.skolem_template_replacement_names =
	        ["#s1"; "#s2"; "s1"; "s2"];
	      skolem_template_local_templates = [TmH "template1"];
	    }
	    template_plan;
	  expect_equal
	    "skolem_branch_choice_template_replacements should build name-to-template replacements"
	    [
	      "#s1", TmH "template1";
	      "#s2", TmH "template1";
	      "s1", TmH "template1";
	      "s2", TmH "template1";
	    ]
	    (Vampire_kernel_elab.skolem_branch_choice_template_replacements
	       template_plan
	       (TmH "template1"));
	  expect_equal
	    "canonical_witness_name should erase certificate-local hash prefixes"
	    "s1"
	    (Vampire_kernel_elab.canonical_witness_name "#s1");
	  begin match
	    Vampire_kernel_elab.unique_registered_choice_expansion_plan
	      ~normalize:(fun tm -> tm)
	      ~witness_symbols:choice_symbols
	      ~registered_witnesses:["#s1", Ap (TmH "eps", TmH "other")]
	      closed_binder_proof
	  with
	  | Vampire_kernel_elab.Unique_registered_choice_expansion expansion ->
	      expect_equal
	        "unique_registered_choice_expansion_plan should expose the unresolved canonical name"
	        "s1"
	        expansion.Vampire_kernel_elab.registered_choice_expansion_name;
	      expect_equal
	        "unique_registered_choice_expansion_plan should collect local choice terms"
	        [closed_binder_witness]
	        expansion.Vampire_kernel_elab.registered_choice_expansion_terms;
	      expect_equal
	        "unique_registered_choice_expansion_plan should build choice-to-symbol replacements"
	        [closed_binder_witness, TmH "s1"]
	        expansion.Vampire_kernel_elab.registered_choice_expansion_replacements
	  | _ ->
	      prerr_endline
	        "kernel_elab unit failure: unique_registered_choice_expansion_plan should find a unique unresolved witness";
	      exit 1
	  end;
	  expect_equal
	    "unique_registered_choice_expansion_plan should report ambiguous unresolved names"
	    (Vampire_kernel_elab.Ambiguous_registered_choice_expansion ["s1"; "s2"])
	    (Vampire_kernel_elab.unique_registered_choice_expansion_plan
	       ~normalize:(fun tm -> tm)
	       ~witness_symbols:choice_symbols
	       ~registered_witnesses:
	         ["#s1", Ap (TmH "eps", TmH "other1");
	          "#s2", Ap (TmH "eps", TmH "other2")]
	       closed_binder_proof);
	  expect_equal
	    "classify_introduced_symbol_replacements should separate direct and indirect cleanup gaps"
	    {
	      Vampire_kernel_elab.introduced_symbols_present = ["#s0"; "s1"];
      introduced_symbols_with_direct_replacement = ["s1"];
      introduced_symbols_without_direct_replacement = ["#s0"];
    }
    (Vampire_kernel_elab.classify_introduced_symbol_replacements
       ~alias_names:aliases
       ~introduced_symbols:["s0"; "s1"]
       ~replacements:[TmH "#s1", TmH "def1"; TmH "s1", TmH "def1"]
       (PPfAp
          (PTmAp (Known "k", Ap (TmH "#s0", TmH "a")),
           PTmAp (Known "k", Ap (TmH "s1", TmH "b")))));
  expect_equal
    "substitute_named_term should preserve vLAM binder convention"
    (Ap (TmH "vLAM", Ap (DB 0, TmH "z")))
    (Vampire_kernel_elab.substitute_named_term
       "X"
       (Ap (TmH "vLAM", Ap (TmH "X", TmH "z"))));
  let nested_exists =
    Ap
      (Ap
         (TmH "vampire_and",
          Ap (TmH "vampire_exists_prop", Lam (Prop, DB 0))),
       Imp
         (TmH "guard",
          Ap (TmH "vampire_exists_prop", Lam (Set, TmH "body"))))
  in
  expect_equal
    "term_exists_head_types should collect nested existential witness types"
    [Prop; Set]
    (Vampire_kernel_elab.term_exists_head_types
       "vampire_exists_prop"
       nested_exists);
  expect_equal
    "term_exists_head_count should count nested existential binders"
    2
    (Vampire_kernel_elab.term_exists_head_count
       "vampire_exists_prop"
       nested_exists);
  expect_equal
    "term_exists_head_types should ignore other existential heads"
    []
    (Vampire_kernel_elab.term_exists_head_types
       "other_exists"
       nested_exists);
  expect_equal
    "term_head should peel type and term applications"
    (TmH "sK")
    (Vampire_kernel_elab.term_head
       (Ap (TpAp (TmH "sK", Prop), TmH "arg")));
  let alias_rewritten =
    Vampire_kernel_elab.rewrite_head_symbols_by_alias
      ~alias_names:aliases
      [TmH "#s0", TmH "eps0"]
      (Lam (Prop, Ap (TmH "s0", DB 0)))
  in
  expect_equal
    "rewrite_head_symbols_by_alias should shift replacements under binders"
    (Lam (Prop, Ap (TmH "eps0", DB 0)))
    alias_rewritten;
  let branch_choice =
    {
      Vampire_kernel_syntax.skolem_branch_choice_index = 0;
      skolem_branch_choice_symbol = "s0";
      skolem_branch_choice_replaced_variable = "X";
      skolem_branch_choice_type = Prop;
      skolem_branch_choice_predicate = Lam (Prop, Ap (DB 0, TmH "a"));
      skolem_branch_choice_body = Ap (TmH "X", TmH "a");
      skolem_branch_choice_witness_term = Some (TmH "#s0");
      skolem_branch_choice_transport_rule =
        Some "choice_witness_substitution";
      skolem_branch_choice_witnessed_body =
        Some (Ap (TmH "#s0", TmH "a"));
    }
  in
  expect_bool
    "skolem_branch_choice_matches_witness should use exact witness terms"
    (Vampire_kernel_elab.skolem_branch_choice_matches_witness
       ~normalize:(fun tm -> tm)
       ~alias_names:aliases
       (TmH "#s0")
       branch_choice);
  expect_bool
    "skolem_branch_choice_matches_witness should use symbol aliases"
    (Vampire_kernel_elab.skolem_branch_choice_matches_witness
       ~normalize:(fun tm -> tm)
       ~alias_names:aliases
       (Ap (TmH "#s0", TmH "arg"))
       { branch_choice with
         Vampire_kernel_syntax.skolem_branch_choice_witness_term = None });
  let branch_contract =
    {
      Vampire_kernel_syntax.skolem_branch_index = 7;
      skolem_branch_parent_index = Some 2;
      skolem_branch_unit = Some "u7";
      skolem_branch_binder_count = Some 0;
      skolem_branch_source_formula = Some (TmH "src");
      skolem_branch_target_formula = Some (TmH "dst");
      skolem_branch_parent_step_variables = [];
      skolem_branch_parent_instantiations = [];
      skolem_branch_introduced_witnesses =
        [
          {
            Vampire_kernel_syntax.skolem_witness_symbol = "s0";
            skolem_witness_replaced_var = "X";
            skolem_witness_term = Some (TmH "#s0");
          };
        ];
      skolem_branch_propositions =
        [
          {
            Vampire_kernel_syntax.skolem_branch_prop_index = 0;
            skolem_branch_prop_role = "source";
            skolem_branch_prop_formula = TmH "src";
          };
          {
            Vampire_kernel_syntax.skolem_branch_prop_index = 1;
            skolem_branch_prop_role = "target";
            skolem_branch_prop_formula = TmH "dst";
          };
        ];
      skolem_branch_choices = [branch_choice];
    }
  in
  expect_equal
    "skolem_branch_witness_symbols should expose introduced witness names"
    ["s0"]
    (Vampire_kernel_elab.skolem_branch_witness_symbols branch_contract);
  expect_equal
    "skolem_branch_choice_for_witness should select branch choices through aliases"
    (Some (branch_contract, branch_choice))
    (Vampire_kernel_elab.skolem_branch_choice_for_witness
       ~alias_names:aliases
       [branch_contract]
       "#s0");
  expect_bool
    "skolem_branch_has_proposition_role should inspect branch proposition roles"
    (Vampire_kernel_elab.skolem_branch_has_proposition_role
       "source"
       branch_contract);
  expect_equal
    "skolem_branch_choice_matching_witness should select choices through aliases"
    (Some branch_choice)
    (Vampire_kernel_elab.skolem_branch_choice_matching_witness
       ~alias_names:aliases
       "#s0"
       branch_contract);
  expect_equal
    "skolem_branch_contract_choice_for_witness should prefer exact source and target contracts"
    (Some (branch_contract, Some branch_choice))
    (Vampire_kernel_elab.skolem_branch_contract_choice_for_witness
       ~alias_names:aliases
       ~branch_matches_formula:(fun formula candidate ->
         candidate = Some formula)
       ~witness:"s0"
       ~source:(TmH "src")
       ~result:(TmH "dst")
       [branch_contract]);
  expect_equal
    "skolem_branch_contract_choice_for_witness should fall back to witness-only choice selection"
    (Some (branch_contract, Some branch_choice))
    (Vampire_kernel_elab.skolem_branch_contract_choice_for_witness
       ~alias_names:aliases
       ~branch_matches_formula:(fun formula candidate ->
         candidate = Some formula)
       ~witness:"#s0"
       ~source:(TmH "other_src")
       ~result:(TmH "other_dst")
       [branch_contract]);
  expect_equal
    "skolem_branch_choice_body should select, rewrite aliases, and bind the replaced variable"
    (Some (Ap (DB 0, TmH "a")))
    (Vampire_kernel_elab.skolem_branch_choice_body
       ~normalize:(fun tm -> tm)
       ~alias_names:aliases
       ~replacements:[]
       ~substitution_name:(Some "X")
       ~target_witness:(TmH "#s0")
       ~witness_type:Prop
       [branch_choice]);
  begin match
    Vampire_kernel_elab.skolem_branch_choice_instantiation
      ~normalize:(fun tm -> tm)
      ~alias_names:aliases
      ~replacements:[]
      ~substitution_name:(Some "X")
      ~target_witness:(TmH "#s0")
      ~witness_type:Prop
      [branch_choice]
  with
  | Some instantiation ->
      expect_equal
        "skolem_branch_choice_instantiation should return the emitted body"
        (Ap (DB 0, TmH "a"))
        instantiation.Vampire_kernel_elab.skolem_choice_body;
      expect_equal
        "skolem_branch_choice_instantiation should return the emitted predicate"
        (Lam (Prop, Ap (DB 0, TmH "a")))
        instantiation.Vampire_kernel_elab.skolem_choice_predicate;
      expect_equal
        "skolem_branch_choice_instantiation should return the emitted witnessed body"
        (Some (Ap (TmH "#s0", TmH "a")))
        instantiation.Vampire_kernel_elab.skolem_choice_witnessed_body;
      let transport_terms =
        Vampire_kernel_elab.skolem_choice_transport_terms
          ~normalize:(fun tm -> tm)
          ~eps_symbol:"eps"
          instantiation
      in
      expect_equal
        "skolem_choice_transport_terms should expose the epsilon witness"
        (Ap (TmH "eps", Lam (Prop, Ap (DB 0, TmH "a"))))
        transport_terms.Vampire_kernel_elab.skolem_transport_epsilon_witness;
      expect_equal
        "skolem_choice_transport_terms should instantiate the body with epsilon"
        (Ap (Ap (TmH "eps", Lam (Prop, Ap (DB 0, TmH "a"))), TmH "a"))
        transport_terms.Vampire_kernel_elab.skolem_transport_epsilon_body;
      expect_equal
        "skolem_choice_transport_terms should preserve the emitted witnessed body"
        (Some (Ap (TmH "#s0", TmH "a")))
        transport_terms.Vampire_kernel_elab.skolem_transport_witnessed_body
  | None ->
      prerr_endline
        "kernel_elab unit failure: skolem_branch_choice_instantiation should keep emitted predicate and body aligned";
      exit 1
  end;
  let lifted =
    Vampire_kernel_elab.lift_skolem_branch_choice_instantiation
      ~ambient_shift:4
      {
        Vampire_kernel_elab.skolem_choice_body =
          Ap (DB 0, DB 2);
        skolem_choice_predicate =
          Lam (Prop, Ap (DB 0, DB 2));
        skolem_choice_witnessed_body =
          Some (Ap (TmH "s0", DB 2));
      }
  in
  expect_equal
    "lift_skolem_branch_choice_instantiation should not move the implicit witness argument"
    (Ap (DB 0, DB 6))
    lifted.Vampire_kernel_elab.skolem_choice_body;
  expect_equal
    "lift_skolem_branch_choice_instantiation should lift free predicate body indices under the lambda"
    (Lam (Prop, Ap (DB 0, DB 6)))
    lifted.Vampire_kernel_elab.skolem_choice_predicate;
  expect_equal
    "lift_skolem_branch_choice_instantiation should lift free witnessed-body indices"
    (Some (Ap (TmH "s0", DB 6)))
    lifted.Vampire_kernel_elab.skolem_choice_witnessed_body;
  expect_equal
    "skolem_branch_choice_instantiation should reject predicate/body drift"
    None
    (Vampire_kernel_elab.skolem_branch_choice_instantiation
       ~normalize:(fun tm -> tm)
       ~alias_names:aliases
       ~replacements:[]
       ~substitution_name:(Some "X")
       ~target_witness:(TmH "#s0")
       ~witness_type:Prop
       [{ branch_choice with
          Vampire_kernel_syntax.skolem_branch_choice_predicate =
            Lam (Prop, Ap (DB 0, TmH "b")) }]);
  expect_equal
    "skolem_branch_choice_instantiation should reject witnessed-body drift"
    None
    (Vampire_kernel_elab.skolem_branch_choice_instantiation
       ~normalize:(fun tm -> tm)
       ~alias_names:aliases
       ~replacements:[]
       ~substitution_name:(Some "X")
       ~target_witness:(TmH "#s0")
       ~witness_type:Prop
       [{ branch_choice with
          Vampire_kernel_syntax.skolem_branch_choice_witnessed_body =
            Some (Ap (TmH "#s0", TmH "b")) }]);
  Vampire_kernel_check.check_skolem_branch_contract
    ~id:"unit"
    ~index:0
    ~normalize:(fun tm -> tm)
    ~alias_names:aliases
    ~introduced_symbol_names:["s0"]
    ~source_formula:(Some (TmH "src"))
    ~target_formula:(Some (TmH "dst"))
    ~propositions:[
      {
        Vampire_kernel_syntax.skolem_branch_prop_index = 0;
        skolem_branch_prop_role = "source";
        skolem_branch_prop_formula = TmH "src";
      };
      {
        Vampire_kernel_syntax.skolem_branch_prop_index = 1;
        skolem_branch_prop_role = "target";
        skolem_branch_prop_formula = TmH "dst";
      };
    ]
    ~choices:[branch_choice];
  expect_error
    "check_skolem_branch_contract should reject predicate/body mismatches"
    (fun () ->
       Vampire_kernel_check.check_skolem_branch_contract
         ~id:"unit"
         ~index:0
         ~normalize:(fun tm -> tm)
         ~alias_names:aliases
         ~introduced_symbol_names:["s0"]
         ~source_formula:None
         ~target_formula:None
         ~propositions:[]
         ~choices:[{
           branch_choice with
           Vampire_kernel_syntax.skolem_branch_choice_predicate =
             Lam (Prop, TmH "wrong");
         }]);
  expect_error
    "check_skolem_branch_contract should reject witnessed-body drift"
    (fun () ->
       Vampire_kernel_check.check_skolem_branch_contract
         ~id:"unit"
         ~index:0
         ~normalize:(fun tm -> tm)
         ~alias_names:aliases
         ~introduced_symbol_names:["s0"]
         ~source_formula:None
         ~target_formula:None
         ~propositions:[]
         ~choices:[{
           branch_choice with
           Vampire_kernel_syntax.skolem_branch_choice_witnessed_body =
             Some (Ap (TmH "#s0", TmH "wrong"));
         }]);
  let helper_formula =
    All
      (Prop,
       Imp
         (Ap (TmH "vampire_exists_prop", Lam (Prop, DB 0)),
          Ap (TmH "done", DB 0)))
  in
  let helper_records =
    Vampire_kernel_elab.skolem_helper_records [TmH "ignored"; helper_formula]
  in
  expect_equal
    "skolem_helper_records should peel forall prefixes and implication bodies"
    [
      {
        Vampire_kernel_elab.skolem_helper_index = 1;
        skolem_helper_tps = [Prop];
        skolem_helper_source =
          Ap (TmH "vampire_exists_prop", Lam (Prop, DB 0));
        skolem_helper_target = Ap (TmH "done", DB 0);
      }
    ]
    helper_records;
  expect_bool
    "term_contains_exists_head should find configured existential heads"
    (Vampire_kernel_elab.term_contains_exists_head
       "vampire_exists_prop"
       helper_formula);
  expect_equal
    "replace_exact_terms_in_term should replace closed witnesses under binders"
    (All (Prop, Ap (TmH "eps0", DB 0)))
    (Vampire_kernel_elab.replace_exact_terms_in_term
       [TmH "#s0", TmH "eps0"]
       (All (Prop, Ap (TmH "#s0", DB 0))));
  expect_bool
    "skolem_helper_target_compatible should accept existential helper targets"
    (Vampire_kernel_elab.skolem_helper_target_compatible
       ~normalize_at_depth:(fun _ tm -> tm)
       ~exists_head:"vampire_exists_prop"
       0
       (Ap (TmH "vampire_exists_prop", Lam (Prop, DB 0)))
       (TmH "anything"));
  begin match helper_records with
  | [helper] ->
      expect_equal
        "matching_skolem_helper should return the selected helper and preserve the rest"
        (Some (helper, []))
        (Vampire_kernel_elab.matching_skolem_helper
           ~normalize_at_depth:(fun _ tm -> tm)
           ~raw_normalize:(fun tm -> tm)
           ~exists_head:"vampire_exists_prop"
           ~local_depth:0
           ~replacements:[]
           ~source:(Ap (TmH "vampire_exists_prop", Lam (Prop, DB 0)))
           ~target:(Ap (TmH "done", DB 0))
           helper_records)
  | _ ->
      prerr_endline "kernel_elab unit failure: helper_records shape";
      exit 1
  end
EOF_OCAML

ocamlopt \
  -I +unix \
  unix.cmxa \
  -I "$ROOT/bin" \
  -o "$WORK_DIR/test_kernel_elab" \
  "$ROOT/bin/hashbtcstub.o" \
  "$ROOT/bin/hashbtc.cmx" \
  "$ROOT/bin/ser.cmx" \
  "$ROOT/bin/hashaux.cmx" \
  "$ROOT/bin/hash.cmx" \
  "$ROOT/bin/hashold.cmx" \
  "$ROOT/bin/mathdata.cmx" \
  "$ROOT/bin/mathdatapfg.cmx" \
  "$ROOT/bin/syntax.cmx" \
  "$ROOT/bin/vampire_kernel_syntax.cmx" \
  "$ROOT/bin/vampire_kernel_check.cmx" \
  "$ROOT/bin/vampire_kernel_elab.cmx" \
  "$WORK_DIR/test_kernel_elab.ml"

"$WORK_DIR/test_kernel_elab"

echo "kernel_elab unit checks passed"
echo "kernel_elab unit artifacts: $WORK_DIR"
