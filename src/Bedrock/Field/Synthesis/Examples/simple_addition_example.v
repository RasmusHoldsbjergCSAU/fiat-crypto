Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import bedrock2.Array.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Syntax.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Word.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import Crypto.Spec.MxDH.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults.
Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Operation.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Field.Translation.Parameters.SelectParameters.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.Tactics.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.X25519_64.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.UnsaturatedSolinasHeuristics.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import bedrock2.Semantics.
Import ListNotations.
Import Syntax.Coercions.
Local Open Scope Z_scope.

Require Import Crypto.Spec.ModularArithmetic.
Definition F := F (2^255 - 19).
Definition a24 : F := F.of_Z _ 121665.

(* Gallina specification *)
Definition ladderstep_gallina
           (X1 : F) (P1 P2 : F * F) : F * F * (F * F) :=
  @MxDH.ladderstep F F.add F.sub F.mul a24 X1 P1 P2.


Existing Instances Defaults64.default_parameters
         curve25519_bedrock2_funcs curve25519_bedrock2_specs
         curve25519_bedrock2_correctness.

Local Notation n := X25519_64.n.
Local Notation s := X25519_64.s.
Local Notation c := X25519_64.c.
Local Notation machine_wordsize := X25519_64.machine_wordsize.
Local Notation M := (UnsaturatedSolinas.m s c).
Local Notation weight :=
  (ModOps.weight (QArith_base.Qnum
                    (UnsaturatedSolinasHeuristics.limbwidth n s c))
                 (Z.pos (QArith_base.Qden
                           (UnsaturatedSolinasHeuristics.limbwidth n s c)))).
Local Notation eval := (Positional.eval weight n).
Local Notation loose_bounds := (UnsaturatedSolinasHeuristics.loose_bounds n s c).
Local Notation tight_bounds := (UnsaturatedSolinasHeuristics.tight_bounds n s c).

Local Open Scope string_scope.
Local Infix "*" := sep : sep_scope.
Delimit Scope sep_scope with sep.

(* need to define scalar-multiplication instance locally so typeclass inference
   knows which instance to pick up (results in weird ecancel_assumption failures
   otherwise) *)
(* TODO: try Existing Instance again *)

Require Import bedrock2.NotationsCustomEntry.

Definition ladderstep : Syntax.func :=
  let X1 := "X1" in
  let X2 := "X2" in
  let X3 := "X3" in
  (* intermediate variables *)
  let A := "A" in
  (* store results back in P1 (X2, Z2) and P2 (X3, Z3) *)
  let Xout := "Xout" in
  let mul := "curve25519_carry_mul" in
  let add := "curve25519_add" in
  ("ladderstep",
   ([X1; X2; X3;
       A; Xout], [],
    bedrock_func_body:(
      add (A, X1, X2) ;     (* llet A  := X2+Z2 in *)
      mul (Xout, A, X3)
  ))).

Instance spec_of_ladderstep : spec_of ladderstep :=
  fun functions =>
    forall (X1 X2 X3 A Xout : list Semantics.word)
           (pX1 pX2 pX3
                pA pout : Semantics.word)
           t m (R : Interface.map.rep (map:=Semantics.mem) -> Prop),
      (* inputs must be bounded by loose_bounds *)
      let X1z := map word.unsigned X1 in
      let X2z := map word.unsigned X2 in
      let X3z := map word.unsigned X3 in
      let Xoutz := map word.unsigned Xout in
      list_Z_bounded_by tight_bounds X1z ->
      list_Z_bounded_by tight_bounds X2z ->
      list_Z_bounded_by tight_bounds X3z ->
      (Bignum n pX1 X1
       * Bignum n pX2 X2
       * Bignum n pX3 X3
       * Bignum n pA A
       * Bignum n pout Xout)%sep m ->
      WeakestPrecondition.call
        functions ladderstep t m
        [pX1; pX2; pX3; pA; pout]
        (fun t' m' rets =>
           t = t' /\
           rets = []%list /\
           exists X4
                  : list Semantics.word,
             let X4z := map word.unsigned X4 in
             let toF := fun x => F.of_Z (2^255 - 19) (eval x) in
             toF (Xoutz) = F.mul ( toF X3z ) (F.add (toF X1z) (toF X2z))
             /\ list_Z_bounded_by tight_bounds X4z
             /\ (Bignum n pX1 X1
                 * Bignum n pX2 X2
                 * Bignum n pA A
                 * Bignum n pout X4)%sep m').

Instance spec_of_curve25519_carry_mul :
  spec_of "curve25519_carry_mul" := spec_of_carry_mul.
Instance spec_of_curve25519_add :
  spec_of "curve25519_add" := spec_of_add.
Ltac prove_bounds :=
  lazymatch goal with
  | H : list_Z_bounded_by tight_bounds ?x
    |- list_Z_bounded_by loose_bounds ?x =>
    apply UnsaturatedSolinas.relax_correct; apply H
  | H : list_Z_bounded_by ?b ?x |- list_Z_bounded_by ?b ?x =>
    apply H
  end.
Ltac prove_length :=
  match goal with
  | |- length (map _ _) = _ => rewrite ?map_length; assumption
  | |- length _ = X25519_64.n =>
    apply bounded_by_loose_bounds_length
      with (s:=X25519_64.s) (c:=X25519_64.c); prove_bounds
  end.
Ltac prove_preconditions :=
  lazymatch goal with
  | |- length _ = _ => prove_length
  | |- list_Z_bounded_by _ _ => prove_bounds
  end.

(* tactics for solving the final arithmetic equivalence *)
Ltac push_FtoZ :=
  cbv [F.sub];
  repeat first [ rewrite ModularArithmeticTheorems.F.to_Z_add
               | rewrite ModularArithmeticTheorems.F.to_Z_mul
               | rewrite ModularArithmeticTheorems.F.to_Z_opp
               | rewrite ModularArithmeticTheorems.F.of_Z_to_Z
               | rewrite ModularArithmeticTheorems.F.to_Z_of_Z
               ].
Ltac rewrite_field_postconditions :=
  repeat lazymatch goal with
         | H : eval (map word.unsigned ?x) mod M = _
           |- context [map word.unsigned ?x] =>
           autorewrite with push_Zmod in H;
           rewrite H
         end.
Ltac solve_F_eq :=
  apply ModularArithmeticTheorems.F.eq_of_Z_iff;
  push_FtoZ; change (Z.pos (2^255 - 19)) with M; pull_Zmod;
  let LHS := fresh "LHS" in
  match goal with |- ?lhs = _ =>
                  set (LHS := lhs) end;
  rewrite_field_postconditions; pull_Zmod;
  subst LHS; try reflexivity.

Ltac t := repeat straightline; handle_call; [ prove_preconditions .. | ].

Lemma ladderstep_correct :
  program_logic_goal_for_function! ladderstep.
Proof.
  straightline_init_with_change.
  Time
  repeat t.

  (* now prove postcondition *)
  repeat split; try reflexivity.
  repeat lazymatch goal with
         | |- exists _, _ => eexists
         | |- _ /\ _ => split
  end. 
  - repeat straightline. solve_F_eq.
    Search ((_ mod _) * _ mod _). rewrite <- Z.mul_mod_idemp_l in H8; try eauto.
      + rewrite H5 in H8. rewrite Z.mul_comm. rewrite Z.mul_mod_idemp_l in H8.
        * rewrite <- H8. subst x0.
      subst x0.
  
    lazymatch goal with
    | |- sep _ _ _ => clear_old_seps; ecancel_assumption
    | _ => idtac
    end.
  all: try prove_bounds.
  cbv [ladderstep_gallina MxDH.ladderstep].
  repeat match goal with
           |- (_ , _) = (_ , _) => apply f_equal2
         end.
  all:solve_F_eq.
Qed.
