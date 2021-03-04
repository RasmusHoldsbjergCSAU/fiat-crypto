Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.WordByWordMontgomery. 
Local Open Scope Z_scope.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Crypto.Bedrock.Field.Translation.Parameters.Defaults32.
Require Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Local Open Scope string_scope.
Import ListNotations.
Require Import bedrock2.NotationsCustomEntry.
(* Require Import bedrock2.NotationsInConstr. *)
Require Import bedrock2.Syntax.
(* Local Open Scope bedrock_expr. *)
Require Crypto.Bedrock.Field.Translation.Parameters.Defaults32.
Require Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Coq.ZArith.ZArith.
(* Require Import bedrock2.NotationsInConstr. *)
Require Import bedrock2.Syntax.
Require Import Coq.Lists.List.
Require Import bedrock2.Array.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Syntax.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Word.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.UnsaturatedSolinasHeuristics.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import bedrock2.Semantics.
Import ListNotations.
Import Syntax.Coercions.
Local Open Scope Z_scope.

Require Import Crypto.Bedrock.Field.Synthesis.Specialized.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.ReifiedOperation.
Require Import Crypto.Bedrock.Field.Common.Names.VarnameGenerator.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.WordByWordMontgomery.
Local Open Scope Z_scope.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.WordByWordMontgomery.
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
Require Import Crypto.Bedrock.Field.Translation.Parameters.SelectParameters.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.Tactics.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import bedrock2.Semantics.
Require Import Theory.QuadraticFieldExtensions.
Import ListNotations.
Import Syntax.Coercions.
Local Open Scope Z_scope.
Section Spec.

Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12prime.

Local Open Scope Z_scope.

(*Parameters to be changed: specify prime and import reification from cache.*)
    Local Notation m := bls12prime.m.
    Local Definition prefix := "bls12_"%string. (* placed before function names *)

    Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12prime.

    Existing Instances Defaults64.default_parameters bls12_bedrock2_funcs
    bls12_bedrock2_specs bls12_bedrock2_correctness.
(*  We require that the prime specified here is the same that was used for reification:
    Change names to match reification cache.*)
    Lemma m_eq: bls12prime.m = m.
    Proof.
        unfold m. reflexivity.
    Qed.
(*  We instantiate specs of all imported bedrock2 functions.
    This needs to be done for typeclass inference to wrok properly.*)

  Instance spec_of_reified_mul :
  spec_of (append prefix "mul") := spec_of_mul.

  Instance spec_of_reified_square :
  spec_of (append prefix "square") := spec_of_square.

  Instance spec_of_reified_add :
  spec_of (append prefix "add") := spec_of_add.

  Instance spec_of_reified_sub :
  spec_of (append prefix "sub") := spec_of_sub.

  Instance spec_of_reified_opp :
  spec_of (append prefix "opp") := spec_of_opp.

  Instance spec_of_reified_to_montgomery :
  spec_of (append prefix "to_montgomery") := spec_of_to_montgomery.

  Instance spec_of_reified_from_montgomery :
  spec_of (append prefix "from_montgomery") := spec_of_from_montgomery.

  Instance spec_of_reified_nonzero :
  spec_of (append prefix "nonzero") := spec_of_nonzero.

  Instance spec_of_reified_selectznz :
  spec_of (append prefix "selectznz") := spec_of_selectznz.

  Instance spec_of_reified_to_bytes :
  spec_of (append prefix "to_bytes") := spec_of_to_bytes.

  Instance spec_of_reified_from_bytes :
  spec_of (append prefix "from_bytes") := spec_of_from_bytes.
(*Instantiation done.*)

(*Initializing parameters; do not touch*)
Local Notation bw := (@width (semantics)).
Local Notation m' := (@WordByWordMontgomery.m' m bw).
Notation n := (WordByWordMontgomery.n m bw).
Local Notation eval := (@WordByWordMontgomery.eval bw n).
Local Notation valid := (@WordByWordMontgomery.valid bw n m).
Local Notation from_mont := (@WordByWordMontgomery.from_montgomerymod bw n m m').
Local Definition valid_words w := valid (List.map Interface.word.unsigned w).
Local Definition map_words := List.map Interface.word.unsigned.
Local Notation r := (WordByWordMontgomery.r bw).
Local Notation r' := (WordByWordMontgomery.r' m bw).
Local Definition num_bytes := Eval compute in (Z.of_nat (((Z.to_nat bw * n) / 8)%nat)).


Lemma bw_eq : WordByWordMontgomery.n m (@width (@semantics Defaults64.default_parameters)) = n.
Proof.
    reflexivity. 
Qed.

Ltac handle_bignum_preconditions :=
    sepsimpl; rewrite m_eq; rewrite bw_eq; ecancel_assumption.

Ltac handle_preconditions :=
    try handle_bignum_preconditions; eauto.

Local Notation evfst x := (eval (from_mont (fst x))).
Local Notation evsnd x := (eval (from_mont (snd x))).


Definition Fp2_add_Gallina_spec in1 in2 out :=
    valid (fst out) /\ valid (snd out) /\
    evfst out = (evfst in1 + evfst in2) mod m /\
    evsnd out = (evsnd in1 + evsnd in2) mod m.

Definition Fp2_mul_Gallina_spec in1 in2 out :=
    valid (fst out) /\ valid (snd out) /\
    evfst out = (evfst in1 * evfst in2 - evsnd in1 * evsnd in2) mod m /\
    evsnd out = (evfst in1 * evsnd in2 + evfst in2 * evsnd in1) mod m.

  Definition Fp2_add : Syntax.func :=
  let outr := "outr" in
  let outi := "outi" in
  let xr := "xr" in
  let xi := "xi" in
  let yr := "yr" in
  let yi := "yi" in
  let add := (append prefix "add") in  
  ("Fp2_add", (
    [outr; outi; xr; xi; yr; yi], [],
    bedrock_func_body:(
    add (outr, yr, xr);
    add (outi, yi, xi)
    )
  )).

  Check (expr.literal 0).
  Definition Fp2_mul : Syntax.func :=
    let outr := "outr" in
    let outi := "outi" in
    let xr := "xr" in
    let xi := "xi" in
    let yr := "yr" in
    let yi := "yi" in
    let v0 := "v0" in
    let v1 := "v1" in
    let v2 := "v2" in
    let add := (append prefix "add") in
    let mul := (append prefix "mul") in
    let sub := (append prefix "sub") in  
    ("Fp2_mul", (
      [outr; outi; xr; xi; yr; yi], [],
      bedrock_func_body:(
      stackalloc num_bytes as v0 {
        stackalloc num_bytes as v1 {
          stackalloc num_bytes as v2 {
            mul (v0, xr, yr);
            mul (v1, xi, yi);
            sub (outr, v0, v1);
            add (v2, xr, xi);
            add (outi, yr, yi);
            mul (outi, v2, outi);
            sub (outi, outi, v0);
            sub (outi, outi, v1)
          }
        }
      }
      )
    )).
    
  Local Open Scope string_scope.
  Local Infix "*" := sep : sep_scope.
  Delimit Scope sep_scope with sep.

Instance spec_of_my_add: spec_of Fp2_add :=
fun functions : list (string * (list string * list string * cmd)) =>
    forall (wxr wxi wyr wyi : list Interface.word.rep)
    (pxr pxi pyr pyi poutr pouti : Interface.word.rep)
    (wold_outr wold_outi : list Interface.word.rep) (t : Semantics.trace)
    (m0 : Interface.map.rep) (Rxr Rxi Ryr Ryi Rout : Interface.map.rep -> Prop),
    valid (List.map Interface.word.unsigned wxr) /\
    valid (List.map Interface.word.unsigned wxi) /\
    valid (List.map Interface.word.unsigned wyr) /\
    valid (List.map Interface.word.unsigned wyi) ->
    (((Bignum n pxr wxr) ) *
    ((Bignum n pxi wxi) ) *
    ((Bignum n pyr wyr) ) *
    ((Bignum n pyi wyi) ) *
    (Bignum n poutr wold_outr) * (Bignum n pouti wold_outi))%sep m0 ->
    WeakestPrecondition.call functions ( "Fp2_add") t m0
    ([pouti; poutr; pxi; pxr; pyi; pyr])
    (fun (t' : Semantics.trace) (m' : Interface.map.rep)
        (rets : list Interface.word.rep) =>
    t = t' /\
    rets = nil /\
    (exists (woutr wouti : list Interface.word.rep) Rout,
        (
                (Fp2_add_Gallina_spec (List.map Interface.word.unsigned wxr, List.map Interface.word.unsigned wxi)
                (List.map Interface.word.unsigned wyr, List.map Interface.word.unsigned wyi)
                (List.map Interface.word.unsigned woutr, List.map Interface.word.unsigned wouti) /\
                valid (List.map Interface.word.unsigned woutr) /\
                valid (List.map Interface.word.unsigned wouti)) /\
             ((Bignum n poutr woutr) * (Bignum n pouti wouti) * Rout)%sep m'))).


Instance spec_of_my_mul: spec_of Fp2_mul :=
fun functions : list (string * (list string * list string * cmd)) =>
    forall (wxr wxi wyr wyi : list Interface.word.rep)
    (pxr pxi pyr pyi pv0 pv1 pv2 poutr pouti : Interface.word.rep)
    (wold_outr wold_outi wold_v0 wold_v1 wold_v2 : list Interface.word.rep) (t : Semantics.trace)
    (m0 : Interface.map.rep) (Rxr Rxi Ryr Ryi Rout : Interface.map.rep -> Prop),
    valid (List.map Interface.word.unsigned wxr) /\
    valid (List.map Interface.word.unsigned wxi) /\
    valid (List.map Interface.word.unsigned wyr) /\
    valid (List.map Interface.word.unsigned wyi) ->
    (((Bignum n pxr wxr) ) *
    ((Bignum n pxi wxi) ) *
    ((Bignum n pyr wyr) ) *
    ((Bignum n pyi wyi) ) *
    (Bignum n poutr wold_outr) * (Bignum n pouti wold_outi))%sep m0 ->
    WeakestPrecondition.call functions ( "Fp2_mul") t m0
    ([poutr; pouti; pxr; pxi; pyr; pyi])
    (fun (t' : Semantics.trace) (m' : Interface.map.rep)
        (rets : list Interface.word.rep) =>
    t = t' /\
    rets = nil /\
    (exists (woutr wouti : list Interface.word.rep) Rout,
        (
                (Fp2_mul_Gallina_spec (List.map Interface.word.unsigned wxr, List.map Interface.word.unsigned wxi)
                (List.map Interface.word.unsigned wyr, List.map Interface.word.unsigned wyi)
                (List.map Interface.word.unsigned woutr, List.map Interface.word.unsigned wouti) /\
                valid (List.map Interface.word.unsigned woutr) /\
                valid (List.map Interface.word.unsigned wouti)) /\
             ((Bignum n poutr woutr) * (Bignum n pouti wouti) * Rout)%sep m'))).

             


Require Import Crypto.Bedrock.Field.Synthesis.Specialized.Tactics.
Require Import bedrock2.string2ident.
Require Import Crypto.Arithmetic.WordByWordMontgomery.


Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Tactics.syntactic_unify.
Require Import bedrock2.Lift1Prop.

Theorem Fp2_add_ok: program_logic_goal_for_function! Fp2_add.
Proof.
    (*Initializing*)
    straightline_init_with_change.
    repeat straightline.


    (*first function call*)
    handle_call; [eauto ..|].
    (*Second function call*)
    handle_call; [eauto .. |].

    (*Prove postcondition*)
    repeat split; auto. do 3 eexists.
    split.
    2: { clear_old_seps. ecancel_assumption. }
    split.
      2: {split; eauto. }
    split. About sep.
      - eauto.
      - split; [eauto|]. split.
        + rewrite Z.add_comm.
          rewrite Prod.fst_pair.
          rewrite Prod.fst_pair.
          rewrite Prod.fst_pair.
          rewrite <- H9. rewrite Z.mod_small.
            * reflexivity.
            * apply WordByWordMontgomery.from_montgomerymod_correct with (r' := r') (m' := m') in H11.
              {
                destruct H11. destruct H12. apply H13.
              }
              all: try reflexivity. simpl.
               cbv [m]. cbv [WordByWordMontgomery.n]. simpl. auto with zarith.
        + rewrite Z.add_comm.
          rewrite Prod.snd_pair.
          rewrite Prod.snd_pair.
          rewrite Prod.snd_pair.
          rewrite <- H6. rewrite Z.mod_small.
          * reflexivity.
          * apply WordByWordMontgomery.from_montgomerymod_correct with (r' := r') (m' := m') in H8.
            {
              destruct H8. destruct H12. apply H13.
            }
            all: try reflexivity. simpl.
            cbv [m]. cbv [WordByWordMontgomery.n]. simpl. auto with zarith.
Qed.

Lemma valid_mod {x : list Z} : valid x -> eval (from_mont x) mod m =eval (from_mont x).
Proof.
  intros. assert (valid (from_mont x)).
    - pose proof (WordByWordMontgomery.from_montgomerymod_correct bw n m r' m').
      apply (H0).
      all: (auto; simpl; try lia).
        + unfold m. simpl. lia.
        + unfold m. cbv [WordByWordMontgomery.n]. simpl. lia.
        + unfold m. simpl. lia.
    - destruct H0. rewrite Z.mod_small; try reflexivity. unfold eval. auto.
Qed.

Check Interface.map.split.
Notation msplit := Interface.map.split.

Lemma split_split_split : forall (m m1 m2 x0 x1 : @Interface.map.rep (@word (@semantics Defaults64.default_parameters))
Init.Byte.byte (@mem (@semantics Defaults64.default_parameters))), msplit m m1 m2 -> msplit m1 x0 x1
  -> msplit m (Interface.map.putmany m2 x1) x0.
Proof.
  intros. split.
    - pose proof Properties.map.putmany_assoc.
      destruct H. destruct H0. rewrite H. rewrite H0. rewrite (Properties.map.putmany_comm x0 x1); auto.
      rewrite (Properties.map.putmany_comm).

      + rewrite Properties.map.putmany_assoc; auto.
        * rewrite Properties.map.disjoint_comm. apply Properties.map.sub_domain_disjoint with (m1' := m1); auto.
          rewrite H0. rewrite Properties.map.putmany_comm; auto.
          apply Properties.map.sub_domain_putmany_r. apply Properties.map.sub_domain_refl.
        * apply Properties.map.disjoint_comm. auto.
        * rewrite Properties.map.disjoint_comm. apply Properties.map.sub_domain_disjoint with (m1' := m1); auto.
          rewrite H0. apply Properties.map.sub_domain_putmany_r. apply Properties.map.sub_domain_refl.
      + rewrite Properties.map.putmany_comm.
        * rewrite <- H0; auto.
        * rewrite Properties.map.disjoint_comm. auto.
  - destruct H, H0. apply Properties.map.disjoint_putmany_l. split.
    + rewrite Properties.map.disjoint_comm. apply Properties.map.sub_domain_disjoint with (m1' := m1); auto.
      rewrite H0. apply Properties.map.sub_domain_putmany_r. apply Properties.map.sub_domain_refl.
    + apply Properties.map.disjoint_comm; auto.
Qed.

 Definition R_putmany (m1 m2 m : @Interface.map.rep (@word (@semantics Defaults64.default_parameters))
 Init.Byte.byte (@mem (@semantics Defaults64.default_parameters))) := m = Interface.map.putmany m1 m2.
    
Lemma alloc_seps (m m1 m2 : @Interface.map.rep (@word (@semantics Defaults64.default_parameters))
Init.Byte.byte (@mem (@semantics Defaults64.default_parameters)))
 P : Interface.map.split m m1 m2 -> (exists R, (P * R)%sep m1) ->
  exists (R' : Interface.map.rep -> Prop), (P * R')%sep m.
Proof.
  intros. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1.
   exists (R_putmany x1 m2). unfold sep. exists x0. exists (Interface.map.putmany x1 m2).
    split.
      - rewrite Properties.map.split_comm. rewrite Properties.map.putmany_comm.
        + apply (split_split_split m m1 m2 x0 x1 H H0).
        + destruct H. apply Properties.map.sub_domain_disjoint with (m1' := m1); auto.
          destruct H0. rewrite H0. rewrite Properties.map.putmany_comm.
          * apply Properties.map.sub_domain_putmany_r. apply Properties.map.sub_domain_refl.
          * auto.
      - split; auto. unfold R_putmany. auto.
Qed.

Local Infix " a +m b" := (Interface.map.putmany a b) (at level 11).

Lemma split_distr (m m1 m2 : @Interface.map.rep (@word (@semantics Defaults64.default_parameters))
Init.Byte.byte (@mem (@semantics Defaults64.default_parameters))) x x0 x1 x2 : msplit m m1 m2 -> msplit m1 x x0 -> msplit m2 x1 x2
  -> msplit m (Interface.map.putmany x x1) (Interface.map.putmany x0 x2).
Proof.
  intros. destruct H. destruct H0. destruct H1. unfold msplit.
  split.
    - rewrite H. rewrite H0. rewrite H1. rewrite Properties.map.putmany_assoc; auto.
      + rewrite Properties.map.putmany_assoc; auto.
        * rewrite (Properties.map.putmany_comm _ x1).
        { rewrite Properties.map.putmany_assoc.
          - rewrite (Properties.map.putmany_comm x1); auto.
             apply (Properties.map.sub_domain_disjoint x1 m2 x).
              + rewrite Properties.map.disjoint_comm. apply Properties.map.sub_domain_disjoint with (m1' := m1); auto.
                rewrite H0. apply Properties.map.sub_domain_putmany_r. apply Properties.map.sub_domain_refl.
              + rewrite H1. apply Properties.map.sub_domain_putmany_r. apply Properties.map.sub_domain_refl.
          - apply Properties.map.sub_domain_disjoint with (m1' := m2).
           + rewrite Properties.map.disjoint_comm. apply Properties.map.sub_domain_disjoint with (m1' := m1); auto.
             rewrite H0. apply Properties.map.sub_domain_putmany_r. apply Properties.map.sub_domain_refl.
           + rewrite H1. apply Properties.map.sub_domain_putmany_r. apply Properties.map.sub_domain_refl.
          - auto.
          - apply Properties.map.sub_domain_disjoint with (m1' := m2).
            + rewrite Properties.map.disjoint_comm. apply Properties.map.sub_domain_disjoint with (m1' := m1); auto.
              rewrite H0. rewrite Properties.map.putmany_comm; auto. apply Properties.map.sub_domain_putmany_r. apply Properties.map.sub_domain_refl.
            + rewrite H1. apply Properties.map.sub_domain_putmany_r. apply Properties.map.sub_domain_refl.
        }
        rewrite <- H0. rewrite Properties.map.disjoint_comm.
        apply Properties.map.sub_domain_disjoint with (m1' := m2).
        {
          apply Properties.map.disjoint_comm. auto.
        }
        rewrite H1. apply Properties.map.sub_domain_putmany_r. apply Properties.map.sub_domain_refl.
        * apply Properties.map.disjoint_putmany_l; split; auto.
          rewrite Properties.map.disjoint_comm. apply Properties.map.sub_domain_disjoint with ( m1' := m1).
          {
            rewrite Properties.map.disjoint_comm. apply Properties.map.sub_domain_disjoint with (m1' := m2).
              - rewrite Properties.map.disjoint_comm. auto.
              - rewrite H1. apply Properties.map.sub_domain_putmany_r. apply Properties.map.sub_domain_refl.
          }
          rewrite H0. rewrite Properties.map.putmany_comm.
          {
            apply Properties.map.sub_domain_putmany_r. apply Properties.map.sub_domain_refl.
          }
          auto.
        * apply Properties.map.sub_domain_disjoint with ( m1' := m1).
        {
          rewrite Properties.map.disjoint_comm. apply Properties.map.sub_domain_disjoint with (m1' := m2).
            - rewrite Properties.map.disjoint_comm. auto.
            - rewrite H1. rewrite Properties.map.putmany_comm.
              + apply Properties.map.sub_domain_putmany_r. apply Properties.map.sub_domain_refl.
              + auto.
        }
        rewrite H0. rewrite Properties.map.putmany_comm.
        {
          apply Properties.map.sub_domain_putmany_r. apply Properties.map.sub_domain_refl.
        }
        auto.
        * apply Properties.map.disjoint_putmany_l; split; auto.
        apply Properties.map.sub_domain_disjoint with ( m1' := m1).
        {
          rewrite Properties.map.disjoint_comm. apply Properties.map.sub_domain_disjoint with (m1' := m2).
            - rewrite Properties.map.disjoint_comm. auto.
            - rewrite H1. rewrite Properties.map.putmany_comm.
              + apply Properties.map.sub_domain_putmany_r. apply Properties.map.sub_domain_refl.
              + auto.
        }
        rewrite H0.
        {
          apply Properties.map.sub_domain_putmany_r. apply Properties.map.sub_domain_refl.
        }
    + rewrite <- H0. rewrite Properties.map.disjoint_comm.
      apply Properties.map.sub_domain_disjoint with (m1' := m2).
      * rewrite Properties.map.disjoint_comm. auto.
      * rewrite H1. apply Properties.map.sub_domain_putmany_r. apply Properties.map.sub_domain_refl.
    +  rewrite <- H0. rewrite Properties.map.disjoint_comm.
    apply Properties.map.sub_domain_disjoint with (m1' := m2).
    * rewrite Properties.map.disjoint_comm. auto.
    * rewrite H1. rewrite Properties.map.putmany_comm; auto. apply Properties.map.sub_domain_putmany_r. apply Properties.map.sub_domain_refl.
  - rewrite Properties.map.disjoint_putmany_r; split; rewrite Properties.map.disjoint_putmany_l; split; auto.
    + rewrite Properties.map.disjoint_comm. apply Properties.map.sub_domain_disjoint with ( m1' := m1).
    {
      rewrite Properties.map.disjoint_comm. apply Properties.map.sub_domain_disjoint with (m1' := m2).
        - rewrite Properties.map.disjoint_comm. auto.
        - rewrite H1. apply Properties.map.sub_domain_putmany_r. apply Properties.map.sub_domain_refl.
    }
    rewrite H0. rewrite Properties.map.putmany_comm.
    {
      apply Properties.map.sub_domain_putmany_r. apply Properties.map.sub_domain_refl.
    }
    auto.
    + apply Properties.map.sub_domain_disjoint with ( m1' := m1).
    {
      rewrite Properties.map.disjoint_comm. apply Properties.map.sub_domain_disjoint with (m1' := m2).
        - rewrite Properties.map.disjoint_comm. auto.
        - rewrite H1. rewrite Properties.map.putmany_comm.
          + apply Properties.map.sub_domain_putmany_r. apply Properties.map.sub_domain_refl.
          + auto.
    }
    rewrite H0.
    {
      apply Properties.map.sub_domain_putmany_r. apply Properties.map.sub_domain_refl.
    }
Qed.

        

 Lemma alloc_seps_alt (m m1 m2 : @Interface.map.rep (@word (@semantics Defaults64.default_parameters))
    Init.Byte.byte (@mem (@semantics Defaults64.default_parameters)))
    P1 R1 P2 R2 : Interface.map.split m m1 m2 ->
      (P1 * R1)%sep m1 -> (P2 * R2)%sep m2 ->
        exists (R' : Interface.map.rep -> Prop), (P1 * P2 * R')%sep m.
Proof.
  intros. destruct H0. destruct H0. destruct H0. destruct H2.
          destruct H1. destruct H1. destruct H1. destruct H4.
          exists (R_putmany x0 x2). unfold sep. exists (Interface.map.putmany x x1).
          exists (Interface.map.putmany x0 x2). split.
            - pose proof (split_distr m m1 m2 x x0 x1 x2). apply H6; auto.
            - split.
              + exists x. exists x1. split; auto. destruct H1. unfold msplit. split; auto.
                destruct H0. apply Properties.map.sub_domain_disjoint with (m1' := m1).
                * rewrite Properties.map.disjoint_comm. apply Properties.map.sub_domain_disjoint with (m1' := m2).
                  {
                    rewrite Properties.map.disjoint_comm; auto. destruct H. auto.
                  }
                  rewrite H1. apply Properties.map.sub_domain_putmany_r. apply Properties.map.sub_domain_refl.
                * rewrite H0. apply Properties.map.sub_domain_putmany_r. apply Properties.map.sub_domain_refl.
              + unfold R_putmany. auto.
Qed.

Lemma alloc_seps_alt' (m m1 m2 : @Interface.map.rep (@word (@semantics Defaults64.default_parameters))
Init.Byte.byte (@mem (@semantics Defaults64.default_parameters)))
P1 P2 : Interface.map.split m m1 m2 ->
  (exists R1, (P1 * R1)%sep m1) -> (exists R2, (P2 * R2)%sep m2) ->
    exists (R' : Interface.map.rep -> Prop), (P1 * P2 * R')%sep m.
Proof.
intros. destruct H0 as [R1]. destruct H0. destruct H0. destruct H0. destruct H2.
      destruct H1 as [R2]. destruct H1. destruct H1. destruct H1. destruct H4.
      exists (R_putmany x0 x2). unfold sep. exists (Interface.map.putmany x x1).
      exists (Interface.map.putmany x0 x2). split.
        - pose proof (split_distr m m1 m2 x x0 x1 x2). apply H6; auto.
        - split.
          + exists x. exists x1. split; auto. destruct H1. unfold msplit. split; auto.
            destruct H0. apply Properties.map.sub_domain_disjoint with (m1' := m1).
            * rewrite Properties.map.disjoint_comm. apply Properties.map.sub_domain_disjoint with (m1' := m2).
              {
                rewrite Properties.map.disjoint_comm; auto. destruct H. auto.
              }
              rewrite H1. apply Properties.map.sub_domain_putmany_r. apply Properties.map.sub_domain_refl.
            * rewrite H0. apply Properties.map.sub_domain_putmany_r. apply Properties.map.sub_domain_refl.
          + unfold R_putmany. auto.
Qed.



Require Import WordByWordMontgomery.
Require Import coqutil.Map.Properties.

Lemma Bignum_anybytes: forall m a wa, Bignum n a wa m -> anybytes a (num_bytes) m.
Proof.
  intros. pose proof (Bignum_to_bytes n a wa).
  unfold impl1 in H0.
  pose proof (H0 m H). unfold ex1 in H1. destruct H1.
  pose proof (array_1_to_anybytes x m a). sepsimpl_hyps. apply H2 in H3.
  assert (num_bytes = Z.of_nat (Datatypes.length x)).
  {
    rewrite H1. simpl. auto.
  }
  rewrite H4. auto.
Qed.

Lemma anybytes_Bignum: forall m a, anybytes a (num_bytes) m -> exists wa, (Bignum n a wa) m.
Proof.
  intros. About anybytes. destruct H.
  pose proof (Bignum_of_bytes n a x). assert (length x =  (n * (Z.to_nat word_size_in_bytes))%nat).
    {
      simpl. simpl in H. Check ftprint. pose proof (map.of_disjoint_list_zip_length (ftprint a num_bytes) x m).
      simpl in H1. rewrite H1; auto.
    }
  apply H0 in H1. unfold impl1 in H1. unfold ex1 in H1.
  pose proof (of_disjoint_list_zip_to_array_1 (Z.to_nat num_bytes) a x m). apply H2 in H.
  apply H1. auto.
Qed.

Lemma anybytes_Bignum_alt: forall m a R, ((anybytes a (num_bytes)) * R)%sep m 
  -> exists wa, (Bignum n a wa * R)%sep m.
Proof.
  intros. do 3 destruct H. destruct H0.
  pose proof (anybytes_Bignum x a H0). destruct H2.
  exists x1.
  exists x. exists x0. split; auto.
Qed.

Lemma empty_frame: forall (P : (@Interface.map.rep (@word (@semantics Defaults64.default_parameters))
Init.Byte.byte (@mem (@semantics Defaults64.default_parameters))) -> Prop) (m : (@Interface.map.rep (@word (@semantics Defaults64.default_parameters))
Init.Byte.byte (@mem (@semantics Defaults64.default_parameters)))),
P m -> exists R, (P * R)%sep m.
Proof. intros. exists (emp True). ecancel_assumption. Qed.

Ltac straightline' :=
  match goal with
  | [Hminit : ?mcond (?minit : @Interface.map.rep _ _ _)
      |- forall (_ : @word.rep _ _)
                (_ _ : @Interface.map.rep _ _ _),
          anybytes _ ?numbytes _ -> msplit _ ?minit _ -> _ ] =>
      let a := (fresh "a") in
      let mStack := (fresh "mStack") in
      let mnew := (fresh "mnew") in
      let Hany := (fresh "Hany") in
      let HanyBignum := (fresh "HanyBignum") in
      let anyval := (fresh "anyval") in
      let Hsplit := (fresh "Hsplit") in
      let Hmnew := (fresh "Hmnew") in
      let R := (fresh "R") in
      intros a mStack mnew Hany Hsplit; destruct (anybytes_Bignum mStack a Hany) as [anyval HanyBignum];
      destruct (alloc_seps_alt' mnew minit mStack mcond (Bignum _ _ _) Hsplit (empty_frame mcond minit Hminit) (empty_frame (Bignum _ _ _) mStack HanyBignum)) as [R Hmnew];
      clear Hany Hsplit HanyBignum
  | _ => straightline
  end.

Ltac exists_frag :=
  match goal with
  | [
      |- exists (_ _ : @Interface.map.rep _ _ _),
        (anybytes ?addr _ _) /\ (msplit ?mem _ _) /\ _ ] =>
        let Hany := (fresh "Hany") in
        idtac
        (* assert (Hany: exists R, ((Bignum n addr _) * R)%sep mem) by (eexists; ecancel_assumption) *)
  | _ => remember 5 as fail
  end.

  Check @sep.
Ltac testac P H :=
  match H with 
  | @sep _ _ _ _ _ _ => remember 4 as true
  | _ => remember 6 as false
  end.




Require Import coqutil.Tactics.letexists.
Theorem Fp2_mul_ok: program_logic_goal_for_function! Fp2_mul.
Proof.
  repeat straightline'.
  repeat (handle_call; [auto| auto| ]).
  exists_frag.
  Ltac get_frame_as_list l P mem :=
    match goal with 
      | [ _ : @sep _ _ _ ?P' ?R' mem |- _] =>
        match P' with
          | P =>
            let thisFrame := (fresh "thisFrame") in remember (l ++ [R']) as thisFrame
          | _ => remember 7 as eyyyy
        end
      | _ => remember 6 as false
    end. Check R.
  get_frame_as_list ([] : list (Interface.map.rep)) (Bignum n pouti x6) a5. Check H28. Set Printing All.
  assert (Hnew : exists R, ((Bignum n a1 x2) * R)%sep a5).
    - eexists.
      pose proof (sep_comm (Bignum n a1 x2) ((Bignum n poutr x1 *
      (Bignum n a0 x0 *
       (Bignum n a x *
        (Bignum n pxr wxr *
         (Bignum n pxi wxi *
          (Bignum n pyr wyr * (Bignum n pyi wyi * (R * (R0 * R1)))))))))%sep) a5). destruct H30.
          
          rewrite H30 in H28.
    listify H28. Check seps.
    assert (seps [Bignum n pouti x6; Bignum n a1 x2; Bignum n poutr x1; 
    Bignum n a0 x0; Bignum n a x; Bignum n pxr wxr; Bignum n pxi wxi;
    Bignum n pyr wyr; Bignum n pyi wyi; R; R0; R1] a5).
      + About reify. pose proof ( bedrock2.Map.SeparationLogic.reify Tree.to_sep ( (Bignum n pouti x6 *
      (Bignum n a1 x2 *
       (Bignum n poutr x1 *
        (Bignum n a0 x0 *
         (Bignum n a x *
          (Bignum n pxr wxr *
           (Bignum n pxi wxi *
            (Bignum n pyr wyr * (Bignum n pyi wyi * (R * (R0 * R1)))))))))))%sep)). simpl. auto.
    
    refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H28). reify_goal. ecancel_assumption. lazymatch goal with |- Lift1Prop.iff1 _ (seps ?RHS) => (remember RHS as this) end.
    - eexists. syntactic_unify_deltavar a5 a5. refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H28).
    cancel.
    ecancel_assumption. 
  destruct Hany as [R' Hany1]. destruct Hany1 as [mStack' Hany2]. destruct Hany2 as [mem' Hmem].
  destruct Hmem as [Hmem HStack]. About ecancel_assumption. destruct H31.
  exists x9, x8. split. - pose proof (Bignum_anybytes x8 a1 x2). apply H33. auto.
  sepsimpl.

  assert ((Bignum n a1 x9 * Ra11)%sep a11 ).
              {
                subst Ra11. ecancel_assumption.
              }
              destruct H79. destruct H79. exists x15. exists x14. split.
              1: {
                apply Bignum_anybytes with (wa := x9). destruct H79. destruct H80.
                auto.
              }
              split.
              1: {
                apply Properties.map.split_comm. destruct H79. auto.
              }
              destruct H79. destruct H80.
              subst Ra11.
              remember ((emp1 *
              (Bignum n poutr x8 *
               (emp2 *
                 (Bignum n a x6 *
                  (Bignum n pxr wxr *
                   (Bignum n pxi wxi * (Bignum n pyr wyr * (Bignum n pyi wyi * x0))))))) *
              Bignum n pouti x13)%sep) as Rx15.
              assert ((Bignum n a0 x7 * Rx15)%sep x15).
              {
                subst Rx15. ecancel_assumption.
              }
              destruct H82. destruct H82. destruct H82. destruct H83.
              exists x17. exists x16. split.
              1: {
                apply Bignum_anybytes with (wa := x7). auto.
              }
              split.
              1: {
                apply Properties.map.split_comm. auto.
              }
              subst Rx15.
              remember ((emp1 *
              (Bignum n poutr x8 *
               (emp2 *
                  (Bignum n pxr wxr *
                   (Bignum n pxi wxi * (Bignum n pyr wyr * (Bignum n pyi wyi * x0)))))) *
              Bignum n pouti x13)%sep) as Rx17.
              assert ((Bignum n a x6 * Rx17)%sep x17).
              {
                subst Rx17. ecancel_assumption.
              }
              destruct H85. destruct H85. destruct H85. destruct H86.
              exists x19. exists x18. split.
              1: {
                apply Bignum_anybytes with (wa := x6). auto.
              }
              split.
              1: {
                apply Properties.map.split_comm. auto.
              }
              subst Rx17.
              repeat straightline.
              
              split.
               1: { reflexivity. }
               split.
               1: {reflexivity. }
               eexists. eexists. eexists. split.
               2: { ecancel_assumption. }
               unfold Fp2_mul_Gallina_spec.
               split; split.
               all: sepsimpl_hyps.
                - subst emp1. sepsimpl_hyps. auto.
                - split.
                  + subst emp2. subst emp1. sepsimpl_hyps. auto.
                  + split.
                    * subst emp1. subst emp2.
                      sepsimpl_hyps.
                      remember (eval (from_mont (map word.unsigned wxi))) as xi.
                      remember (eval (from_mont (map word.unsigned wxr))) as xr.
                      remember (eval (from_mont (map word.unsigned wyi))) as yi.
                      remember (eval (from_mont (map word.unsigned wyr))) as yr.
                      rewrite (valid_mod H89) in H84. rewrite H84.
                  
                        rewrite (valid_mod H78) in H49. rewrite H49.
                        rewrite (valid_mod H54) in H33. rewrite H33.
                        rewrite <- Zminus_mod. apply (f_equal (fun y => y mod m)). ring.
                    * subst emp1. subst emp2. sepsimpl_hyps.
                      remember (eval (from_mont (map word.unsigned wxi))) as xi.
                      remember (eval (from_mont (map word.unsigned wxr))) as xr.
                      remember (eval (from_mont (map word.unsigned wyi))) as yi.
                      remember (eval (from_mont (map word.unsigned wyr))) as yr.
                      rewrite (valid_mod H40) in H24. rewrite H24.
                      rewrite (valid_mod H56) in H27. rewrite H27.
                      rewrite (valid_mod H58) in H55. rewrite H55.
                      rewrite (valid_mod H62) in H59. rewrite H59.
                      rewrite (valid_mod H60) in H57. rewrite H57.
                      rewrite (valid_mod H54) in H33. rewrite H33.
                      rewrite (valid_mod H78) in H49. rewrite H49.
                      rewrite <- Z.mul_mod.
                        2: { unfold m. simpl. auto with zarith. }
                      rewrite <- (Zminus_mod _ (xr * yr)).
                      rewrite <- Zminus_mod. apply (f_equal (fun y => (y mod m))). ring.
                      
                      
                      
                - subst emp1; subst emp2; sepsimpl_hyps; auto.
                - subst emp1; subst emp2. sepsimpl_hyps. auto.
Qed.

(*Printing to C*)
From bedrock2 Require Import ToCString Bytedump.
Definition bls12_c_add :=
  c_module (add :: nil).
  Definition bls12_c_mul :=
  c_module (mul :: nil).
  Definition bls12_c_sub :=
  c_module (sub :: nil).
  Definition bls12_c_Fp2_add :=
  c_module (Fp2_add :: nil).
  Definition bls12_c_Fp2_mul :=
  c_module (Fp2_mul :: nil).
Eval compute in bls12_c_Fp2_mul.

