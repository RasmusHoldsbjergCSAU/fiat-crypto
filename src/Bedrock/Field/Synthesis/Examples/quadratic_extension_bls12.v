Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
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
Require Import bedrock2.NotationsInConstr.
Require Import bedrock2.Syntax.
Local Open Scope bedrock_expr.
Require Crypto.Bedrock.Field.Translation.Parameters.Defaults32.
Require Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.NotationsInConstr.
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
    Local Definition u := -0xd201000000010000.
    Local Definition p_of_u u := (((u - 1)^2 * (u^4 - u^2 + 1)) / 3) + u.
    Local Notation m := bls12prime.m.
    Local Definition prefix := "bls12_"%string. (* placed before function names *)

    Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12prime.

    Existing Instances Defaults64.default_parameters bls12_bedrock2_funcs
    bls12_bedrock2_specs bls12_bedrock2_correctness.
(*  We require that the prime specified here is the same that was used for reification:
    Change names to match reification cache.*)
    Lemma m_eq: bls12prime.m = m.
    Proof.
        unfold m. unfold bls12prime.m. reflexivity.
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
Local Notation bw := (@width (@semantics Defaults64.default_parameters)).
Local Definition m' := @WordByWordMontgomery.m' m Semantics.width.
Notation n := (WordByWordMontgomery.n m bw).
Local Definition eval := @WordByWordMontgomery.eval bw n.
Local Definition valid := @WordByWordMontgomery.valid bw n m.
Local Definition from_mont := @WordByWordMontgomery.from_montgomerymod bw n m m'.
Local Definition valid_words w := valid (List.map Interface.word.unsigned w).
Local Definition map_words := List.map Interface.word.unsigned.
Local Notation r := (WordByWordMontgomery.r bw).
Local Notation r' := (WordByWordMontgomery.r' m bw).

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
    evsnd out = (evfst in1 * evsnd in2 + evfst in1 * evsnd in2) mod m.

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
      [outr; outi; xr; xi; yr; yi; v0; v1; v2], [],
      bedrock_func_body:(
      mul (v0, xr, yr);
      mul (v1, xi, yi);
      sub (outr, v0, v1);
      add (v2, xr, xi);
      add (outi, yr, yi);
      mul (outi, v2, outi);
      sub (outi, outi, v0);
      sub (outi, outi, v1)
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
    ((Bignum n pv0 wold_v0) ) *
    ((Bignum n pv1 wold_v1) ) *
    ((Bignum n pv2 wold_v2) ) *
    (Bignum n poutr wold_outr) * (Bignum n pouti wold_outi))%sep m0 ->
    WeakestPrecondition.call functions ( "Fp2_mul") t m0
    ([pouti; poutr; pxi; pxr; pyi; pyr; pv0; pv1; pv2])
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
        + unfold eval. unfold from_mont. unfold m'.
          assert (bw = width) by reflexivity.
          rewrite <- H12. rewrite Z.add_comm.
          rewrite Prod.fst_pair.
          rewrite Prod.fst_pair.
          rewrite Prod.fst_pair.
          rewrite <- H9. rewrite Z.mod_small.
            * reflexivity.
            * apply WordByWordMontgomery.from_montgomerymod_correct with (r' := r') (m' := m') in H11.
              {
                destruct H11. destruct H13. apply H14.
              }
              all: try reflexivity. simpl.
               cbv [m]. cbv [WordByWordMontgomery.n]. simpl.
               auto. auto with zarith.
        + unfold eval. unfold from_mont. unfold m'.
        assert (bw = width) by reflexivity.
        rewrite <- H12. rewrite Z.add_comm.
        rewrite Prod.snd_pair.
        rewrite Prod.snd_pair.
        rewrite Prod.snd_pair.
        rewrite <- H6. rewrite Z.mod_small.
          * reflexivity.
          * apply WordByWordMontgomery.from_montgomerymod_correct with (r' := r') (m' := m') in H8.
            {
              destruct H8. destruct H13. apply H14.
            }
            all: try reflexivity. simpl.
             cbv [m]. cbv [WordByWordMontgomery.n]. simpl.
             auto. auto with zarith.
Qed.


Theorem Fp2_mul_ok: program_logic_goal_for_function! Fp2_mul.
Proof.
    (*Initializing*)
    straightline_init_with_change. 
    repeat straightline.

    (*first function call*)
    handle_call; [eauto ..|].
    (*Second function call*)
    handle_call; [eauto .. |].
    (*remaining function calls*)
    handle_call; [eauto .. |].
    handle_call; [eauto .. |].
    handle_call; [eauto .. |].
    handle_call; [eauto .. |].
    handle_call; [eauto .. |].
    handle_call; [eauto .. |].
    

    (*Prove postcondition*)
    repeat split; auto. do 3 eexists.
    split.
    2: {  ecancel_assumption. }
    split.
      2: {split; eauto. }
    split.
      - eauto.
      - split; [eauto|]. split.
        + unfold eval. unfold from_mont. unfold m'.
          assert (bw = width) by reflexivity.
          rewrite <- H12. rewrite Z.add_comm.
          rewrite Prod.fst_pair.
          rewrite Prod.fst_pair.
          rewrite Prod.fst_pair.
          rewrite <- H9. rewrite Z.mod_small.
            * reflexivity.
            * apply WordByWordMontgomery.from_montgomerymod_correct with (r' := r') (m' := m') in H11.
              {
                destruct H11. destruct H13. apply H14.
              }
              all: try reflexivity. simpl.
               cbv [m]. cbv [WordByWordMontgomery.n]. simpl.
               auto. auto with zarith.
        + unfold eval. unfold from_mont. unfold m'.
        assert (bw = width) by reflexivity.
        rewrite <- H12. rewrite Z.add_comm.
        rewrite Prod.snd_pair.
        rewrite Prod.snd_pair.
        rewrite Prod.snd_pair.
        rewrite <- H6. rewrite Z.mod_small.
          * reflexivity.
          * apply WordByWordMontgomery.from_montgomerymod_correct with (r' := r') (m' := m') in H8.
            {
              destruct H8. destruct H13. apply H14.
            }
            all: try reflexivity. simpl.
             cbv [m]. cbv [WordByWordMontgomery.n]. simpl.
             auto. auto with zarith.
Qed.