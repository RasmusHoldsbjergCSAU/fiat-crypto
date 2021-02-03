Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.WordByWordMontgomery.
Local Open Scope Z_scope.

Local Definition m := 2^256 - 2^224 + 2^192 + 2^96 - 1.
Local Definition machine_wordsize := 64.
Local Definition prefix := "p256_"%string. (* placed before function names *)

Instance names : names_of_operations.
  make_names_of_operations prefix. Defined.

Definition ops : wbwmontgomery_reified_ops m machine_wordsize.
  make_reified_ops. Time Defined.

Instance p256_bedrock2_funcs : bedrock2_wbwmontgomery_funcs.
funcs_from_ops ops. Defined.

Instance p256_bedrock2_specs : bedrock2_wbwmontgomery_specs.
specs_from_ops ops m. Defined.

Instance p256_bedrock2_correctness : bedrock2_wbwmontgomery_correctness.
prove_correctness ops m machine_wordsize. Defined.


Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.NotationsInConstr.
Require Import bedrock2.Syntax.
Local Open Scope bedrock_expr.
Coercion expr.var : string >-> Syntax.expr.


Eval cbv [add p256_bedrock2_funcs] in add.
Check add.
Eval cbv [add p256_bedrock2_funcs] in add.
About bedrock_func.
Check bedrock_func.
Eval cbv [spec_of_add p256_bedrock2_specs] in spec_of_add.
About Bignum.

Check add.
Eval compute in add.

Require Import Znat.

Import Syntax BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Local Coercion literal (z : Z) : expr := expr.literal z.
Local Coercion var (x : string) : Syntax.expr := Syntax.expr.var x.
Local Coercion name_of_func (f : function) := fst f.

Definition addF : func :=
  let px := "px" in
  let py := "py" in
  let pout := "pout" in
  ("addF", ([px; py; pout], ([]:list String.string), bedrock_func_body:(
                         add(pout, px, py)
                         ))).


From bedrock2 Require Import Semantics BasicC64Semantics WeakestPrecondition ProgramLogic.
From coqutil Require Import Word.Properties Word.Interface Tactics.letexists.

About WordByWordMontgomery.WordByWordMontgomery.valid.

Check cmd.

Eval compute in Semantics.width.

Instance spec_of_addF : spec_of "addF" := fun functions =>
forall (wx wy : list Interface.word.rep)
  (px py pout : Interface.word.rep)
  (wold_out : list Interface.word.rep) (t : Semantics.trace)
  (m0 : Interface.map.rep) (Rx Ry Rout : Interface.map.rep -> Prop),
WordByWordMontgomery.WordByWordMontgomery.valid Semantics.width
  (WordByWordMontgomery.n m Semantics.width) m
  (List.map Interface.word.unsigned wx) /\
WordByWordMontgomery.WordByWordMontgomery.valid Semantics.width
  (WordByWordMontgomery.n m Semantics.width) m
  (List.map Interface.word.unsigned wy) ->
Separation.sep
  (Bignum.Bignum (WordByWordMontgomery.n m Semantics.width) px wx) Rx
  m0 ->
Separation.sep
  (Bignum.Bignum (WordByWordMontgomery.n m Semantics.width) py wy) Ry
  m0 ->
Separation.sep
  (Bignum.Bignum (WordByWordMontgomery.n m Semantics.width) pout
     wold_out) Rout m0 ->
WeakestPrecondition.call functions "addF" t m0
  (pout :: px :: py :: nil)
  (fun (t' : Semantics.trace) (m' : Interface.map.rep)
     (rets : list Interface.word.rep) =>
   t = t' /\
   rets = nil /\
   (exists wout : list Interface.word.rep,
      Separation.sep
        (Separation.sep
           (Separation.emp
              (WordByWordMontgomery.WordByWordMontgomery.eval
                 Semantics.width
                 (WordByWordMontgomery.WordByWordMontgomery.from_montgomerymod
                    Semantics.width
                    (WordByWordMontgomery.n m Semantics.width) m
                    (WordByWordMontgomery.m' m Semantics.width)
                    (List.map Interface.word.unsigned wout)) mod m =
               (WordByWordMontgomery.WordByWordMontgomery.eval
                  Semantics.width
                  (WordByWordMontgomery.WordByWordMontgomery.from_montgomerymod
                     Semantics.width
                     (WordByWordMontgomery.n m Semantics.width) m
                     (WordByWordMontgomery.m' m Semantics.width)
                     (List.map Interface.word.unsigned wx)) +
                WordByWordMontgomery.WordByWordMontgomery.eval
                  Semantics.width
                  (WordByWordMontgomery.WordByWordMontgomery.from_montgomerymod
                     Semantics.width
                     (WordByWordMontgomery.n m Semantics.width) m
                     (WordByWordMontgomery.m' m Semantics.width)
                     (List.map Interface.word.unsigned wy))) mod m /\
               WordByWordMontgomery.WordByWordMontgomery.valid
                 Semantics.width
                 (WordByWordMontgomery.n m Semantics.width) m
                 (List.map Interface.word.unsigned wout)))
           (Bignum.Bignum (WordByWordMontgomery.n m Semantics.width)
              pout wout)) Rout m')).


Definition sum5_twice : func :=
  let ret := "ret" in
  let s := "s" in
  ("sum5_twice", ([], ([ret]:list String.string), bedrock_func_body:(
                         ret = 0;
                         unpack! s = sum5();
                         ret = ret + s;
                         ret = ret + s
                         ))).