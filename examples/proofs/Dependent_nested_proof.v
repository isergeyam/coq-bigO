Set Implicit Arguments.
Require Import TLC.LibTactics.
(* Load the CFML library, with time credits. *)
Require Import CFML.CFLibCredits.
Require Pervasives_ml.
Require Array_ml.
Require Import Pervasives_proof.
Require Import ArrayCredits_proof.
(* Load the big-O library. *)
Require Import Dominated.
Require Import UltimatelyGreater.
Require Import Monotonic.
Require Import LibZExtra.
(* Load the custom CFML tactics with support for big-Os *)
Require Import CFMLBigO.
(* Load the CF definitions. *)
Require Import Dependent_nested_ml.

Ltac auto_tilde ::= try solve [ auto with maths | false; math ].

Lemma f_spec :
  specZ [cost \in_O (fun n => n^2)]
    (forall n,
       0 <= n -> (* FIXME (need more xfor lemmas) *)
       app f [n]
       PRE (\$ cost n)
       POST (fun (_:unit) => \[])).
Proof.
  xspecO_refine straight_line. intros n N. xcf.
  xpay. xfor_inv (fun (_:int) => \[]). math.
  { intros i Hi.
    xpay. xfor_inv (fun (_:int) => \[]). math.
    intros j Hj. xpay. xret~. hsimpl. hsimpl. }
  hsimpl. hsimpl.

  cleanup_cost.
  { eapply monotonic_sum; [| now monotonic]. eapply monotonic_cumul_Z.
    intros. rewrite~ <-cumul_nonneg. }
  dominated.
  rewrite dominated_big_sum_bound.
  2: now repeat ultimately_greater.
  { setoid_rewrite Z.pow_2_r. dominated.
    rewrite dominated_big_sum_bound. dominated. ultimately_greater.
    apply~ filter_universe_alt. monotonic. }
  { apply filter_universe_alt.
    eauto using monotonic_after_of_monotonic with monotonic zarith. }
Qed.
