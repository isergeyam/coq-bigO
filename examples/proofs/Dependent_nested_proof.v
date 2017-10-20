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
Require Import Tmp.
(* Load the custom CFML tactics with support for big-Os *)
Require Import CFMLBigO.
Require Import EvarsFacts.
(* Load the CF definitions. *)
Require Import Dependent_nested_ml.

Ltac auto_tilde ::= try solve [ auto with maths | false; math ].

Hypothesis pay1 : forall B (F : ~~B) (H: hprop) (Q: B -> hprop) c,
  F (\$ max0 c \* H) Q -> F (\$ max0 (1 + c) \* H) Q.

Lemma f_spec :
  specZ [cost \in_O (fun n => n^2)]
    (forall n,
       0 <= n -> (* FIXME (need more xfor lemmas) *)
       app f [n]
       PRE (\$ cost n)
       POST (fun (_:unit) => \[])).
Proof.
  xspecO. intros n N. xcf. xpay.
  xfor_inv (fun (_:int) => \[]). math.
  { intros i Hi. apply pay1.
    xfor_inv (fun (_:int) => \[]). math.
    intros j Hj. apply pay1. xret. hsimpl. hsimpl.
    simpl. clean_max0. rewrite Z.add_0_r. reflexivity.
    hsimpl. }
  hsimpl.
  simpl.
  assert (L: forall f g a b, f = g -> cumul a b f = cumul a b g) by admit. (* FIXME *)
  erewrite L; swap 1 2. extens. intro i.
  rewrite max0_eq; [| admit]. reflexivity. reflexivity.
  hsimpl.

  cleanup_cost.
  admit. (* TODO *)

  dominated. apply dominated_max0.
  rewrite dominated_big_sum_bound.
  { eapply dominated_eq_r; swap 1 2.
    { intros a. rewrite (Z.pow_2_r a). reflexivity. }
    dominated. eapply dominated_eq_l; swap 1 2.
    intro.
    hide_evars_then ltac:(fun _ => rewrite cumulP; rewrite big_const_Z; ring_simplify).
    reflexivity. reflexivity. }
  ultimately_greater. apply~ filter_universe_alt.
  apply filter_universe_alt. monotonic. admit.
Qed.