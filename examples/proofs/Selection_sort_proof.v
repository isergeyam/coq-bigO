Set Implicit Arguments.
Require Import TLC.LibTactics.
Require Import TLC.LibListSort.
Require Import TLC.LibListZ.
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
Require Import DominatedNary.
Require Import LimitNary.
Require Import Generic.
(* Load the custom CFML tactics with support for big-Os *)
Require Import CFMLBigO.
(* Load the CF definitions. *)
Require Import Selection_sort_ml.

Lemma swap_spec :
  specO unit_filterType eq
    (fun cost =>
      forall a (xs: list int) i j,
      index xs i -> index xs j ->
      app swap [a i j]
      PRE (\$ cost tt \* a ~> Array xs)
      POST (fun (_:unit) => a ~> Array (xs[i := xs[j]][j := xs[i]])))
    (fun (_:unit) => 1).
Proof.
  xspecO_refine straight_line. introv Ii Ij. xcf. xpay.
  xapps~. xapps~. xapp~. xapp~. apply~ index_update.
  cleanup_cost. monotonic. dominated.
Qed.

Hint Extern 1 (RegisterSpec swap) => Provide (provide_specO swap_spec).

Ltac auto_tilde ::= try solve [ eauto with maths | false; math ].

(* cumul a b (λi. f (b-i))
   = f(b-a) + f(b-(a+1)) + ... + f(b-(b-1))
   = f(b-a) + f(b-(a+1)) + ... + f(1)
   = cumul 1 (b-a+1) (λi. f i)
*)
Lemma cumul_triangle_renumber : forall lo hi f g,
  (forall i, lo <= i -> i < hi -> g i = f (hi - i)) ->
  cumul lo hi g = cumul 1 (hi-lo+1) f.
Proof.
  intros *. induction_wf: (upto hi) lo. intros Hg.
  unfold cumul. interval_case_l lo hi.
  { intros. cbn. rewrite~ interval_empty. }
  { intros. cbn.
    rewrite~ (@interval_cons_r 1 (hi - lo + 1)).
    rewrite List.map_app, Big.big_app. 2: typeclass. cbn.
    unfold cumul, Big.big in IH. rewrite IH. 2: upto. 2: intros; applys~ Hg.
    cbn. rewrite~ Hg.
    ring_simplify (hi - (lo + 1) + 1) (hi - lo + 1 - 1). unfold Big.big. cbn.
    math. }
Qed.

Lemma selection_sort_spec :
  specZ [cost \in_O (fun n => n ^ 2)]
    (forall a (xs : list int),
      1 <= length xs -> (* TODO: generalize the for-loop reasoning rule *)
      app selection_sort [a]
      PRE (\$ cost (length xs) \* a ~> Array xs)
      POST (fun (_:unit) => Hexists (xs' : list int), a ~> Array xs')).
Proof.
  xspecO_refine straight_line. xcf. xpay. xapps~.
  weaken. xfor_inv (fun (_:int) =>
    Hexists (xs':list int), a ~> Array xs' \* \[ length xs = length xs']
  ).
  { math. }
  { intros i Hi. xpull. intros xs' L.
    xpay. xapp. xseq.
    { weaken. xfor_inv (fun (_:int) =>
        Hexists (xs'':list int) (k:int),
        a ~> Array xs'' \* p ~~> k \*
        \[index xs'' k /\ length xs = length xs'']).
      { math. }
      intros j Hj. xpull. intros xs'' k (Hk & L').
      xpay. xapps. xapps~. xapps~. apply~ int_index_prove.
      xif.
      { xapp. hsimpl. splits~. apply~ int_index_prove. }
      { xret. hsimpl. splits~. }
      hsimpl. splits~. apply~ int_index_prove.

      match goal with |- cumul _ _ (fun _ => ?X) <= _ => ring_simplify X end.
      rewrite Z.max_l, Z.add_0_l; autos~. reflexivity. }

    xpull. intros xs'' k (? & ?). xapps. xapps~. apply~ int_index_prove.
    hsimpl. rewrite !LibListZ.length_update; auto.
  }
  hsimpl~. hsimpl.
  sets len_xs: (length xs). rewrite Z.add_0_l. reflexivity.

  eapply cleanup_cost_tagged, cleanup_cost_eq.
  { intro x. unfold costf.
    rewrite cumul_triangle_renumber
      with (lo := 0) (f := fun i => 3 * i + cost swap_spec tt + 1); auto; cycle 1.
    { intros. rewrite~ cumul_const. }
    ring_simplify (x - 2 + 1 - 0 + 1). reflexivity. }

  cleanup_cost.
  { monotonic. }
  { dominated.
    etransitivity. eapply dominated_big_sum_bound'; swap 1 3.
    { repeat apply_nary dominated_sum_distr_nary; dominated.
      apply dominated_reflexive. all: cbn; dominated. }
    1, 2: now ultimately_greater.
    { monotonic. intros ? ? H. destruct~ H. } now limit. now cbn; dominated.
Qed.
