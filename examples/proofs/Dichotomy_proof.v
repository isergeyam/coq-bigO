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
Require Import Procrastination.Procrastination.
Require Import elia.
(* Load the CF definitions. *)
Require Import Dichotomy_ml.

Require Import Sorted.

Ltac auto_tilde ::= try solve [ auto with maths | false; math ].

Lemma middle_inbound : forall i j m,
  0 <= i < j ->
  m = i + (j - i `/` 2) ->
  i <= m < j.
Proof.
  introv [Hi Hij] ->. split.
  { pols. apply~ Z.quot_pos. }
  { forwards~: Z.quot_lt (j-i) 2. }
Qed.

Lemma half_pos : forall n,
  2 <= n ->
  0 < n `/` 2.
Proof.
  intros n N. forwards~ H: Z.quot_le_mono 2 n 2.
  rewrite~ Z.quot_same in H.
Qed.

Hint Resolve half_pos.

Definition bsearch_correct (xs: list int) v i j k :=
     (k = -1 /\ forall p, i <= p < j -> xs[p] <> v)
  \/ (i <= k < j /\ xs[k] = v).

Lemma bsearch_correct_oob xs v i j :
  j <= i ->
  bsearch_correct xs v i j (-1).
Proof. intros. left~. Qed.

Hint Resolve bsearch_correct_oob.

Lemma bsearch_correct_found xs v i j k :
  i <= k < j ->
  v = xs[k] ->
  bsearch_correct xs v i j k.
Proof. intros. right~. Qed.

Hint Resolve bsearch_correct_found.

Lemma sort_read : forall l,
  LocallySorted Z.le l ->
  forall i j,
  0 <= i ->
  i <= j ->
  j < length l ->
  l[i] <= l[j].
Proof.
  induction 1.
  { intros. false. rew_list in *. math. }
  { intros. rew_list in *. rew_array. repeat case_if~. }
  { intros. rew_list in *. rew_array.
    case_if.
    { case_if~. case_if~.
      transitivity b. auto.
      specializes IHLocallySorted 0 (j-1) __ __ __.
      rew_array in *. case_if~. case_if~. }
    { case_if~.
      { case_if~. case_if~.
        specializes IHLocallySorted 0 (j-1) __ __ __.
        rew_array in *. repeat case_if~. }
      { case_if~. case_if~.
        specializes IHLocallySorted (i-1) (j-1) __ __ __.
        rew_array in *. repeat case_if~. } } }
Qed.

Lemma bsearch_correct_recurse_l xs v i j j' k :
  LocallySorted Z.le xs ->
  0 <= i -> j <= length xs ->
  i <= j' < j ->
  v < xs[j'] ->
  bsearch_correct xs v i j' k ->
  bsearch_correct xs v i j k.
Proof.
  intros S Hi Hj Hij Hv C.
  assert (Hsort: forall p, j' <= p < j -> v < xs[p]).
  { intros. forwards~: sort_read xs j' p. }
  destruct C as [(-> & C)|(Hk & C)].
  { left~. split~. intros.
    specializes C p. specializes Hsort p.
    tests: (p < j'). specializes~ C __. specializes~ Hsort __; autos~. }
  { right~. }
Qed.

Lemma bsearch_correct_recurse_r xs v i i' j k :
  LocallySorted Z.le xs ->
  0 <= i -> j <= length xs ->
  i <= i' < j ->
  xs[i'] < v ->
  bsearch_correct xs v (i'+1) j k ->
  bsearch_correct xs v i j k.
Proof.
  intros S Hi Hj Hij Hv C.
  assert (Hsort: forall p, i <= p <= i' -> xs[p] < v).
  { intros. forwards~: sort_read xs p i'. }
  destruct C as [(-> & C)|(Hk & C)].
  { left~. split~. intros.
    tests: (p <= i'). { specializes Hsort p __. }
    specializes C p __. }
  { right~.  }
Qed.

Lemma bsearch_spec :
  specZ [cost \in_O Z.log2]
    (forall t (xs : list int) (v : int) (i j : int),
        LocallySorted Z.le xs ->
        0 <= i <= length xs ->
        0 <= j <= length xs ->
        app bsearch [t v i j]
        PRE (\$ (cost (j - i)) \* t ~> Array xs)
        POST (fun (k:int) =>
                t ~> Array xs \*
                \[ bsearch_correct xs v i j k ])).
Proof.
  begin defer assuming a b.
  defer Ha: (0 <= a).

  sets cost: (fun (n:Z_filterType) => If 0 < n then a * Z.log2 n + b else 1).
  asserts cost_nonneg: (forall x, 0 <= cost x).
  { intro x. subst cost; simpl. case_if~.
    rewrite <-Z.log2_nonneg. ring_simplify. defer.
  }
  asserts costPpos: (forall n, 0 < n -> cost n = a * Z.log2 n + b).
  { intro n. subst cost; simpl. case_if~. }
  asserts costPneg: (forall n, n <= 0 -> cost n = 1).
  { intro n. subst cost; simpl. case_if~. }

  asserts cost_monotonic: (monotonic Z.le Z.le cost).
  { intros x y H. subst cost; simpl.
    case_if; case_if~.
    { monotonic. }
    { rewrite <-Z.log2_nonneg. ring_simplify. defer. } }

  { xspecO cost.
    introv. gen_eq n: (j-i). gen i j. induction_wf IH: (downto 0) n.
    intros i j Hn Hxs Hi Hj.

    weaken. xcf. xpay.
    (* xif_ifcost / xif_maxcost / xif = celui qui sert le plus souvent *)
    xif_guard as C. { xret~. }

    (* rewrite nle_as_gt in C. *) asserts~ C' : (i < j). clear C.
    xret ;=> Hm. forwards~ Hmbound: middle_inbound Hm.
    xapps. { apply~ int_index_prove. }
    xrets. xif. { xret~. }
    xapps. { apply~ int_index_prove. }
    xif.
    { weaken. xapp~ (m - i).
      hsimpl. applys~ bsearch_correct_recurse_l m.
      subst m.
      (* tactique xcost? *)
      match goal with |- cost ?x <= _ => ring_simplify x end.
      reflexivity. }
    { (* forwards: IH __ (m+1) j. Focus 2. reflexivity. *)
      weaken. xapp~ (j - (m+1)).
      hsimpl. applys~ bsearch_correct_recurse_r m.
      subst m. reflexivity. }

    cases_if; ring_simplify.
    { rewrite~ costPneg. }
    { rewrite (Z.max_r 0); [| auto with zarith].
      rewrite Z.max_l; swap 1 2.
      { apply cost_monotonic. forwards~: Zquot_mul_2 (j-i). }
      tests Hn1: (j - i = 1).
      + rewrite Hn1. cbn. rewrite~ (costPneg 0). rewrite~ (costPpos n).
        rewrite <-Z.log2_nonneg. ring_simplify. defer.
      + rewrite~ costPpos. rewrite~ costPpos.
        rewrite <-Hn. rewrite~ <-(@Zlog2_step n). pols. defer.
    }

    assumption.
    { unfold cost. transitivity (fun x => a * Z.log2 x + b).
      - apply dominated_ultimately_eq.
        rewrite ZP. exists 1. intros. cases_if~.
      - dominated. }
  }
  end defer. elia.
Qed.

Lemma bsearch_spec2 :
  specZ [cost \in_O Z.log2]
    (forall t (xs : list int) (v : int) (i j : int),
        0 <= i <= length xs ->
        0 <= j <= length xs ->
        app bsearch [t v i j]
        PRE (\$ (cost (j - i)) \* t ~> Array xs)
        POST (fun (k:int) => t ~> Array xs)).
Proof.
  xspecO_refine recursive. intros costf M D ?.
  { introv. gen_eq n: (j-i). gen i j. induction_wf IH: (downto 0) n.
    intros i j Hn Hi Hj.

    weaken. xcf. xpay.
    (* xif_ifcost / xif_maxcost / xif = celui qui sert le plus souvent *)
    xif_guard as C. { xret~. }
    (* rewrite nle_as_gt in C. *) asserts~ C' : (i < j). clear C.
    xret ;=> Hm. forwards~: middle_inbound Hm.
    xapps. { apply~ int_index_prove. }
    xrets. xif. { xret~. }
    xapps. { apply~ int_index_prove. }
    xif.
    { weaken. xapp~ (m - i). subst m. rewrite Z.add_simpl_l.
      reflexivity. }
    { (* forwards: IH __ (m+1) j. Focus 2. reflexivity. *)
      weaken. xapp~ (j - (m+1)). subst m. reflexivity. }

    rew_cost.
    cases_if; ring_simplify.
    { assert (HH: n <= 0) by math. generalize n HH. defer. }
    { defer ?: (forall n, 0 <= costf n).
      rewrite (Z.max_r 0); [| auto with zarith].
      rewrite Z.max_l; swap 1 2.
      { apply M. forwards~: Zquot_mul_2 (j-i). }
      assert (HH: 1 <= n) by math. rewrite <-Hn.
      generalize n HH. defer. } }

  close_cost.

  begin defer assuming a b c.
  exists (fun (n:Z_filterType) => If 0 < n then a * Z.log2 n + b else c).
  repeat split.
  { intros. cases_if~. defer. }
  { intros. deferred;=>. cases_if~. rewrite <-Z.log2_nonneg. pols. all: defer. }
  { intros n N. tests: (n = 1).
    { repeat cases_if~. cbn. pols. defer. }
    { cases_if~; [| now false~]. cases_if~. rewrite~ <-(@Zlog2_step n). pols.
      defer. } }

  cleanup_cost.
  { intros x y H. cases_if; case_if~.
    { deferred. monotonic. }
    { rewrite <-Z.log2_nonneg. 2: now deferred. pols. deferred; math. } }
  { transitivity (fun x => a * Z.log2 x + b).
    - apply dominated_ultimately_eq.
      rewrite ZP. exists 1. intros. cases_if~.
    - dominated. }
  end defer. elia. (* a = 3, b = 4, c = 1 *)
Qed.

Ltac r2l := credr2l; apply pred_incl_refl.

Require Import ssreflect.

Lemma bsearch_spec_explicit :
  forall t (xs : list int) (v : int) (i j : int),
    0 <= i <= length xs ->
    0 <= j <= length xs ->
    app bsearch [t v i j]
    PRE (\$ (If j <= i then 1 else 3 * Z.log2 (j - i) + 4) \* t ~> Array xs)
    POST (fun (k:int) => t ~> Array xs).
Proof.
    introv. gen_eq n: (j-i). gen i j. induction_wf IH: (downto 0) n.
    intros i j Hn Hi Hj.
    xcf. xpay. r2l.
    xif as C.
    { xret~. case_if~. rewrite credits_join_eq. hsimpl. rewrite le_zarith. pols. math. }
    asserts~ C': (i < j). clear C. case_if~.
    xret;=> Hm. forwards~: middle_inbound Hm.
    xapps. { apply~ int_index_prove. } r2l.
    xrets. xif.
    { xret~. rewrite !credits_join_eq. hsimpl. rewrite le_zarith. pols.
      rewrite -Z.log2_nonneg //. }
    xapps. { apply~ int_index_prove. } r2l.
    rewrite !credits_join_eq. match goal with |- context [ \$ ?x ] => ring_simplify x end.
    xif.
    { xapp~ (m - i). hsimpl_credits. rewrite le_zarith.
      apply Zle_minus_le_0. rewrite Hm. rewrite Z.add_simpl_l.
      tests Hn1: (j-i=1).
      + rewrite Hn1. cbn. rewrite Z.add_0_r. case_if~. rewrite -Z.log2_nonneg //.
      + assert (HH: 2 <= n) by math. case_if~. { exfalso. forwards~: half_pos (j-i). }
        rewrite -Hn. rewrite -(@Zlog2_step n) //. math. }
    { xapp~ (j - (m+1)). hsimpl_credits. rewrite le_zarith.
      apply Zle_minus_le_0. rewrite Hm.
      tests Hn1: (j-i=1).
      + rewrite Hn1. cbn. case_if~. rewrite -Z.log2_nonneg //.
      + assert (HH: 2 <= n) by math. rewrite -Hm. case_if. now rewrite -Z.log2_nonneg //.
        pols. rewrite Hm. forwards~: Zquot_mul_2 (j-i).
        rewrite -(@Zlog2_step n) //. rewrite Hn. pols.
        apply~ Z.mul_le_mono_nonneg_l. apply Z.log2_le_mono. math. }
Qed.
