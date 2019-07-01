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

Lemma bsearch_spec :
  specZ [cost \in_O Z.log2]
    (forall t (xs : list int) (v : int) (i j : int),
        0 <= i <= length xs ->
        0 <= j <= length xs ->
        app bsearch [t v i j]
        PRE (\$ (cost (j - i)) \* t ~> Array xs)
        POST (fun (k:int) => t ~> Array xs)).
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
    intros i j Hn Hi Hj.

    weaken. xcf. xpay.
    (* xif_ifcost / xif_maxcost / xif = celui qui sert le plus souvent *)
    xif_guard as C. { xret~. }
    (* rewrite nle_as_gt in C. *) asserts~ C' : (i < j). clear C.
    xret ;=> Hm. forwards~ Hmbound: middle_inbound Hm.
    xapps. { apply~ int_index_prove. }
    xrets. xif. { xret~. }
    xapps. { apply~ int_index_prove. }
    xif.
    { weaken. xapp~ (m - i). subst m.
      (* tactique xcost? *)
      match goal with |- cost ?x <= _ => ring_simplify x end.
      reflexivity. }
    { (* forwards: IH __ (m+1) j. Focus 2. reflexivity. *)
      weaken. xapp~ (j - (m+1)). subst m. reflexivity. }

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
      tests Hn1: (j-i = 1).
      + rewrite Hn1. cbn. asserts_rewrite~ (n = 1). defer.
      + assert (HH: 2 <= n) by math. rewrite <-Hn.
        generalize n HH. defer. }
  }

  close_cost.

  begin defer assuming a b.
  defer Ha: (0 <= a).
  exists (fun (n:Z_filterType) => If 0 < n then a * Z.log2 n + b else 1).
  repeat split.
  { intros. cases_if~. }
  { intros. cases_if~. rewrite <-Z.log2_nonneg. pols. defer. }
  { cases_if~. cases_if~. simpl. pols. defer. }
  { intros n N. cases_if~; [| now false~]. cases_if~.
    rewrite~ <-(@Zlog2_step n). pols. defer. }

  cleanup_cost.
  { intros x y H. cases_if; case_if~.
    { monotonic. }
    { rewrite <-Z.log2_nonneg. pols. deferred; math. } }
  { transitivity (fun x => a * Z.log2 x + b).
    - apply dominated_ultimately_eq.
      rewrite ZP. exists 1. intros. cases_if~.
    - dominated. }
  end defer. elia.
Qed.
