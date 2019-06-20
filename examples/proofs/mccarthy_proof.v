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
Require Import TLC.LibIntTactics.
(* Load the custom CFML tactics with support for big-Os *)
Require Import CFMLBigO.
Require Import Procrastination.Procrastination.
Require Import elia.
(* Load the CF definitions. *)
Require Import Mccarthy_ml.

Require Import PolTac.PolTac.

Ltac case_max :=
  match goal with |- context [Z.max ?n ?m] =>
    destruct (Z.max_spec_le n m) as [(? & ->) | (? & ->)]
  end.

Lemma mcfuel_spec :
  exists (cost : Z -> Z),
  forall fuel n,
  0 <= fuel ->
  0 <= n ->
  cost n < fuel ->
  app mcfuel [fuel n]
  PRE (\$ cost n)
  POST (fun (r:Z) => \[ r = Z.max 91 (n-10) ]).
Proof.
  begin defer assuming cost. exists cost.
  defer cost_nonneg: (forall n, 0 <= cost n).
  intro fuel. induction_wf: (downto 0) fuel. intros.
  weaken. xcf. xpay. xrets. xif.
  { stop_refine. false. specializes cost_nonneg n. math. }
  xif_guard. xrets. math_lia.
  xapps. math. math. math.
  generalize n fuel H0 H C C0 H1. defer.
  asserts_rewrite ((n + 11) - 10 = n + 1); [math|].
  xapps. math. math. math_lia.
  generalize n fuel H H0 H1 C C0. defer.
  hsimpl. rewrite H3. math_lia.
  rew_cost. generalize n H0. defer.

  end defer.
  begin defer assuming a b c.
  exists (fun n => Z.max c (a - b * n)).
  { defer?: (1 <= c).
    repeat split.
    - intros. math_lia.
    - intros.
      rewrite Z.max_lub_lt_iff in *. unpack.
      assert (n < 101) by math_lia. defer?: (0 <= b).
      split.
      { enough (c+1 < fuel) by math. rewrite <-H3.
        enough (c+1 < a - b * 101) by math_nia. defer. }
      { enough (a - b * 112 + 1 < fuel) by math_nia.
        rewrite <-H3.
        enough (a - b * 112 + 1 < a - b * 101) by math_nia.
        defer. }
    - intros. deferred. math_nia.
    - deferred. intros.
      case_if. math_nia.
      assert (n < 101) by math.
      repeat case_max; pols; try first [ false; timeout 1 math_nia | defer | timeout 1 math_nia ].
      pols. assert (90 <= n) as <- by math. defer. }
  end defer.

  exists 407 4 1. math_nia.
Qed.

Lemma mc_spec :
  exists (cost : Z -> Z),
  forall fuel n,
  0 <= fuel ->
  0 <= n ->
  cost n < fuel ->
  app mc [n]
  PRE (\$ cost n)
  POST (fun (r:Z) => \[ r = Z.max 91 (n-10) ]).
Proof.
  begin defer assuming cost. exists cost.
  defer cost_nonneg: (forall n, 0 <= cost n).
  intro fuel. induction_wf: (downto 0) fuel. intros.
  weaken. xcf. xpay. xif_guard. xrets. math_lia.
  specializes cost_nonneg n.
  xapps (fuel - 1). math. math. math.
  generalize n fuel H H0 H1 C. defer.
  asserts_rewrite ((n+11)-10 = n+1); [math|].
  xapps (fuel - 1). math. math. math_lia.
  generalize n fuel H H0 H1 C. defer.
  hsimpl. subst r. math_lia.
  generalize n H0. defer.

  end defer.
  begin defer assuming a b c.
  exists (fun n => Z.max c (a - b * n)).
  { defer?: (1 <= c).
    repeat split.
    - intros. math_lia.
    - intros.
      rewrite Z.max_lub_lt_iff in *. unpack.
      assert (n < 101) by math_lia. defer?: (0 <= b).
      split.
      { enough (c+1 < fuel) by math. rewrite <-H3.
        enough (c+1 < a - b * 101) by math_nia. defer. }
      { enough (a-b*112 + 1 < fuel) by math_nia. rewrite <-H3.
        enough (a-b*112 + 1 < a-b*101) by math_nia. defer. }
    - intros. deferred. math_nia.
    - deferred. intros. case_if. math_nia. assert (n < 101) by math.
      repeat case_max; pols; try first [ false; timeout 1 math_nia | defer | timeout 1 math_nia ].
      pols. assert (90 <= n) as <- by math. defer. }
  end defer.

  exists 407 4 1. math_nia.
Qed.

Lemma mc_spec2 :
  exists (cost variant : Z -> Z),
  forall fuel n,
  0 <= n ->
  variant n < fuel ->
  app mc [n]
  PRE (\$ cost n)
  POST (fun (r:Z) => \[ r = Z.max 91 (n-10) ]).
Proof.
  begin defer assuming cost variant. exists cost variant.
  defer cost_nonneg: (forall n, 0 <= cost n).
  defer variant_nonneg: (forall n, 0 <= variant n).
  intro fuel. induction_wf: (downto 0) fuel. intros.
  weaken. xcf. xpay. xif_guard. xrets. math_lia.
  specializes cost_nonneg n.
  specializes variant_nonneg n.
  xapps (fuel - 1). math. math.
  generalize n fuel H H0 C. defer.
  asserts_rewrite ((n+11)-10 = n+1); [math|].
  xapps (fuel - 1). math. math_lia.
  generalize n fuel H H0 C. defer.
  hsimpl. subst r. math_lia.
  generalize n H. defer.

  end defer.
Abort.

Lemma mc_spec2 :
  exists (cost : Z -> Z),
  forall n,
  0 <= n ->
  app mc [n]
  PRE (\$ cost n)
  POST (fun (r:Z) => \[ r = Z.max 91 (n-10) ]).
Proof.
  (* induction bien fondée sur (101 - n) *)
Abort.
