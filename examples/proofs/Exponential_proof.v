Set Implicit Arguments.
Require Import TLC.LibTactics TLC.LibIntTactics.
(* Load the CFML library, with time credits. *)
Require Import CFML.CFLibCredits.
Require Pervasives_ml.
Require Array_ml.
Require Import Pervasives_proof.
Require Import Array_proof.
(* Load the big-O library. *)
Require Import Dominated.
Require Import UltimatelyGreater.
Require Import Monotonic.
Require Import LibZExtra.
(* Load the custom CFML tactics with support for big-Os *)
Require Import CFMLBigO.
Require Import Procrastination.Procrastination.
(* Load the CF definitions. *)
Require Import Exponential_ml.

(* This is kind of ad-hoc... *)
Lemma pow2_sub_1_nonneg :
  forall x,
  0 <= x ->
  0 <= 2^x - 1.
Proof.
  intros. apply Z.le_add_le_sub_r.
  auto with zarith.
Qed.

Hint Resolve pow2_sub_1_nonneg : zarith.

Ltac auto_tilde ::= try solve [ auto with zarith | auto with maths | false; math ].

Lemma f_spec :
  specZ [cost \in_O (fun n => 2 ^ n)]
    (forall (n: int),
      0 <= n ->
      app f [n]
        PRE (\$ (cost n))
        POST (fun (tt:unit) => \[])).
Proof.
  xspecO_refine recursive. intros costf M D g.
  intro n. induction_wf: (downto 0) n. intro N.
  xcf. weaken. xpay. xrets. xif.
  { xret~. }
  { xapp~. xapp~. }
  generalize n N. defer. close_cost.

  exists (fun n => 2^(n+1)-1). split.
  intros. rewrite~ Z.max_r. ring_simplify. rew_pow~ 2 n.
  cleanup_cost. monotonic. dominated.
Qed.

(* Alternatively, follow the substitution method all the way... *)
Lemma f_spec' :
  specZ [cost \in_O (fun n => 2 ^ n)]
    (forall (n: int),
      0 <= n ->
      app f [n]
        PRE (\$ (cost n))
        POST (fun (tt:unit) => \[])).
Proof.
  xspecO_refine recursive. intros costf M D g.
  intros n. induction_wf: (downto 0) n. intro N.
  xcf. weaken. xpay. xrets. xif_guard.
  { xret. hsimpl. }
  { xapp~. xapp~. }
  ring_simplify. generalize n N. defer. close_cost.

  begin defer assuming a b. defer Ha: (0 <= a).
  sets cost: (fun (n:Z_filterType) => a * 2^n + b).
  assert (cost_nonneg: forall n, 0 <= n -> 0 <= cost n).
  { intros n N. unfold cost. rewrite~ <- pow2_ge_1. pols. defer. }

  exists cost. split.
  { intros n N. cases_if; ring_simplify; unfold cost.
    { subst n. ring_simplify. defer. }
    { rew_pow~ 2 (n-1). pols. ring_simplify. (* FIXME: elia *) defer. } }
  cleanup_cost. monotonic. dominated. end defer. elia.
Qed.

Lemma cumul_pow n :
  0 <= n ->
  cumul 0 n (fun i => 2 ^ i) = 2^n - 1.
Proof.
  induction_wf: (downto 0) n.
  unfold cumul. intro. interval_case_r 0 n.
  { intros. cbn. assert (n = 0) as -> by math. cbn. math. }
  { intros. cbn. rewrite List.map_app, Big.big_app. 2: typeclass.
    cbn. unfold cumul in IH. rewrite~ IH. rew_pow~ 2 (n-1). }
Qed.

Lemma loop_spec :
  specZ [cost \in_O (fun n => 2 ^ n)]
    (forall (n:int),
      1 <= n ->
      app loop [n]
        PRE (\$ (cost n))
        POST (fun (tt:unit) => \[])).
Proof.
  xspecO_refine straight_line. intros n Hn. xcf. xpay.
  xfor_inv (fun (i:int) => \[]). math.
  { intros i Hi. xpay. xapp_spec (spec f_spec). math. }
  hsimpl. hsimpl.
  cleanup_cost. monotonic.
  { apply dominated_sum_distr; [| now dominated].
    rewrite dominated_big_sum with (g := (fun i => 2^i)).
    { erewrite dominated_ultimately_le_nonneg; swap 1 2.
      - exists 0. intros. split.
        now apply cumul_nonneg; eauto using Z.pow_nonneg with maths.
        rewrite~ cumul_pow. apply Z.le_refl.
      - dominated. }
    { apply ultimately_gt_ge, filter_universe_alt. intros a.
      rewrite~ <-(cost_nonneg f_spec a). }
    { exists 0. intros. apply~ Z.pow_pos_nonneg. }
    dominated. }
Qed.
