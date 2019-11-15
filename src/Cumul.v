Require Import TLC.LibTactics.
Require Import ZArith.
Open Scope Z_scope.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Psatz. (* nia *)
Require Import Big.
Require Import TLC.LibLogic.
Require Import TLC.LibWf.

(* A small ad-hoc library of iterated big sums *)

Open Scope list_scope.

Fixpoint seqZ (start : Z) (len : nat) : list Z :=
  match len with
  | 0%nat => nil
  | S len => start :: seqZ (start + 1) len
  end.

Lemma seqZ_S_r : forall len start,
  seqZ start (S len) = seqZ start len ++ (start + Z.of_nat len) :: nil.
Proof.
  induction len.
  { intros. cbn. rewrite~ Z.add_0_r. }
  { intros. cbn. f_equal. cbn in IHlen. rewrite IHlen.
    f_equal. f_equal. lia. }
Qed.

Definition interval (lo hi : Z) : list Z :=
  seqZ lo (Z.to_nat (hi - lo)).

Lemma Z_to_nat_pos_inv : forall x n,
  (0 < n)%nat ->
  Z.to_nat x = n ->
  0 < x.
Proof. intros. destruct x; cbn in *; lia. Qed.

Lemma Z_to_nat_zero_inv : forall x,
  Z.to_nat x = 0%nat ->
  x <= 0.
Proof. intros. destruct x; cbn in *; lia. Qed.

Lemma interval_empty : forall lo hi,
  hi <= lo ->
  interval lo hi = nil.
Proof.
  intros. unfold interval.
  assert (Z.to_nat (hi - lo) = 0%nat) as ->.
  { apply LibInt.to_nat_neg. rewrite LibInt.le_zarith. lia. }
  reflexivity.
Qed.

Lemma interval_cons_l : forall lo hi,
  lo < hi ->
  interval lo hi = lo :: interval (lo + 1) hi.
Proof.
  intros. unfold interval.
  gen_eq d: (Z.to_nat (hi - lo)). intro Hd. destruct d.
  { zify. rewrite Z2Nat.id in *; lia. }
  { symmetry in Hd. forwards~: Z_to_nat_pos_inv Hd. lia.
    cbn. f_equal. f_equal. zify. rewrite Z2Nat.id in *; lia. }
Qed.

Lemma interval_cons_r' : forall lo hi,
  lo <= hi ->
  interval lo (hi + 1) = interval lo hi ++ hi :: nil.
Proof.
  intros. unfold interval.
  gen_eq d: (Z.to_nat (hi - lo)). intro Hd. symmetry in Hd. destruct d.
  { apply Z_to_nat_zero_inv in Hd. cbn.
    assert (hi + 1 - lo = 1) as -> by lia. cbv. f_equal. lia. }
  { set (d' := S d) in *.
    assert (Z.to_nat (hi + 1 - lo) = S d') as ->.
    { zify. rewrite Z2Nat.id in *; lia. }
    rewrite seqZ_S_r. f_equal. f_equal. zify. rewrite Z2Nat.id in *; lia. }
Qed.

Lemma interval_cons_r : forall lo hi,
  lo < hi ->
  interval lo hi = interval lo (hi - 1) ++ (hi - 1) :: nil.
Proof.
  intros. assert (hi = (hi - 1) + 1) as -> by lia.
  rewrite interval_cons_r'. 2: lia. repeat f_equal; lia.
Qed.

Lemma interval_destruct_l : forall lo hi,
  (hi <= lo /\ interval lo hi = nil) \/
  (lo < hi /\ interval lo hi = lo :: interval (lo + 1) hi).
Proof.
  intros. tests~: (hi <= lo).
  { left. splits~. rewrite~ interval_empty. }
  { right. splits~. lia. rewrite~ interval_cons_l. lia. }
Qed.

Lemma interval_destruct_r : forall lo hi,
  (hi <= lo /\ interval lo hi = nil) \/
  (lo < hi /\ interval lo hi = interval lo (hi - 1) ++ (hi - 1) :: nil).
Proof.
  intros. tests~: (hi <= lo).
  { left. splits~. rewrite~ interval_empty. }
  { right. splits~. lia. rewrite~ interval_cons_r. lia. }
Qed.

Ltac interval_case_l lo hi :=
  let H := fresh in
  destruct (interval_destruct_l lo hi) as [[H ->]|[H ->]]; revert H.
Ltac interval_case_r lo hi :=
  let H := fresh in
  destruct (interval_destruct_r lo hi) as [[H ->]|[H ->]]; revert H.

Ltac downto :=
  unfold downto; rewrite ?LibInt.le_zarith, ?LibInt.lt_zarith; try lia.
Ltac upto :=
  unfold upto; rewrite ?LibInt.le_zarith, ?LibInt.lt_zarith; try lia.

Lemma interval_app : forall lo mid hi,
  lo <= mid ->
  mid <= hi ->
  interval lo mid ++ interval mid hi = interval lo hi.
Proof.
  intros lo mid. induction_wf: (upto mid) lo. intros.
  interval_case_l lo mid.
  { intros. rewrite List.app_nil_l. assert (mid = lo) as -> by lia. auto. }
  { intros. rewrite <-List.app_comm_cons, IH; auto; try lia; try upto.
    rewrite~ <-interval_cons_l. lia. }
Qed.

Lemma in_interval_lo :
  forall x lo hi,
  List.In x (interval lo hi) ->
  lo <= x.
Proof.
  intros *. induction_wf: (downto lo) hi.
  interval_case_r lo hi.
  { cbn. tauto. }
  { rewrite List.in_app_iff. cbn. intros ? [?|[?|?]]; try tauto.
    { applys~ IH (hi - 1). downto. } { lia. } }
Qed.

Lemma in_interval_hi :
  forall x lo hi,
  List.In x (interval lo hi) ->
  x < hi.
Proof.
  intros *. induction_wf: (upto hi) lo.
  interval_case_l lo hi.
  { cbn. tauto. }
  { cbn. intros ? [?|?]. lia. applys~ IH (lo + 1). upto. }
Qed.

Lemma big_const_Z :
  forall lo hi c,
  lo <= hi ->
  \big[Z.add]_(_ <- interval lo hi) c = (hi - lo) * c.
Proof.
  intros *. induction_wf: (upto hi) lo.
  interval_case_l lo hi.
  { cbn. nia. }
  { cbn. unfold Big.big in IH. cbn in IH. intros.
    rewrite IH. nia. upto. lia. }
Qed.

Lemma big_zero_Z :
  forall lo hi,
  \big[Z.add]_(_ <- interval lo hi) 0 = 0.
Proof.
  intros *. induction_wf: (upto hi) lo.
  interval_case_l lo hi.
  { cbn. nia. }
  { cbn. unfold Big.big in IH. cbn in IH. intros. rewrite~ IH. upto. }
Qed.

Lemma big_nonneg_Z :
  forall lo hi (f : Z -> Z),
  (forall x, lo <= x -> x < hi -> 0 <= f x) ->
  0 <= \big[Z.add]_(i <- interval lo hi) f i.
Proof.
  intros.
  rewrite <-big_covariant with
    (R := Z.le)
    (f := fun _ => 0);
  try typeclass.
  { rewrite big_zero_Z. lia. }
  { introv HIn. forwards~: in_interval_lo HIn. forwards~: in_interval_hi HIn. }
Qed.

Definition cumul (lo hi : Z) (f : Z -> Z) : Z :=
  \big[Z.add]_(i <- interval lo hi) f i.

Lemma cumulP :
  forall lo hi (f : Z -> Z),
  cumul lo hi f = \big[Z.add]_(i <- interval lo hi) f i.
Proof. reflexivity. Qed.

Lemma cumul_const : forall lo hi c,
  lo <= hi ->
  cumul lo hi (fun _ => c) = (hi - lo) * c.
Proof. apply big_const_Z. Qed.

Lemma cumul_const' : forall lo hi c,
  cumul lo hi (fun _ => c) = (Z.max 0 (hi - lo)) * c.
Proof.
  intros. tests~: (lo <= hi). rewrite~ cumul_const; nia.
  unfold cumul; rewrite~ interval_empty; cbn. nia. lia.
Qed.

Lemma cumul_nonneg : forall lo hi (f: Z -> Z),
  (forall x, lo <= x -> x < hi -> 0 <= f x) ->
  0 <= cumul lo hi f.
Proof.
  intros. rewrite cumulP, <-big_nonneg_Z; auto with zarith.
Qed.

Lemma cumul_split (k : Z) : forall lo hi (f : Z -> Z),
  lo <= k ->
  k <= hi ->
  cumul lo hi f = cumul lo k f + cumul k hi f.
Proof.
  intros. unfold cumul.
  rewrite~ <-(@interval_app lo k hi). rewrite List.map_app, big_app.
  auto. typeclass.
Qed.

Arguments cumul_split k [lo] [hi] f _ _.

Lemma cumul_minus_one : forall f lo hi,
  lo <= hi ->
  cumul lo hi f = (hi - lo) + cumul lo hi (fun x => f x - 1).
Proof.
  intros *. induction_wf: (upto hi) lo.
  unfold cumul. interval_case_l lo hi.
  { intros. cbn. lia. }
  { intros. cbn. unfold cumul, Big.big in IH. rewrite IH.
    2: upto. 2: lia. cbn. lia. }
Qed.

Lemma cumul_cons_l : forall lo hi (f : Z -> Z),
  lo < hi ->
  cumul lo hi f = f lo + cumul (lo + 1) hi f.
Proof. intros. unfold cumul. rewrite~ interval_cons_l. Qed.

Lemma cumul_cons_r : forall lo hi (f : Z -> Z),
  lo < hi ->
  cumul lo hi f = cumul lo (hi - 1) f + f (hi - 1).
Proof.
  intros. unfold cumul. rewrite~ interval_cons_r.
  rewrite~ List.map_app. cbn. rewrite big_app. cbn.
  rewrite Z.add_0_r. reflexivity. typeclass.
Qed.

Lemma cumul_triangle : forall lo hi (f : Z -> Z),
  Z.abs (cumul lo hi f) <= cumul lo hi (fun x => Z.abs (f x)).
Proof.
  intros *. induction_wf: (upto hi) lo. unfold cumul. interval_case_l lo hi.
  { intros. cbn. lia. }
  { intros. cbn. unfold cumul, Big.big in IH. rewrite Z.abs_triangle, IH.
    2: upto. cbn. lia. }
Qed.
