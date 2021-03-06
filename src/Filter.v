Require Import Coq.Logic.Classical_Pred_Type.
Require Import TLC.LibTactics.
Require Import TLC.LibAxioms.
Require Import TLC.LibLogic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import ssreflect.
Require Import LibRewrite.
Require Import ZArith Reals.
Require Import Psatz.

(* We could in principle perform this construction using [bool] instead of [Prop]
   as the codomain of predicates. However, [bool] does not support quantification
   over an infinite set, whereas [Prop] does. *)

Notation pred A := (A -> Prop) (only parsing).

(* ---------------------------------------------------------------------------- *)

Module Filter.

(* Technically, a filter is a nonempty set of subsets of A, which is
   closed under inclusion and (finite) intersection. *)

Definition filter A := pred (pred A).

Record mixin_of (A : Type) := Mixin {

(* Let us write [ultimately] for a filter.  A filter is a modality: if [P] is a
   predicate, then [ultimately P] is a proposition. In other words, a filter is
   a quantifier: if [P] is a predicate, then [ultimately (fun x => P x)] is a
   proposition. Intuitively, this proposition means that ``ultimately'' [P]
   holds. In other words, for every sufficiently ''large'' [x], [P] holds. *)

  ultimately : filter A;

(* A filter is nonempty. In fact, it contains the universe. In other words,
   [ultimately x => True] is just [True]. Thus, the quantifier [ultimately]
   is weaker than a universal quantifier: [forall x, P x] implies
   [ultimately x, P x]. *)

  _ :
    ultimately (fun _ => True);

(* A filter is closed by inclusion and by (finite) intersection. In other
   words, the quantifier [ultimately] is covariant and commutes with (finite)
   conjunction. The last condition means that [ultimately] is universal in
   nature, as opposed to existential. In particular, the universal quantifier
   can be viewed as a filter, but the existential quantifier cannot. *)

  _ :
    forall P1 P2 P : pred A,
    ultimately P1 ->
    ultimately P2 ->
    (forall a, P1 a -> P2 a -> P a) ->
    ultimately P
}.

Notation class_of := mixin_of (only parsing).

Section ClassDef.
  Record type : Type := Pack { sort : Type ; class : class_of sort }.
End ClassDef.

Module Exports.
  Coercion sort : type >-> Sortclass.
  Notation filterType := type.
  Notation FilterMixin := Mixin.
  Notation FilterType T m := (@Pack T m).
End Exports.

End Filter.
Export Filter.Exports.

Definition ultimately T := Filter.ultimately (Filter.class T).
Arguments ultimately : clear implicits.

(* ---------------------------------------------------------------------------- *)

Section FilterLaws.

Variable A : filterType.

Implicit Type P : pred A.

(* Re-statement of the defining laws. *)

Lemma filter_universe:
  ultimately A (fun _ => True).
Proof. destruct A as [? M]. destruct M. eauto. Qed.

Lemma filter_closed_under_intersection:
  forall P1 P2 P,
  ultimately A P1 ->
  ultimately A P2 ->
  (forall a, P1 a -> P2 a -> P a) ->
  ultimately A P.
Proof. destruct A as [? M]. destruct M. eauto. Qed.

(* A filter is closed by subset inclusion.
   That is, [ultimately] is covariant. *)

Lemma filter_closed_under_inclusion:
  forall P1 P2,
  ultimately A P1 ->
  (forall a, P1 a -> P2 a) ->
  ultimately A P2.
Proof.
  eauto using filter_closed_under_intersection.
Qed.

(* If [P] holds everywhere, then [ultimately P] holds. *)

Lemma filter_universe_alt:
  forall P,
  (forall a, P a) ->
  ultimately A P.
Proof.
  (* A filter is nonempty, so it has one inhabitant. *)
  pose filter_universe.
  (* A filter is closed by inclusion, so the universe is also
     an inhabitant of the filter. *)
  eauto using filter_closed_under_inclusion.
Qed.

(* [ultimately] commutes with conjunction. *)

Lemma filter_conj:
  forall P1 P2,
  ultimately A P1 /\ ultimately A P2 <-> ultimately A (fun x => P1 x /\ P2 x).
Proof.
  intros P1 P2. split.
  { intros [ h1 h2 ].
    apply (filter_closed_under_intersection h1 h2).
    tauto. }
  { intros h. split;
    apply (filter_closed_under_inclusion h);
    tauto. }
Qed.

Lemma filter_conj_alt :
  forall P1 P2,
    ultimately A P1 ->
    ultimately A P2 ->
    ultimately A (fun x => P1 x /\ P2 x).
Proof. intros. apply filter_conj. tauto. Qed.

(* An existential quantifier can be pushed into [ultimately]. That is,
   [exists/ultimately] implies [ultimately/exists]. The converse is false; to
   see this, replace [ultimately] with [forall], which is one possible
   interpretation of [ultimately]. *)

Lemma ultimately_exists:
  forall B (Q : A -> pred B),
  (exists y, ultimately A (fun x => Q x y)) ->
  ultimately A (fun x => exists y, Q x y).
Proof.
  intros B Q [ y HQ ].
  eapply filter_closed_under_inclusion.
  { exact HQ. }
  simpl. intros. exists y. assumption.
Qed.

(* [ultimately] can be pushed into a universal quantifier. That is,
   [ultimately/forall] implies [forall/ultimately]. The converse is false:
   for instance, on the natural numbers, [forall x, [ultimately y, x <= y]]
   obviously holds, whereas [ultimately y, forall x, x <= y] does not.
   A fortiori, two [ultimately] quantifiers do not in general commute. *)

Lemma forall_ultimately:
  forall B (Q : B -> pred A),
  ultimately A (fun y => forall x, Q x y) ->
  forall x, ultimately A (fun y => Q x y).
Proof.
  intros. eapply filter_closed_under_inclusion; eauto.
Qed.

End FilterLaws.

(* TEMPORARY define rewriting-rule versions of these laws? *)

(* Instance for rewriting under [ultimately] *)

Program Instance Pw_eq_ultimately_proper (A : filterType) :
  Proper (pw eq ==> Basics.flip Basics.impl) (ultimately A).
Next Obligation.
  intros. unfold respectful, pointwise_relation, Basics.flip, Basics.impl.
  intros P1 P2 H U. apply (filter_closed_under_inclusion U).
  intros. rewrite H. assumption.
Qed.

(* ---------------------------------------------------------------------------- *)
(* A set of tactics useful to intersect an arbitrary number of filters.

   [filter_intersect] turns a goal of the form:

     ultimately A P1 -> ... ultimately A Pn -> Q

   into:

     ultimately A (P1 /\ ... /\ Pn) -> Q



   [filter_closed_under_intersection] turns a goal of the form:

     ultimately A P1 -> ... ultimately A Pn -> ultimately A P

   into:

     forall x, P1 x /\ ... /\ Pn x -> P
 *)

Ltac filter_intersect_two_base I U1 U2 :=
  lets I: filter_conj_alt U1 U2.

Ltac filter_intersect_two :=
  let U1 := fresh in
  let U2 := fresh in
  let U := fresh in
  intros U1 U2;
  filter_intersect_two_base U U1 U2;
  revert U; clear U1; clear U2.

Ltac filter_intersect :=
  match goal with
  | |- (ultimately ?A _) -> (ultimately ?A _) -> _ =>
    let U := fresh in
    intro U;
    filter_intersect;
    revert U;
    filter_intersect_two
  | |- (ultimately ?A _) -> (ultimately ?B _) -> _ =>
    idtac
  | |- (ultimately _ _) -> _ =>
    idtac
  end.

Ltac filter_closed_under_intersection :=
  filter_intersect;
  let U := fresh in
  intro U;
  applys filter_closed_under_inclusion U;
  clear U.

(* Test goals *)

Goal
  forall A P1 P2 P3 B P4 P5,
  (ultimately A (fun x => P1 x /\ P2 x /\ P3 x) -> ultimately B P4 -> ultimately B P5 -> False) ->
  ultimately A P1 ->
  ultimately A P2 ->
  ultimately A P3 ->
  ultimately B P4 ->
  ultimately B P5 ->
  False.
Proof.
  do 8 intro.
  filter_intersect.
  assumption.
Qed.

Goal
  forall (A: filterType) (P1 P2 P3 P4 : A -> Prop),
  (forall x, (P1 x /\ P2 x /\ P3 x) -> P4 x) ->
  ultimately A P1 ->
  ultimately A P2 ->
  ultimately A P3 ->
  ultimately A P4.
Proof.
  do 6 intro.
  filter_closed_under_intersection.
  assumption.
Abort.

(* ---------------------------------------------------------------------------- *)

(* Inclusion of filters. *)

Definition finer A (ult1 ult2 : Filter.filter A) :=
  forall P, ult2 P -> ult1 P.

(* ---------------------------------------------------------------------------- *)

(* Applying a function [f] to a filter [ult] produces another filter, known as
   the image of [ult] under [f]. *)

Section Image.

  Variable A : filterType.
  Variable B : Type.

  Variable f : A -> B.

  Definition image : Filter.filter B :=
    fun P => ultimately A (fun x => P (f x)).

  Definition image_filterMixin : Filter.mixin_of B.
  Proof.
    eapply Filter.Mixin with image.
    { apply filter_universe. }
    { intros P1 P2 P I1 I2 H.
      unfold image in *.
      apply (filter_closed_under_intersection I1 I2).
      eauto. }
  Defined.

  Definition image_filterType :=
    FilterType B image_filterMixin.

End Image.
Arguments image A [B] f P.
Arguments image_filterType A [B] f.

Lemma imageP :
  forall (A : filterType) B (f : A -> B),
  forall (P: B -> Prop),
  ultimately (image_filterType A f) P =
  ultimately A (fun x => P (f x)).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------- *)

(* The filter [on Q] represents validity everywhere in the set [Q].
   In other words, [on Q P] holds if and only if [Q] implies [P]. *)

Section On.

Variable A : Type.

Variable Q : pred A.

Definition on : Filter.filter A :=
  fun P => forall x, Q x -> P x.

Definition on_filterMixin : Filter.mixin_of A.
Proof.
  eapply Filter.Mixin with on; unfold on; eauto.
Defined.

Definition on_filterType := FilterType A on_filterMixin.

Goal ultimately on_filterType = on.
Proof. reflexivity. Qed.

Lemma onP:
  forall P : pred A,
  ultimately on_filterType P =
  forall x, Q x -> P x.
Proof. reflexivity. Qed.

End On.

(* ---------------------------------------------------------------------------- *)
(* As an instance of [on_filterType], the filter of positive elements on Z. *)

Definition positive_filterType : filterType := on_filterType (Z.le 0).

Lemma positiveP:
  forall P : pred Z,
  ultimately positive_filterType P =
  forall x, (0 <= x)%Z -> P x.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------- *)

(* The singleton set that contains just the set [A] is a filter. We call this
   modality [everywhere]. *)

Section FilterEverywhere.

Variable A : Type.

Definition everywhere_filterMixin : Filter.mixin_of A.
Proof.
  eapply Filter.Mixin with
    (fun (P: A -> Prop) => forall a, P a); eauto.
Defined.

Definition everywhere_filterType := FilterType A everywhere_filterMixin.

End FilterEverywhere.

Lemma everywhereP A :
  forall (P : A -> Prop),
  ultimately (everywhere_filterType A) P =
  forall a, P a.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------- *)

(* A filter on [unit], as an instance of [everywhere]. *)

Definition unit_filterType := everywhere_filterType unit.

Lemma unitP :
  forall (P : unit -> Prop), ultimately unit_filterType P = P tt.
Proof.
  intro P.
  assert (H: ultimately unit_filterType P = (forall tt, P tt)) by reflexivity.
  rewrite H.
  apply prop_ext. splits; auto. intros ? x. dependent inversion x. assumption.
Qed.

(* ---------------------------------------------------------------------------- *)

(* The filter of all subsets that contain a particular value [x]. For a property
   to hold on [singleton x], it only needs to hold on [x]. *)

Section Singleton.

Variable A : Type.
Variable x : A.

Definition singleton_filterMixin : Filter.mixin_of A.
Proof.
  eapply Filter.Mixin with (fun P => P x); eauto.
Defined.

Definition singleton_filterType := FilterType A singleton_filterMixin.

Lemma singletonP :
  forall (P : A -> Prop),
  ultimately singleton_filterType P =
  P x.
Proof. reflexivity. Qed.

End Singleton.

(* ---------------------------------------------------------------------------- *)

Section Order.

Variable A : Type.
Variable le : A -> A -> Prop.
Hypothesis IA : Inhab A.
Hypothesis upper_bound : forall x y : A, exists z, le x z /\ le y z.
Hypothesis le_trans : forall x y z, le x y -> le y z -> le x z.

Definition order : Filter.filter A :=
  fun P => exists x0, forall x, le x0 x -> P x.

Definition order_filterMixin : Filter.mixin_of A.
Proof.
  eapply Filter.Mixin with order.
  - unfold order. exists arbitrary. eauto.
  - introv [x1 H1] [x2 H2] HH. destruct (upper_bound x1 x2) as (z & Hz1 & Hz2).
    exists z. intros. eauto 10 using le_trans.
Defined.

Definition order_filterType := FilterType A order_filterMixin.

Lemma orderP :
  forall (P : A -> Prop),
  ultimately order_filterType P =
  exists x0, forall x, le x0 x -> P x.
Proof. reflexivity. Qed.

End Order.

(* ---------------------------------------------------------------------------- *)

(* The standard filter on [nat]. *)

Definition nat_filterMixin : Filter.mixin_of nat.
Proof.
  eapply Filter.Mixin with
    (fun (P: nat -> Prop) => exists n0, forall n, le n0 n -> P n).
  - exists 0%nat. eauto with arith.
  - { introv [n0 H0] [n1 H1] H. exists (max n0 n1).
      intros n ?. apply H.
      - apply H0. lia.
      - apply H1. lia. }
Defined.

Definition nat_filterType := FilterType nat nat_filterMixin.

Lemma natP :
  forall (P : nat -> Prop),
  ultimately nat_filterType P =
  exists n0, forall n, le n0 n -> P n.
Proof. reflexivity. Qed.

Lemma ultimately_ge_nat (n0: nat) :
  ultimately nat_filterType (fun n => le n0 n).
Proof.
  rewrite natP. exists n0. eauto.
Qed.

Lemma natP_ultimately (cond : nat -> Prop) :
  forall (P : nat -> Prop),
  ultimately nat_filterType cond ->
  ultimately nat_filterType P =
  exists x0, cond x0 /\ forall x, le x0 x -> P x.
Proof.
  intros P Ucond. rewrite natP. rewrite natP in Ucond.
  destruct Ucond as (ncond & Hcond).
  apply prop_ext. split.
  { intros [n0 H]. exists (max ncond n0). splits.
    - apply Hcond. lia.
    - intros. apply H. lia. }
  { intros (n0 & lo_le_n0 & H). eauto. }
Qed.

Arguments natP_ultimately [cond] [P] _.

(* ---------------------------------------------------------------------------- *)

(* The standard filter on [Z]. *)

Definition Z_filterMixin : Filter.mixin_of Z.
Proof.
  eapply Filter.Mixin with
    (fun (P: Z -> Prop) => exists n0, forall n, Z.le n0 n -> P n).
  - exists 0%Z. eauto with arith.
  - { introv [n0 H0] [n1 H1] H. exists (Z.max n0 n1).
      intros n ?. apply H.
      - apply H0. lia.
      - apply H1. lia. }
Defined.

Definition Z_filterType := FilterType Z Z_filterMixin.

Lemma ZP :
  forall (P : Z -> Prop),
  ultimately Z_filterType P =
  exists n0, forall n, Z.le n0 n -> P n.
Proof. reflexivity. Qed.

Lemma ultimately_ge_Z (x0: Z) :
  ultimately Z_filterType (fun x => Z.le x0 x).
Proof.
  rewrite ZP. exists x0. eauto.
Qed.

Lemma ZP_ultimately (cond : Z -> Prop) :
  forall (P : Z -> Prop),
  ultimately Z_filterType cond ->
  ultimately Z_filterType P =
  exists x0, cond x0 /\ forall x, Z.le x0 x -> P x.
Proof.
  intros P Ucond. rewrite ZP. rewrite ZP in Ucond.
  destruct Ucond as (ncond & Hcond).
  apply prop_ext. split.
  { intros [n0 H]. exists (Z.max ncond n0). splits.
    - apply Hcond. lia.
    - intros. apply H. lia. }
  { intros (n0 & lo_le_n0 & H). eauto. }
Qed.

Arguments ZP_ultimately [cond] [P] _.

Definition Zshift (x0 : Z) : Z -> Z :=
  fun x => (x0 + x)%Z.

Lemma Zshift_inv (x0 : Z) :
  forall x, Zshift (- x0) (Zshift x0 x) = x.
Proof.
  unfold Zshift. intros. omega.
Qed.

Lemma ZshiftP (x0 : Z) :
  forall P,
  ultimately Z_filterType (fun x => P (Zshift x0 x)) =
  ultimately Z_filterType P.
Proof.
  intros. apply prop_ext.
  split; do 2 rewrite ZP; intros (x1 & H1); unfold Zshift in *.
  { exists (x1 + x0)%Z. intros.
    assert (HH: n = (x0 + (n - x0))%Z) by lia. rewrite HH.
    apply H1. lia. }
  { exists (x1 - x0)%Z. intros. apply H1. lia. }
Qed.

(* ---------------------------------------------------------------------------- *)

(* The standard filter on [R]. *)

Definition R_filterMixin : Filter.mixin_of R.
Proof.
  eapply Filter.Mixin with
    (fun (P: R -> Prop) => exists x0, forall x, Rle x0 x -> P x).
  - exists 0%R. eauto with arith.
  - { introv [x0 H0] [x1 H1] H. exists (Rmax x0 x1).
      intros x ?. apply H.
      - apply H0. lets: Rmax_l x0 x1. lra.
      - apply H1. lets: Rmax_r x0 x1. lra. }
Defined.

Definition R_filterType := FilterType R R_filterMixin.

Lemma RP :
  forall (P : R -> Prop),
  ultimately R_filterType P =
  exists x0, forall x, Rle x0 x -> P x.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------- *)

(* The product of two filters. *)

(* The members of the product filter are all subsets [P] which contain a product
   [P1] * [P2], where [P1] and [P2] are members of the left-hand and right-hand
   filters, respectively. *)

(* This is a symmetric notion of product. It is *not* the same as writing
   [ultimately A1 (fun a1 => ultimately A2 (fun a2 => P (a1, a2)))], which is
   dissymmetric.

   The symmetric product implies the dissymetric ones, but the converse is
   false. For example, if P (x, y) = (x <= y), then
   [ultimately (fun x => ultimately (fun y => P (x, y)))] is true, but not
   [ultimately P].
*)

Section FilterProduct.

Variable A1 A2 : filterType.

Definition product : Filter.filter (A1 * A2) :=
  fun P =>
    exists P1 P2,
    ultimately A1 P1 /\ ultimately A2 P2 /\
    forall a1 a2, P1 a1 -> P2 a2 -> P (a1, a2).

Definition product_filterMixin : Filter.mixin_of (A1 * A2).
Proof.
  eapply Filter.Mixin with product.
  { do 2 (eexists (fun _ => True)).
    repeat split; apply filter_universe. }
  { intros P Q R.
    intros (P1 & P2 & uP1 & uP2 & ?).
    intros (Q1 & Q2 & uQ1 & uQ2 & ?).
    intros HH.
    exists (fun a1 => P1 a1 /\ Q1 a1).
    exists (fun a2 => P2 a2 /\ Q2 a2).
    repeat split; try (apply filter_conj; eauto).
    intuition eauto. }
Defined.

Definition product_filterType :=
  FilterType (A1 * A2) product_filterMixin.

End FilterProduct.

Arguments product : clear implicits.

Lemma productP :
  forall (A1 A2 : filterType) P,
  ultimately (product_filterType A1 A2) P =
  (exists P1 P2,
   ultimately A1 P1 /\
   ultimately A2 P2 /\
   (forall a1 a2, P1 a1 -> P2 a2 -> P (a1, a2))).
Proof. reflexivity. Qed.

Definition fswap (A1 A2 B : Type) (f: A1 * A2 -> B) : A2 * A1 -> B :=
  fun '(x, y) => f (y, x).

Lemma product_fswap :
  forall (A1 A2 : filterType) P,
  ultimately (product_filterType A1 A2) P <->
  ultimately (product_filterType A2 A1) (fswap P).
Proof.
  intros. do 2 rewrite productP.
  split; introv (P1 & P2 & UP1 & UP2 & HP); exists P2 P1; unfold fswap in *; splits~.
Qed.

Definition liftl (A1 A2 B : Type) (f: A1 -> B) : A1 * A2 -> B * A2 :=
  fun '(x, y) => (f x, y).

Definition liftr (A1 A2 B : Type) (f: A2 -> B) : A1 * A2 -> A1 * B :=
  fun '(x, y) => (x, f y).

(* Symmetric product implies both dissymetric products. *)

Lemma product_dissym_l :
  forall (A1 A2 : filterType) P,
  ultimately (product_filterType A1 A2) P ->
  ultimately A1 (fun x => ultimately A2 (fun y => P (x, y))).
Proof.
  introv UP. rewrite productP in UP.
  destruct UP as (P1 & P2 & UP1 & UP2 & HP).
  revert UP1; filter_closed_under_intersection. introv P1a.
  revert UP2; filter_closed_under_intersection. introv P2a.
  apply HP; eauto.
Qed.

Lemma product_dissym_r :
  forall (A1 A2 : filterType) P,
  ultimately (product_filterType A1 A2) P ->
  ultimately A2 (fun y => ultimately A1 (fun x => P (x, y))).
Proof.
  introv UP.
  forwards UP': proj1 product_fswap UP.
  apply (product_dissym_l UP').
Qed.

(* Disprove some facts about [product] that may seem true. *)

(* Dissymetric products do not imply symmetric product.
   Symmetric product is strictly stronger than dissymetric products. *)

Lemma product_counter_example_1 :
  (forall (A1 A2 : filterType) P,
   (forall x, ultimately A2 (fun y => P (x, y))) ->
   (forall y, ultimately A1 (fun x => P (x, y))) ->
   ultimately (product_filterType A1 A2) P) ->
  False.
Proof.
  intro H.
  specializes H nat_filterType nat_filterType
    (fun '(x, y) => x < y \/ y < x).
  simpl in H.
  specializes H ___.
  { intro x. rewrite natP. exists (x+1). intros. lia. }
  { intro y. rewrite natP. exists (y+1). intros. lia. }
  rewrite productP in H. destruct H as (P1 & P2 & UP1 & UP2 & HP).
  rewrite natP in UP1, UP2. destruct UP1 as (x0 & HP1). destruct UP2 as (y0 & HP2).

  destruct (Nat.le_gt_cases x0 y0).
  { specializes HP y0 y0 ___. lia. }
  { specializes HP x0 x0 ___. apply HP2. lia. lia. }
Qed.

Lemma product_counter_example_2 :
  (forall (A1 A2 : filterType) P,
   ultimately A1 (fun x => ultimately A2 (fun y => P (x, y))) ->
   ultimately A2 (fun y => ultimately A1 (fun x => P (x, y))) ->
   ultimately (product_filterType A1 A2) P) ->
  False.
Proof.
  intro H.
  apply product_counter_example_1.
  introv H1 H2.
  apply H; apply filter_universe_alt; auto.
Qed.

(* Similarly, one cannot prove a property on a product filter by proving it
   component-by-component. *)
Goal
  (forall (A1 A2 : filterType) P Q,
   ultimately A1 (fun x =>
     ultimately A2 (fun y => P (x, y)) ->
     ultimately A2 (fun y => Q (x, y))) ->
   ultimately (product_filterType A1 A2) P ->
   ultimately (product_filterType A1 A2) Q) ->
  False.
Proof.
  intro H.
  specializes H Z_filterType Z_filterType
    (fun (_: Z * Z) => True)
    (fun '(x, y) => Z.le x y).
  simpl in H.
  specializes H ___.
  { rewrite ZP. exists 0%Z. intros.
    rewrite ZP. exists n. eauto. }
  { apply filter_universe. }
  rewrite productP in H. destruct H as (P1 & P2 & UP1 & UP2 & HP).
  rewrite ZP in UP1, UP2. destruct UP1 as (x0 & HP1). destruct UP2 as (y0 & HP2).

  destruct (Z.le_gt_cases x0 y0).
  { specializes HP (y0 + 1)%Z y0 ___.
    apply HP1. lia. apply HP2. lia.
    lia. }
  { specializes HP x0 y0 ___.
    apply HP1. lia. apply HP2. lia.
    lia. }
Qed.

(* ---------------------------------------------------------------------------- *)

Section FilterOr.

Variable A : Type.
Variable F1 F2 : Filter.mixin_of A.

Definition or : Filter.filter A :=
  fun P =>
    exists P1 P2,
    ultimately (FilterType A F1) P1 /\ ultimately (FilterType A F2) P2 /\
    (forall a, P1 a \/ P2 a -> P a).

Definition or_filterMixin : Filter.mixin_of A.
Proof.
  eapply Filter.Mixin with or.
  { do 2 (eexists (fun _ => True)).
    repeat split; apply filter_universe. }
  { intros P Q R.
    intros (P1 & P2 & uP1 & uP2 & HP).
    intros (Q1 & Q2 & uQ1 & uQ2 & HQ).
    intros HH.
    exists (fun a1 => P1 a1 /\ Q1 a1).
    exists (fun a2 => P2 a2 /\ Q2 a2).
    repeat split; try apply filter_conj; eauto.
    intros a [[? ?]|[? ?]]; apply HH; eauto. }
Defined.

Definition or_filterType :=
  FilterType A or_filterMixin.

End FilterOr.

Section FilterOrP.

Variable A1 A2 : filterType.

Definition orp : Filter.filter (A1 * A2) :=
  fun P =>
    exists P1 P2,
    ultimately A1 P1 /\ ultimately A2 P2 /\
    (forall a1 a2, P1 a1 -> P (a1, a2)) /\
    (forall a1 a2, P2 a2 -> P (a1, a2)).

Definition orp_filterMixin : Filter.mixin_of (A1 * A2).
Proof.
  eapply Filter.Mixin with orp.
  { do 2 (eexists (fun _ => True)).
    repeat split; apply filter_universe. }
  { intros P Q R.
    intros (P1 & P2 & uP1 & uP2 & HP1 & HP2).
    intros (Q1 & Q2 & uQ1 & uQ2 & HQ1 & HQ2).
    intros HH.
    exists (fun a1 => P1 a1 /\ Q1 a1).
    exists (fun a2 => P2 a2 /\ Q2 a2).
    repeat split; try apply filter_conj; eauto.
    all: intros; unpack; eauto. }
Defined.

Definition orp_filterType :=
  FilterType (A1 * A2) orp_filterMixin.

End FilterOrP.

Lemma orp_equiv_or_product : forall (A1 A2: filterType) P,
  ultimately (orp_filterType A1 A2) P <->
  ultimately
    (@or_filterType (A1 * A2)
       (product_filterMixin (everywhere_filterType A1) A2)
       (product_filterMixin A1 (everywhere_filterType A2)))
    P.
Proof.
  intros. split.
  { intros (P1 & P2 & uP1 & uP2 & H1 & H2). cbn. unfold or.
    eexists (fun '(_, a2) => P2 a2).
    eexists (fun '(a1, _) => P1 a1). cbn. repeat split.
    - exists (fun _:A1 => True) P2. repeat split; eauto.
    - exists P1 (fun _:A2 => True). repeat split; eauto.
    - intros [? ?] [?|?]; eauto. }
  { intros (P1 & P2 & uP1 & uP2 & HH).
    rewrite -/(product_filterType (everywhere_filterType A1) A2) in uP1.
    rewrite -/(product_filterType A1 (everywhere_filterType A2)) in uP2.
    cbn in HH, P1, P2. cbn. unfold orp.
    exists (fun a1 => forall a2, P2 (a1, a2)).
    exists (fun a2 => forall a1, P1 (a1, a2)). repeat split; eauto.
    { destruct uP2 as (P21 & P22 & U21 & U22 & H2).
      rewrite everywhereP in U22. revert U21.
      filter_closed_under_intersection. eauto. }
    { destruct uP1 as (P11 & P12 & U11 & U12 & H1).
      rewrite everywhereP in U11. revert U12.
      filter_closed_under_intersection. eauto. } }
Qed.

(* ---------------------------------------------------------------------------- *)

Section FilterAsymProduct.

Variable A1 A2 : filterType.

Definition asymproduct : Filter.filter (A1 * A2) :=
  fun P => ultimately A1 (fun a1 => ultimately A2 (fun a2 => P (a1, a2))).

Definition asymproduct_filterMixin : Filter.mixin_of (A1 * A2).
Proof.
  eapply Filter.Mixin with asymproduct.
  { repeat (apply filter_universe_alt; intro). trivial. }
  { intros P Q R H1 H2 HH.
    revert H1 H2. unfold asymproduct. filter_closed_under_intersection.
    intro. intros [H1 H2]. revert H1 H2. filter_closed_under_intersection.
    intro. intros [? ?]. eauto. }
Defined.

Definition asymproduct_filterType :=
  FilterType (A1 * A2) asymproduct_filterMixin.

End FilterAsymProduct.

Arguments asymproduct : clear implicits.

Lemma asymproductP :
  forall (A1 A2 : filterType) P,
  ultimately (asymproduct_filterType A1 A2) P =
  ultimately A1 (fun a1 => ultimately A2 (fun a2 => P (a1, a2))).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------- *)

(* The dual of [ultimately] is [often]. Whereas [ultimately x, P x] intuitively
   means that, once [x] is large enough, [P x] holds always, [often x, P x]
   means that it is not the case that, once [x] is large enough, [P x] is false
   always. In other words, [often x, P x] means that there exist arbitrarily
   large [x]'s such that [P x] holds. We use the positive formulation as a
   definition. The fact this is equivalent to the doubly-negated form can be
   proved by exploiting the principle of excluded middle. *)

Section Often.

Variable A : filterType.

Implicit Type P Q : pred A.

Definition often P :=
  forall Q, ultimately A Q -> exists a, P a /\ Q a.

Lemma often_characterization:
  forall P,
  ~ ultimately A (fun x => ~ P x) <-> often P.
Proof.
  unfold often. split.

  (* Left-to-right implication. *) {
  (* Reductio ad absurdum. If there did not exist [a] that satisfies [P /\ Q],
     then [~ (P /\ Q)] would hold everywhere. *)
  intros oftenP Q ultQ.
  apply not_all_not_ex. intros nPQ.
  (* Thus, [~ (P /\ Q)] would hold ultimately. *)
  specialize (filter_universe_alt nPQ). intro nPQ'.
  (* However, by hypothesis, [Q] holds ultimately. By combining these facts,
     we find that [~P] holds ultimately. *)
  assert (ultimately A (fun a => ~ P a)).
  { eapply filter_closed_under_intersection.
    - exact ultQ.
    - exact nPQ'.
    - eauto. }
  (* This contradicts the hypothesis [~ ultimately ~ P]. *)
  tauto. }

  (* Right-to-left implication. *)
  { intros H unP. destruct (H _ unP). tauto. }
Qed.

(* TEMPORARY the definition of [often] looks like a [limit] assertion. Is it one?
   Is there a connection? *)

End Often.

Arguments often : clear implicits.

(* ---------------------------------------------------------------------------- *)

Section InvImage.
  Variable A : Type.
  Variable B : filterType.

  Variable f : A -> B.

  Definition invimage : Filter.filter A :=
    fun P => exists Q,
        ultimately B Q /\
        (forall a, Q (f a) -> P a).

  Definition invimage_filterMixin : Filter.mixin_of A.
  Proof.
    eapply Filter.Mixin with invimage.
    { unfold invimage. exists (fun _:B => True).
      eauto using filter_universe_alt. }
    { intros P1 P2 P [Q1 [UQ1 I1]] [Q2 [UQ2 I2]] HH. unfold invimage.
      exists (fun b => Q1 b /\ Q2 b). split.
      revert UQ1 UQ2; filter_closed_under_intersection; eauto.
      intros a [? ?]. eauto. }
  Defined.

  Definition invimage_filterType := FilterType A invimage_filterMixin.

End InvImage.

Arguments invimage : clear implicits.
Arguments invimage_filterType : clear implicits.

Lemma invimageP : forall A B f P,
  ultimately (invimage_filterType A B f) P =
  (exists Q, ultimately B Q /\ (forall a, Q (f a) -> P a)).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------- *)

Section Within.

(* If we have a filter on [A], and if [P] is a subset of [A], then [within P] is
   also a filter on [A]. By definition, a formula [Q] is ultimately holds within
   [P] if and only if [P -> Q] is ultimately true. *)

Variable A : filterType.

Variable P : pred A.

Definition within : Filter.filter A :=
  fun Q => ultimately A (fun x => P x -> Q x).

Definition within_filterMixin : Filter.mixin_of A.
Proof.
  eapply Filter.Mixin with within.
  { apply filter_universe_alt. tauto. }
  { intros Q1 Q2 Q hPQ1 hPQ2 ?.
    eapply filter_closed_under_intersection.
    - exact hPQ1.
    - exact hPQ2.
    - eauto. }
Defined.

Definition within_filterType := FilterType A within_filterMixin.

Goal ultimately within_filterType = within.
Proof. reflexivity. Qed.

End Within.

Arguments within : clear implicits.
Arguments within_filterType : clear implicits.

Lemma withinP:
  forall (A : filterType) (P : A -> Prop),
  forall Q,
  ultimately (within_filterType A P) Q =
  ultimately A (fun x => P x -> Q x).
Proof. reflexivity. Qed.

Lemma within_finer :
  forall (A : filterType) P,
  finer (ultimately (within_filterType A P)) (ultimately A) .
Proof.
  introv. unfold finer. intros Q. rewrite withinP.
  filter_closed_under_intersection. tauto.
Qed.

(* ---------------------------------------------------------------------------- *)

Definition measure {A} (m: A -> Z) : Filter.filter A :=
  invimage A Z_filterType m.

Definition measure_filterType {A} (m: A -> Z) :=
  invimage_filterType A Z_filterType m.

Lemma measureP : forall A (m: A -> Z) P,
  ultimately (measure_filterType m) P =
  exists x0, forall x, (x0 <= m x)%Z -> P x.
Proof.
  intros. apply prop_ext. cbn. unfold invimage.
  split; intros H.
  - destruct H as [Q [HQ H]]. rewrite ZP in HQ.
    destruct HQ as [x0 H0]. exists x0. auto.
  - destruct H as [x0 H0]. exists (fun x => x0 <= x)%Z.
    rewrite ZP. eauto.
Qed.
