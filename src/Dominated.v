Require Import TLC.LibTactics.

Require Import Coq.Logic.Classical_Pred_Type.
Require Export ZArith.
Open Scope Z_scope.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Psatz. (* nia *)
Require Export Filter.
Require Export Limit.
Require Import Big.
Require Export Cumul.
Require Export LibFunOrd.
Require Import LibRewrite.
Require Import BigEnough.
Require Import Monotonic.
Require Import TLC.LibAxioms.
Require Import TLC.LibLogic.
Require Import TLC.LibWf.

(* -------------------------------------------------------------------------- *)

(* If we have a filter on [A], then we can define a domination relation between
   functions of type [A -> Z]. *)

(* In principle, we could consider functions of type [A -> B], where [B] is an
   integral domain (see ssrnum.v). The (relative) integers form an integral
   domain; so do the reals. *)

(* [dominated f g] holds if and only if, for some constant [c], [f x] is
   ultimately bounded (in norm) by [c * g x]. *)

Section Domination.

Implicit Types A : filterType.

Definition dominated A (f g : A -> Z) :=
  exists c, ultimately A (fun x => Z.abs (f x) <= c * Z.abs (g x)).

Arguments dominated : clear implicits.

(* This notion is analogous to [is_domin] in Coquelicot. *)

(* -------------------------------------------------------------------------- *)
(* Alternative definition, equivalent to [dominated]. *)

Definition dominatedU A (f g : A -> Z) :=
  ultimately Z_filterType (fun c =>
    ultimately A (fun x => Z.abs (f x) <= c * Z.abs (g x))).

Arguments dominatedU : clear implicits.

Lemma dominated_eq_dominatedU A f g :
  dominated A f g <-> dominatedU A f g.
Proof.
  split.
  { intros [c U]. exists c. intros c' Hc'. revert U.
    filter_closed_under_intersection. intros. nia. }
  { intros [c U]. exists c. eauto with zarith. }
Qed.

(* -------------------------------------------------------------------------- *)

Lemma dominated_finer A (F1 F2: Filter.mixin_of A) (f g : A -> Z) :
  finer (Filter.ultimately F1) (Filter.ultimately F2) ->
  dominated (FilterType A F2) f g ->
  dominated (FilterType A F1) f g.
Proof. intros HF [c U]. exists c. now apply HF. Qed.

(* -------------------------------------------------------------------------- *)

(* The multiplicative constant of [dominated] can always be assumed to be
   non-negative.
*)

Lemma dominated_nonneg_const A f g :
  dominated A f g ->
  exists c, (0 <= c) /\ ultimately A (fun x => Z.abs (f x) <= c * Z.abs (g x)).
Proof.
  intros (c & U).
  destruct (Z.neg_nonneg_cases c) as [c_neg | c_nonneg].
  - exists 0. splits; [ omega |].
    revert U; filter_closed_under_intersection.
    intros. nia.
  - eauto.
Qed.

(* Domination is reflexive. *)

Lemma dominated_reflexive A f :
  dominated A f f.
Proof.
  exists 1. auto using filter_universe_alt with zarith.
Qed.

(* Domination is transitive. *)

Lemma dominated_transitive A f g h :
  dominated A f g -> dominated A g h -> dominated A f h.
Proof.
  intros D1 D2.
  forwards (c1 & c1P & U1): dominated_nonneg_const D1.
  forwards (c2 & c2P & U2): dominated_nonneg_const D2.
  exists (c1 * c2).
  apply (filter_closed_under_intersection U1 U2).
  intros. nia.
Qed.

(* Pointwise equality implies domination. *)

Lemma dominated_eq A f f' :
  (forall a, f a = f' a) ->
  dominated A f f'.
Proof.
  introv H. exists 1. apply filter_universe_alt.
  intros. rewrite H. auto with zarith.
Qed.

Lemma dominated_eq_l A f f' g :
  dominated A f g ->
  (forall a, f a = f' a) ->
  dominated A f' g.
Proof.
  introv D E. eapply dominated_transitive; [| eapply D].
  apply dominated_eq. auto.
Qed.

Lemma dominated_eq_r A f g g' :
  dominated A f g ->
  (forall a, g a = g' a) ->
  dominated A f g'.
Proof.
  introv D E. eapply dominated_transitive; [eapply D |].
  apply dominated_eq. auto.
Qed.

(* Asymptotic pointwise equality implies domination.

   This comes in handy to "patch" non-asymptotic parts of a function that appear
   in a [dominated] goal, typically so that it has nicer properties.

   For example, this allows to change a goal

     [dominated _ f g]

   into

     [dominated _ (fun x => max 0 (f x)) g]

   when f is ultimately nonnegative. Now [fun x => max 0 (f x)] is always
   nonnegative, which may be more convenient to handle.
*)

Lemma dominated_ultimately_eq A f f' :
  ultimately A (fun x => f x = f' x) ->
  dominated A f f'.
Proof.
  introv U.
  exists 1. revert U; filter_closed_under_intersection.
  intros. lia.
Qed.

(* Pointwise inequality implies domination. *)

Lemma dominated_le A f g :
  (forall x, Z.abs (f x) <= Z.abs (g x)) ->
  dominated A f g.
Proof.
  exists 1. apply filter_universe_alt. eauto with zarith.
Qed.

Lemma dominated_le_nonneg A f g :
  (forall x, 0 <= f x <= g x) ->
  dominated A f g.
Proof.
  intros H. exists 1. apply filter_universe_alt. intros a.
  specialize (H a). nia.
Qed.

(* Asymptotic pointwise inequality implies domination. *)

Lemma dominated_ultimately_le A f g :
  ultimately A (fun x => Z.abs (f x) <= Z.abs (g x)) ->
  dominated A f g.
Proof.
  intros U. exists 1.
  apply (filter_closed_under_inclusion U).
  eauto with zarith.
Qed.

Lemma dominated_ultimately_le_nonneg A f g :
  ultimately A (fun x => 0 <= f x <= g x) ->
  dominated A f g.
Proof.
  intros U. apply dominated_ultimately_le. revert U.
  filter_closed_under_intersection. intros. lia.
Qed.

End Domination.

Arguments dominated : clear implicits.

(******************************************************************************)
(* Setoid instances to rewrite with/under dominated.

   We came up with this by trial and error; it is sketchy and should probably be
   improved. *)

Add Parametric Relation (A : filterType) : (A -> Z) (dominated A)
  reflexivity proved by (@dominated_reflexive A)
  transitivity proved by (@dominated_transitive A)
  as dominated_preorder.

Program Instance Eq_dominated_subrelation (A : filterType) :
  subrelation (pw eq) (dominated A).
Next Obligation.
  intros ? f g H. apply dominated_eq. apply H.
Qed.

Program Instance Eq_flip_dominated_subrelation (A : filterType) :
  subrelation (Basics.flip (pw eq)) (dominated A).
Next Obligation.
  intros ? f g H. unfold pw, Basics.flip in H. apply dominated_eq. eauto.
Qed.

(*?*)
Program Instance Pw_eq_dominated_proper (A : filterType) :
  Proper (pw eq ==> pw eq ==> Basics.flip Basics.impl) (dominated A).
Next Obligation.
  intros. unfold respectful, pointwise_relation, Basics.flip, Basics.impl.
  intros f g H f' g' H' D.
  eapply dominated_transitive. apply (dominated_eq H).
  eapply dominated_transitive. apply D. apply dominated_eq. auto.
Qed.

(*
Program Instance Le_dominated_subrelation (A : filterType) :
  subrelation (pw Z.le) (dominated A).
Next Obligation. Admitted.
*)

(*
Program Instance Pw_eq_subrelation_eq (A B : Type) :
  subrelation (@pointwise_relation A B eq) eq.
Next Obligation. Admitted.

Goal forall (A:filterType), subrelation eq (dominated A).
  typeclasses eauto.
Qed.

Goal forall A B, subrelation (@pointwise_relation A B eq) eq.
  typeclasses eauto.
Qed.
*)

(* Program Instance Subrelation_transitive (A : Type) : Transitive (@subrelation A). *)
(* Next Obligation. apply subrelation_transitive. Qed. *)

(* Hint Resolve subrelation_transitive : typeclass_instances. *)

(*
Goal forall (A:filterType), subrelation (@pointwise_relation _ _ eq) (dominated A).
  typeclasses eauto.
Qed.

Goal forall (A:filterType), subrelation (Basics.flip (@pointwise_relation _ _ eq)) (dominated A).
  typeclasses eauto.
Qed.
*)

Hint Rewrite Z.add_0_r : myhints.

Goal dominated Z_filterType (fun x => (x+0)+0) (fun x => x).
  dup.
  { setoid_rewrite Z.add_0_r. admit. }
  rewrite_strat (topdown (hints myhints)).
  apply dominated_reflexive.
Abort.

Goal dominated Z_filterType (fun x => x) (fun x => x+0).
  setoid_rewrite Z.add_0_r.
  apply dominated_reflexive.
Qed.

(*
Goal forall a b, a <= b -> dominated Z_filterType (fun x => x + a) (fun x => x + b).
  intros a b H.
  setoid_rewrite H.
  apply dominated_reflexive.
Qed.
*)

(******************************************************************************)

Section DominatedLaws.

Implicit Types A : filterType.

(* 0 is dominated by any function *)

Lemma dominated_zero A f :
  dominated A (fun _ : A => 0) f.
Proof.
  exists 0. apply filter_universe_alt. intros. nia.
Qed.

(* A constant is dominated by any other non-zero constant. *)

Lemma dominated_cst A c1 c2 :
  c2 <> 0 ->
  dominated A (fun _ => c1) (fun _ => c2).
Proof.
  intros.
  exists (Z.abs (c1 * c2)).
  apply filter_universe_alt. intros. nia.
Qed.

(* A constant is dominated by any function going to infinity. *)

Lemma dominated_cst_limit A c g :
  limit A Z_filterType g ->
  dominated A (fun _ => c) g.
Proof.
  introv L. rewrite limitP in L.
  forwards Ugbig: L (fun x => Z.abs c <= x). { apply ultimately_ge_Z. }
  exists 1. revert Ugbig. filter_closed_under_intersection.
  intros; lia.
Qed.

Lemma dominated_cst_id c :
  dominated Z_filterType (fun _ => c) (fun x => x).
Proof.
  exists 1. exists (Z.abs c). intros; lia.
Qed.

(* Domination is compatible with mul. *)

Lemma dominated_mul A f1 f2 g1 g2 :
  dominated A f1 g1 ->
  dominated A f2 g2 ->
  dominated A (fun x => (f1 x) * (f2 x)) (fun x => (g1 x) * (g2 x)).
Proof.
  intros D1 D2.
  forwards (c1 & c1_pos & U1): dominated_nonneg_const D1.
  forwards (c2 & c2_pos & U2): dominated_nonneg_const D2.
  exists (c1 * c2).
  revert U1 U2; filter_closed_under_intersection.
  intros. rewrite !Z.abs_mul. nia.
Qed.

(* As a corollary, domination is compatible with multiplying by constants. *)

Lemma dominated_mul_cst A c1 c2 f g :
  c2 <> 0 ->
  dominated A f g ->
  dominated A (fun x => c1 * (f x)) (fun x => c2 * (g x)).
Proof.
  intros c2_nz D.
  equates 1 2. applys~ dominated_mul (fun (_:A) => c1) f (fun (_:A) => c2) g.
  applys~ dominated_cst. auto. auto.
Qed.

Lemma dominated_mul_cst_l_1 A c f g :
  dominated A f g ->
  dominated A (fun x => c * (f x)) g.
Proof.
  intros D. rewrite <-dominated_eq with (f' := g).
  applys dominated_mul_cst 1 D. omega.
  auto with zarith.
Qed.

Lemma dominated_mul_cst_l_2 A c f g :
  dominated A f g ->
  dominated A (fun x => (f x) * c) g.
Proof.
  intros D. eapply dominated_eq_l. applys dominated_mul_cst_l_1 D.
  intros. rewrite Z.mul_comm. reflexivity.
Qed.

Lemma dominated_mul_cst_r_1 A c f g :
  dominated A f g ->
  c <> 0 ->
  dominated A f (fun x => c * (g x)).
Proof.
  intros D NZ. rewrite dominated_eq.
  applys dominated_mul_cst 1 D. assumption.
  auto with zarith.
Qed.

Lemma dominated_mul_cst_r_2 A c f g :
  dominated A f g ->
  c <> 0 ->
  dominated A f (fun x => (g x) * c).
Proof.
  intros D NZ. rewrite dominated_eq_r; swap 1 2. applys dominated_mul_cst_r_1 D.
  apply NZ. apply dominated_reflexive. intros. simpl. rewrite Z.mul_comm. reflexivity.
  (* TODO: cleanup *)
Qed.

(* Dominated is compatible with max. *)

Lemma dominated_max A f1 f2 g1 g2 :
  ultimately A (fun x => 0 <= g1 x) ->
  ultimately A (fun x => 0 <= g2 x) ->
  dominated A f1 g1 ->
  dominated A f2 g2 ->
  dominated A (fun x => Z.max (f1 x) (f2 x)) (fun x => Z.max (g1 x) (g2 x)).
Proof.
  intros P1 P2 D1 D2.
  forwards (c1 & c1_pos & U1): dominated_nonneg_const D1.
  forwards (c2 & c2_pos & U2): dominated_nonneg_const D2.
  exists (Z.max c1 c2).
  revert P1 P2 U1 U2; filter_closed_under_intersection.
  introv (? & ? & ? & ?). nia.
Qed.

(* One can "distribute" dominated over max, that is, a max is dominated by some
   function if both its components are dominated by it.
*)

Lemma dominated_max_distr A f g h :
  dominated A f h ->
  dominated A g h ->
  dominated A (fun x => Z.max (f x) (g x)) h.
Proof.
  intros (c1 & U1) (c2 & U2).
  exists (Z.max c1 c2).
  revert U1 U2; filter_closed_under_intersection.
  intros. nia.
Qed.

(* A maximum is dominated by a sum, for ultimately nonnegative functions. *)

Lemma dominated_max_sum A f g :
  ultimately A (fun x => 0 <= f x) ->
  ultimately A (fun x => 0 <= g x) ->
  dominated A (fun x => Z.max (f x) (g x)) (fun x => f x + g x).
Proof.
  intros fpos gpos. exists 1.
  revert fpos gpos; filter_closed_under_intersection.
  intros. nia.
Qed.

(* Conversely, a sum is dominated by a maximum. [max] and [+] are asymptotically
   equivalent, for ultimately nonnegative functions. *)

Lemma dominated_sum_max A f g :
  ultimately A (fun x => 0 <= f x) ->
  ultimately A (fun x => 0 <= g x) ->
  dominated A (fun x => f x + g x) (fun x => Z.max (f x) (g x)).
Proof.
  intros fpos gpos. exists 2.
  revert fpos gpos; filter_closed_under_intersection.
  intros. nia.
Qed.

(* Dominated is compatible with min, for ultimately nonnegative functions *)

Lemma dominated_min A f1 f2 g1 g2 :
  ultimately A (fun (x:A) => 0 <= f1 x) ->
  ultimately A (fun (x:A) => 0 <= f2 x) ->
  ultimately A (fun (x:A) => 0 <= g1 x) ->
  ultimately A (fun (x:A) => 0 <= g2 x) ->
  dominated A f1 g1 ->
  dominated A f2 g2 ->
  dominated A (fun (x:A) => Z.min (f1 x) (f2 x)) (fun (x:A) => Z.min (g1 x) (g2 x)).
Proof.
  intros Pf1 Pf2 Pg1 Pg2 D1 D2.
  forwards (c1 & c1_pos & U1): dominated_nonneg_const D1.
  forwards (c2 & c2_pos & U2): dominated_nonneg_const D2.
  exists (Z.max c1 c2).
  revert Pf1 Pf2 Pg1 Pg2 U1 U2; filter_closed_under_intersection.
  introv (? & ? & ? & ? & ? & ?). nia.
Qed.

Lemma dominated_min_distr A f g1 g2 :
  dominated A f g1 ->
  dominated A f g2 ->
  dominated A f (fun (x:A) => Z.min (g1 x) (g2 x)).
Proof.
  intros D1 D2.
  forwards (c1 & c1_pos & U1): dominated_nonneg_const D1.
  forwards (c2 & c2_pos & U2): dominated_nonneg_const D2.
  exists (Z.max c1 c2).
  revert U1 U2; filter_closed_under_intersection.
  introv (? & ?). nia.
Qed.

(* Domination is compatible with sum. *)

Lemma dominated_sum A f1 f2 g1 g2 :
  ultimately A (fun x => 0 <= g1 x) ->
  ultimately A (fun x => 0 <= g2 x) ->
  dominated A f1 g1 ->
  dominated A f2 g2 ->
  dominated A (fun x => f1 x + f2 x) (fun x => g1 x + g2 x).
Proof.
  intros g1P g2P (c1 & u1) (c2 & u2).
  exists (Z.max c1 c2).
  revert g1P g2P u1 u2; filter_closed_under_intersection.
  intros. nia.
Qed.

Lemma dominated_sum_distr A f g h :
  dominated A f h ->
  dominated A g h ->
  dominated A (fun x => f x + g x) h.
Proof.
  intros (c1 & U1) (c2 & U2).
  exists (c1 + c2).
  revert U1 U2; filter_closed_under_intersection.
  introv (? & ?). nia.
Qed.

Lemma dominated_sum_r_nonneg_1 A f g1 g2 :
  ultimately A (fun x => 0 <= g1 x) ->
  ultimately A (fun x => 0 <= g2 x) ->
  dominated A f g1 ->
  dominated A f (fun x => g1 x + g2 x).
Proof.
  intros g1P g2P D. forwards (c & cP & U): dominated_nonneg_const D. exists c.
  revert U g1P g2P; filter_closed_under_intersection.
  intros a [H1 H2]. nia.
Qed.

Lemma dominated_sum_r_nonneg_2 A f g1 g2 :
  ultimately A (fun x => 0 <= g1 x) ->
  ultimately A (fun x => 0 <= g2 x) ->
  dominated A f g2 ->
  dominated A f (fun x => g1 x + g2 x).
Proof.
  intros g1P g2P D. forwards (c & cP & U): dominated_nonneg_const D. exists c.
  revert U g1P g2P; filter_closed_under_intersection.
  intros a [H1 H2]. nia.
Qed.

(* This lemma offers a general mechanism for transforming the parameters
   of the asymptotic analysis. *)

(* Let [f] and [g] be functions of a parameter [j]. Assume [f] is dominated
   by [g]. Now, let [p] be a function of [I] into [J], which defines [j] in
   terms of [i]. Assume that [p i] becomes arbitrarily large as [i] grows.
   Then, [f . p] is dominated by [g . p]. These are functions of [i]. *)

(* The converse implication is false, as the image of the function [p] could
   lie in a subset of well-chosen values of [j] outside of which [f] is not
   dominated by [g]. *)

(* This lemma is analogous to [domin_comp] in Coquelicot. *)

Lemma dominated_comp :
  forall (I J : filterType) (f g : J -> Z),
  dominated J f g ->
  forall p : I -> J,
  limit I J p ->
  dominated I (fun i => f (p i)) (fun i => g (p i)).
Proof.
  (* The statement is really quite obvious, since [dominated] is defined
     in terms of [ultimately], and [limit _ _ p] means precisely that [p]
     maps [ultimately] to [ultimately]. *)
  introv ( c & u ) hp.
  (* The multiplicative factor is unaffected by the transformation. *)
  exists c.
  (* The hypothesis [u] states that for large enough [j], [f j] is
     bounded by [c] times [g j]. The hypothesis [hp] states that
     [p i] becomes arbitrarily large as [i] becomes large enough.
     The result follows directly from the combination of these
     hypotheses. *)
  eapply filter_closed_under_inclusion.
    eapply hp. eexact u.
    simpl. eauto.
Qed.

(* Alternative formulation of [dominated_comp], that doesn't require the goal to
   syntactically match the composition of [f] (resp. [g]) and [p].

   It only requires the user to prove the pointwise equality between the
   functions that appear in the goal and the composition of [f] (resp. [g]) and
   [p].
*)

Lemma dominated_comp_eq :
  forall (I J : filterType) (f g : J -> Z),
  dominated J f g ->
  forall (p : I -> J) (fp gp : I -> Z),
  limit I J p ->
  (forall i, fp i = f (p i)) ->
  (forall i, gp i = g (p i)) ->
  dominated I fp gp.
Proof.
  introv domfg limitp fp_eq gp_eq.
  forwards: fun_ext_dep fp_eq.
  forwards: fun_ext_dep gp_eq.
  subst. apply dominated_comp; eauto.
Qed.

(* Note: the conclusion of [dominated_comp] could be rephrased as follows. *)

Goal
  forall (I J : filterType),
  forall f g : J -> Z,
  forall p : I -> J,
  dominated I (fun i => f (p i)) (fun i => g (p i)) <->
  dominated (image_filterType I p) f g.
Proof.
  intros. unfold dominated, image. tauto.
Qed.

(* TODO: move *)

Lemma dominated_shift :
  forall f g x0,
  dominated Z_filterType f g <->
  dominated Z_filterType (fun x => f (Zshift x0 x)) (fun x => g (Zshift x0 x)).
Proof.
  intros. unfold dominated.
  split; intros (c & U); exists c. simpl in *.
  rewrite~ <-(ZshiftP x0) in U.
  rewrite~ <-(ZshiftP x0).
Qed.

Lemma dominated_pow_r_cst_l A :
  forall (f g : A -> Z) (b c: Z),
  0 <= c -> 0 < b ->
  (* if f x = -c, g = 0, b ^ (f x) is O(g) but b ^ (c + f x) is not O(g) *)
  ultimately A (fun x => 0 <= f x) ->
  dominated A (fun x => b ^ (f x)) g ->
  dominated A (fun x => b ^ (c + f x)) g.
Proof.
  introv cpos bpos Ufpos D.
  forwards~ [k U]: dominated_mul_cst_l_1 (b^c) D.
  exists k. applys filter_closed_under_intersection Ufpos U. intros.
  rewrites~ Z.pow_add_r.
Qed.

Lemma dominated_pow_r_cst_r A :
  forall (f g : A -> Z) (b c: Z),
  0 <= c -> 0 < b ->
  ultimately A (fun x => 0 <= f x) ->
  dominated A (fun x => b ^ (f x)) g ->
  dominated A (fun x => b ^ (f x + c)) g.
Proof.
  introv cpos bpos ? ?.
  eapply dominated_eq_l. applys dominated_pow_r_cst_l.
  apply cpos. apply bpos. eassumption. eassumption.
  intros. rewrites~ Zplus_comm.
Qed.

Lemma dominated_pow_l A :
  forall (f g : A -> Z) (e: Z),
  ultimately A (fun x => 0 <= f x) ->
  ultimately A (fun x => 0 <= g x) ->
  dominated A f g ->
  dominated A (fun x => (f x) ^ e) (fun x => (g x) ^ e).
Proof.
  introv Ufpos Ugpos D.
  forwards (k & K & U) : dominated_nonneg_const D.
  exists (Z.abs (k ^ e)).
  generalize Ufpos Ugpos U. filter_closed_under_intersection.
  intros a (? & ? & ?).
  asserts f_le_kg: (f a ^ e <= (k * g a) ^ e).
  { apply Z.pow_le_mono_l. nia. }
  lets powmul: Z.pow_mul_l k (g a) e. rewrites powmul in f_le_kg.
  forwards: Z.pow_nonneg k e. lia.
  repeat (rewrite Z.abs_eq; [| apply Z.pow_nonneg; lia ]).
  nia.
Qed.

Lemma dominated_cst_pow : forall a c,
  0 < a ->
  dominated Z_filterType (fun _ => c) (fun n => a^n).
Proof. intros. apply dominated_cst_limit. limit. Qed.

Lemma dominated_log A :
  forall f g : A -> Z,
    ultimately A (fun x => 2 <= g x) ->
    dominated A f g ->
    dominated A (fun x => Z.log2 (f x)) (fun x => Z.log2 (g x)).
Proof.
  introv U_g_ge_2 D.
  forwards (k & K & U) : dominated_nonneg_const D.
  exists (Z.abs (Z.log2 k) + 1 + 1).
  applys filter_closed_under_intersection U_g_ge_2 U.
  intros a g_ge_2 f_le_kg.
  forwards: Z.log2_nonneg (f a).
  forwards: Z.log2_nonneg (g a).
  forwards: Z.log2_nonneg k.
  destruct (Z.neg_nonneg_cases (f a)) as [fneg | fpos].
  - (* f a < 0 => Z.log2 (f a) = 0 *)
    rewrite Z.log2_nonpos. rewrite Z.abs_0. nia. lia.
  - { (* 0 <= f a *)
      asserts gpos: (0 <= g a). nia. (* 0 <= g a *)

      assert (g_ge_2' : 2^1 <= g a) by (simpl; apply g_ge_2).
      forwards~ I: Z.log2_le_mono g_ge_2'. rewrites~ Z.log2_pow2 in I.
      forwards: Z.log2_le_mono (f a) (k * g a). nia.
      forwards: Z.log2_mul_above k (g a); try nia. omega. }
Qed.

End DominatedLaws.

(* ---------------------------------------------------------------------------- *)

Lemma pack_forall_pair_eq :
  forall (A B C : Type) (P Q : A * B -> C),
  (forall (a : A) (b : B), P (a, b) = Q (a, b)) -> (forall x, P x = Q x).
Proof.
  introv H. intros [? ?]. eauto.
Qed.

(* TEMPORARY move *)
Ltac asserts_applys P :=
  let H := fresh in
  asserts H : P; [ | applys H; clear H ].

Ltac math_apply P :=
  asserts_applys P; [ intros; omega | .. ].

(* ---------------------------------------------------------------------------- *)

Definition Oex (f g : Z * Z -> Z) :=
  exists c n0, forall x y, n0 <= x \/ n0 <= y -> Z.abs (f (x, y)) <= c * Z.abs (g (x, y)).

Goal forall f g,
  Oex f g <->
  dominated (orp_filterType Z_filterType Z_filterType) f g.
Proof.
  intros f g. split.
  { intros [c [n0 HU]]. exists c. unfold orp_filterType. cbn. unfold or.
    do 2 exists (fun n => n0 <= n).
    do 2 (split; [ now apply ultimately_ge_Z |]). split; intros; apply HU; eauto. }
  { intros [c HU]. unfold orp_filterType in HU. cbn in HU. unfold or in HU.
    exists c. destruct HU as [P1 [P2 (U1 & U2 & H1 & H2)]]. rewrite ZP in U1, U2.
    destruct U1 as [n1 U1]. destruct U2 as [n2 U2]. exists (Z.max n1 n2).
    intros x y [Hxy|Hxy]; eauto with zarith. }
Qed.

(* ---------------------------------------------------------------------------- *)


Section ProductLaws.

(* [product_filterType] is "symmetrical" *)
Lemma dominated_product_swap : forall (A B : filterType) f g,
  dominated (product_filterType A B) (fun '(a,b) => f a b) (fun '(a,b) => g a b) ->
  dominated (product_filterType B A) (fun '(b,a) => f a b) (fun '(b,a) => g a b).
Proof.
  introv H. destruct H as [c U].
  exists c. rewrite productP in *. destruct U as (P1 & P2 & UP1 & UP2 & UU).
  exists P2 P1. splits~.
Qed.

End ProductLaws.

Module Product.

(* Under some assumptions, domination is compatible with [cumul] (i.e "big sum").

   Note that [f] and [g] are functions over [A * Z]. Moreover, their sums are
   also functions over [A * Z]. Domination is expressed wrt. the product filter
   of [A] and [Z], both for [f], [g] and their sums.

   Note that the hypothesis:

     [forall a, monotonic (le_after lo Z.le) Z.le (fun i => f (a, i))]

   cannot be relaxed to:

     [forall a, ultimately (fun x =>
        monotonic (le_after x Z.le) Z.le (fun i => f (a, i))].

   I.e, [f] really has to be monotonic starting at the summation index.

   For example, if we take:
     f (a, x) = 2^a if x = 0, x otherwise
     g (a, x) = x

   then:
     - dominated f g holds
     - for all a, f is monotonic for x big enough
     - Σf (a, x) is equal to x2^a while Σg (a, x) is O(x²).
*)

Lemma dominated_big_sum :
  forall (A: filterType) (f g : A -> Z -> Z) (lo : Z),
  ultimately A (fun a => forall i, lo <= i -> 0 <= f a i) ->
  ultimately A (fun a => forall i, lo <= i -> 0 <= g a i) ->
  dominated (product_filterType A Z_filterType)
    (fun '(a, i) => f a i) (fun '(a, i) => g a i) ->
  (forall a, monotonic (le_after lo Z.le) Z.le (fun i => f a i)) ->
  dominated (product_filterType A Z_filterType)
    (fun '(a, n) => cumul lo n (fun i => f a i))
    (fun '(a, n) => cumul lo n (fun i => g a i)).
Proof.
  introv Uf_nonneg Ug_nonneg dom_f_g f_mon. simpl in *.
  forwards (c & c_pos & U_f_le_g): dominated_nonneg_const dom_f_g.
  clear dom_f_g.

  rewrite productP in U_f_le_g.
  destruct U_f_le_g as (P1 & P2 & UP1 & UP2 & H).

  rewrite (ZP_ultimately (filter_conj_alt (ultimately_ge_Z 0) (ultimately_ge_Z lo))) in UP2.
  destruct UP2 as (N & (Nnonneg & lo_le_N) & HN).

  exists (c * (N - lo + 1)). rewrite productP.
  revert Uf_nonneg Ug_nonneg UP1; filter_intersect; intro UP1'.

  eexists. exists (fun n => N + 1 <= n). splits.
  { apply UP1'. }
  { apply ultimately_ge_Z. }
  intros a n (f_nonneg & g_nonneg & P1_a) N_le_n.
  clear UP1'.

  asserts~ H' : (forall x, N <= x -> Z.abs (f a x) <= c * Z.abs (g a x)).
  clear H HN P1_a.

  (* Product filter dance done. *)

  (* Eliminate [Z.abs] in the goal, as [f] and [g] are nonnegative. *)
  rewrite Z.abs_eq; [| apply cumul_nonneg; eauto].
  rewrite Z.abs_eq; [| apply cumul_nonneg; eauto].

  (* Eliminate [Z.abs] in H', for the same reason. *)
  assert (Hfg : (forall x, N <= x -> f a x <= c * g a x)). {
    intros x N_le_x.
    specializes H' x N_le_x.
    rewrite Z.abs_eq in H'; [| apply f_nonneg; lia].
    rewrite Z.abs_eq in H'; [| apply g_nonneg; lia].
    assumption.
  }
  clear H'.

  (* Start proving the main inequality, by splitting [cumul]s, and rewriting
     under [Z.le]. *)

  change (fun i => f a i) with (f a).
  change (fun i => g a i) with (g a).

  rewrite (cumul_split N) with (f := f a) by omega.
  rewrite cumulP with (f := f a) (lo := N).
  rewrite big_covariant with
    (xs := interval N n)
    (g := (fun i => c * g a i))
    (R := Z.le);
  try typeclass; cycle 1.
  { eauto using in_interval_lo. }

  rewrite <-big_map_distributive; try typeclass.
  rewrite <-cumulP with (f := g a).
  rewrite cumulP with (f := f a) (lo := lo).
  rewrite big_covariant with
    (xs := interval lo N)
    (g := (fun _ => f a N)); try typeclass; cycle 1.
  { introv inI.
    forwards x_lt_N: in_interval_hi inI.
    forwards lo_le_x: in_interval_lo inI.
    forwards x_le_N: Z.lt_le_incl x_lt_N.
    apply f_mon. unfold le_after. lia. }

  rewrite~ big_const_Z.
  rewrite Hfg by omega.

  asserts_rewrite
    (c * (N - lo + 1) * cumul lo n (g a) =
     c * (N - lo + 1) * cumul lo N (g a) +
     c * (N - lo) * cumul N n (g a) +
     c * cumul N n (g a)).
  { match goal with |- _ = ?r => remember r as rhs end.
    rewrite (cumul_split N) by omega.
    rewrite Z.mul_add_distr_l.

    subst rhs. rewrite Zplus_assoc_reverse.
    apply Zplus_eq_compat; eauto.

    match goal with |- _ = ?r => remember r as rhs end.
    rewrite Z.mul_add_distr_l.
    rewrite Z.mul_add_distr_r.
    rewrite Z.mul_1_r.
    subst rhs. reflexivity. }

  apply Zplus_le_compat_r.

  asserts_rewrite <-(0 <= c * (N - lo + 1) * cumul lo N (g a)). {
    apply Z.mul_nonneg_nonneg.
    { nia. }
    { apply cumul_nonneg. intros. apply g_nonneg. lia. }
  }
  rewrite Zplus_0_l.
  rewrite Z.mul_assoc with (m := c).
  rewrite Z.mul_comm with (m := c).

  apply Zmult_le_compat_l.
  - rewrite~ cumul_cons_l. 2: lia. rewrite <-cumul_nonneg. lia.
    intros. apply~ g_nonneg. lia.
  - nia.
Qed.

(* Corollary of the previous lemma, where the summation is done up to some
   function [h], which is required to grow to infinity.
*)

Lemma dominated_big_sum_with (h : Z -> Z) :
  forall (A: filterType) (f g : A -> Z -> Z) (lo : Z),
  ultimately A (fun a => forall i, lo <= i -> 0 <= f a i) ->
  ultimately A (fun a => forall i, lo <= i -> 0 <= g a i) ->
  dominated (product_filterType A Z_filterType)
    (fun '(a, i) => f a i) (fun '(a, i) => g a i) ->
  (forall a, monotonic (le_after lo Z.le) Z.le (fun i => f a i)) ->
  limit Z_filterType Z_filterType h ->
  dominated (product_filterType A Z_filterType)
    (fun '(a, n) => cumul lo (h n) (fun i => f a i))
    (fun '(a, n) => cumul lo (h n) (fun i => g a i)).
Proof.
  introv Ufnonneg Ugnonneg dom_f_g f_mon h_lim.
  eapply dominated_comp_eq.
  - applys~ dominated_big_sum lo dom_f_g.
  - eapply limit_liftr. apply h_lim.
  - intros [? ?]. reflexivity.
  - intros [? ?]. reflexivity.
Qed.

(* Even more general corollary of [dominated_big_sum]: the body of the big sum
   can now depend on the sum upper bound.
*)

Lemma dominated_big_sum' :
  forall (A: filterType) (f g : A -> Z -> Z -> Z) (h : Z -> Z) (lo : Z),
  ultimately (product_filterType A Z_filterType) (fun '(a, n) => forall i, lo <= i -> 0 <= f a n i) ->
  ultimately (product_filterType A Z_filterType) (fun '(a, n) => forall i, lo <= i -> 0 <= g a n i) ->
  dominated (product_filterType (product_filterType A Z_filterType) Z_filterType)
    (fun '(a, n, i) => f a n i) (fun '(a, n, i) => g a n i) ->
  (forall a n, monotonic (le_after lo Z.le) Z.le (fun i : Z => f a n i)) ->
  limit Z_filterType Z_filterType h ->
  dominated (product_filterType A Z_filterType)
    (fun '(a, n) => cumul lo (h n) (fun i => f a n i))
    (fun '(a, n) => cumul lo (h n) (fun i => g a n i)).
Proof.
  introv ? ? D M ?.
  forwards~ Dcumul: dominated_big_sum_with h (product_filterType A Z_filterType)
    (fun '(a, n) i => f a n i) (fun '(a, n) i => g a n i) lo.

  { eapply dominated_eq_l. eapply dominated_eq_r. apply D.
    intros [[? ?] ?]. reflexivity.
    intros [[? ?] ?]. reflexivity. }

  { intros [? ?]. eapply monotonic_eq. apply M. reflexivity. }

  eapply dominated_comp_eq with
    (J := product_filterType (product_filterType A Z_filterType) Z_filterType)
    (p := fun '(a, i) => (a, i, i)).
  apply Dcumul.

  { eapply limit_eq.
    apply limit_product with (f := fun p => p) (g := fun '(a, x) => x). (* ehh *)
    limit. limit. intros [? ?]. reflexivity. }

  intros [? ?]. reflexivity.
  intros [? ?]. reflexivity.
Qed.

(* The iterated sum of [f] is dominated by [f] times the number of
   iterations. *)

Lemma dominated_big_sum_bound :
  forall (A : filterType) (f : A -> Z -> Z) (lo : Z),
  ultimately A (fun a => forall i, lo <= i -> 0 <= f a i) ->
  (forall a, monotonic (le_after lo Z.le) Z.le (fun i => f a i)) ->
   dominated (product_filterType A Z_filterType)
    (fun '(a, n) => cumul lo n (fun i => f a i))
    (fun '(a, n) => n * f a n).
Proof.
  introv U_f_nonneg f_mon.
  eexists (Z.max 1 (1 - lo)). rewrite productP. do 2 eexists. splits.
  { apply U_f_nonneg. }
  { apply (filter_conj_alt (ultimately_ge_Z 1) (ultimately_ge_Z (lo + 1))). }
  { intros a n f_nonneg [one_le_n lo_le_n].
    rewrite Z.abs_eq; [| apply cumul_nonneg; eauto].
    rewrite Z.abs_eq; [| eauto with zarith].
    rewrite cumulP.
    rewrite big_covariant with
      (g := (fun p => f a (n-1)));
    try typeclass; cycle 1.
    { intros x I. apply f_mon. unfold le_after.
      forwards~: in_interval_lo I. forwards~: in_interval_hi I. lia. }

    rewrite big_const_Z. 2: lia.
    assert (f_le: f a (n - 1) <= f a n)
      by (apply f_mon; unfold le_after; lia).
    rewrite f_le; [| lia].
    assert (f_an_nonneg: 0 <= f a n) by (apply f_nonneg; lia).

    destruct (Z.le_gt_cases 0 lo) as [O_le_lo | lo_lt_O].
    { rewrite Z.max_l; [| lia]. ring_simplify. nia. }
    { rewrite Z.max_r; [| lia]. rewrite Z.mul_assoc.
      apply Zmult_le_compat_r; nia. } }
Qed.

Lemma dominated_big_sum_bound_with (h : Z -> Z) :
  forall (A: filterType) (f : A -> Z -> Z) (lo : Z),
  ultimately A (fun a => forall i, lo <= i -> 0 <= f a i) ->
  (forall a, monotonic (le_after lo Z.le) Z.le (fun i => f a i)) ->
  limit Z_filterType Z_filterType h ->
  dominated (product_filterType A Z_filterType)
    (fun '(a, n) => cumul lo (h n) (fun i => f a i))
    (fun '(a, n) => h n * f a (h n)).
Proof.
  introv U_f_nonneg f_mon lim_h.
  forwards~ dom_bound: dominated_big_sum_bound f lo.
  applys dominated_comp_eq dom_bound.
  - eapply limit_liftr. exact lim_h.
  - intros [? ?]. reflexivity.
  - intros [? ?]. reflexivity.
Qed.

End Product.

(* Asymptotic pointwise equality implies domination of iterated sums.

   Similarly to [dominated_ultimately_eq], this allows to "patch"
   non-asymptotic parts of functions, which iterated sum appears in
   a dominated goal.

   Note:
   The [ultimately (fun x => 0 < f' x)] assumption is really required.

   Otherwise, take [f := fun x => if x = 0 then 1 else 0] and [f' := 0].

   [ultimately (fun x => f x = f' x)] holds, but
   [dominated (cumul f 0) (cumul f' 0)] doesn't.

   This is not completely tight; [often (fun x => 0 < f' x)] may be enough.
   However, in practice the functions we handle tend to be ultimately
   monotonic, in which case this boils down to the same thing.
*)
Lemma dominated_cumul_ultimately_eq :
  forall (f f' : Z -> Z) lo,
  ultimately Z_filterType (fun x => f x = f' x) ->
  ultimately Z_filterType (fun x => 0 < f' x) ->
  dominated Z_filterType (fun n => cumul lo n f) (fun n => cumul lo n f').
Proof.
  introv.
  generalize (ultimately_ge_Z lo). filter_intersect. rewrite ZP.
  intros (N & HN).

  exists 2. rewrite ZP.
  exists_big n0 Z. intros n n0_le_n.

  assert (N_le_n : N <= n) by (rewrite <-n0_le_n; big).
  assert (lo_le_N : lo <= N) by (apply HN; omega).

  assert (cumul_f'_ge_n : forall n, N <= n -> n - N <= cumul N n f'). {
    assert (cumul_minus_ge_0 :
      forall n, 0 <= cumul N n (fun x => f' x - 1)
    ).
    { intros. apply cumul_nonneg.
      intros x ? ?. forwards~ (? & ? & ?): HN x ___.
      omega. }

    intros x H.
    rewrite~ cumul_minus_one.
    rewrite <-cumul_minus_ge_0. omega.
  }

  assert (cumul_past_N_ge_0 : forall n, 0 <= cumul N n f).
  { intros. apply cumul_nonneg.
    intros x ? ?. forwards~ (? & ? & ?) : HN x ___.
    omega. }

  assert (cumul_past_N_eq : forall n,
    N <= n -> cumul N n f' = cumul N n f
  ).
  { intros. unfold cumul. apply big_covariant; try typeclass.
    introv I. symmetry. apply HN. applys* in_interval_lo. }

  assert (cumul_f'_pos : 0 <= cumul lo n f'). {
    rewrite (cumul_split N) by auto.
    rewrite <-cumul_f'_ge_n; auto.
    math_apply (forall a b c, c - a <= b -> 0 <= a + (b - c)).
    rewrite <-n0_le_n. big.
  }

  rewrite Z.abs_eq with (cumul lo n f') by auto.
  rewrite (cumul_split N) with (f := f) by auto.
  rewrite Z.abs_triangle.
  rewrite Z.abs_eq with (cumul N n f) by auto.
  rewrite (cumul_split N) with (f := f') by auto.
  rewrite Z.mul_add_distr_l.
  rewrite cumul_past_N_eq by auto.
  math_apply (forall a b c, a <= c + b -> a + b <= c + 2 * b).
  rewrite <-cumul_past_N_eq by auto.
  rewrite <-cumul_f'_ge_n by auto.
  math_apply (forall a b c d, a - b + d <= c -> a <= b + (c - d)).
  rewrite <-n0_le_n. big.
  close.
Qed.

(* We could deduce a [dominated_big_sum] lemma for the one parameter case from
   [Product.dominated_big_sum], by instantiating [A] by [unit].

   However, thanks to the previous lemma [dominated_cumul_ultimately_eq], we can
   do better, and replace the monotonocity hypothesis by a "ultimately positive"
   hypothesis.
*)
Lemma dominated_big_sum :
  forall (f g : Z -> Z) (lo : Z),
  ultimately Z_filterType (fun i => 0 < f i) ->
  ultimately Z_filterType (fun i => 0 < g i) ->
  dominated Z_filterType f g ->
  dominated Z_filterType (fun n => cumul lo n f) (fun n => cumul lo n g).
Proof.
  introv Uf_pos Ug_pos dom_f_g. simpl in *.
  forwards (c & c_pos & U_f_le_g): dominated_nonneg_const dom_f_g.
  clear dom_f_g.

  revert Uf_pos Ug_pos U_f_le_g. filter_intersect.
  rewrite (ZP_ultimately (filter_conj_alt (ultimately_ge_Z 0) (ultimately_ge_Z lo))).
  intros (N & (N_nonneg & lo_le_N) & HN).

  (* "patch" [f] and [g] to make them equal to [0] between [lo] and [N].
     [dominated_cumul_ultimately_eq] allows us to do precisely that. *)

  pose (f' := fun x => If lo <= x < N then 0 else f x).
  pose (g' := fun x => If lo <= x < N then 0 else g x).
  apply dominated_transitive with (fun n => cumul lo n f').
  { apply dominated_cumul_ultimately_eq;
    subst f'; simpl; rewrite ZP; exists N; intros.
    { cases_if; [omega | tauto]. }
    { cases_if; [omega | applys~ HN]. } }
  apply dominated_transitive with (fun n => cumul lo n g'); cycle 1.
  { apply dominated_cumul_ultimately_eq;
    subst g'; simpl; rewrite ZP; exists N; intros.
    cases_if; [omega | tauto]. applys~ HN. }

  (* Instantiate the big-O constant, and do some cleanup. *)

  exists c. rewrite ZP. exists N. intros n N_le_n.

  assert (f_g_nonneg : forall n, N <= n -> 0 <= f n /\ 0 <= g n).
  { intros. splits; apply Z.lt_le_incl; applys~ HN. }
  assert (cumul_f'_nonneg : forall n, 0 <= cumul lo n f').
  { intros. subst f'. apply cumul_nonneg. intros.
    cases_if~; [| apply f_g_nonneg]; auto with zarith. }
  assert (cumul_g'_nonneg : forall n1 n2, lo <= n1 -> 0 <= cumul n1 n2 g').
  { intros. subst g'. apply cumul_nonneg. intros.
    cases_if~; [| apply f_g_nonneg]; auto with zarith. }

  (* Eliminate [Z.abs] in the goal and HN, as [f] and [g] are nonnegative. *)
  rewrite Z.abs_eq by auto.
  rewrite Z.abs_eq by (apply cumul_g'_nonneg; auto with zarith).
  assert (Hf'g' : forall x, N <= x -> f' x <= c * (g' x)). {
    intros x N_le_x. specializes HN x N_le_x.
    rewrite Z.abs_eq in HN by applys~ f_g_nonneg.
    rewrite Z.abs_eq in HN by applys~ f_g_nonneg.
    subst f' g'. simpl. cases_if~; omega.
  }
  clear HN.

  (* Start proving the main inequality by splitting [cumul]s.
     [cumul f' lo N] and [cumul g' lo N] are equal to 0, and
     after [N], [f x <= c * g x] holds.
  *)

  rewrite (cumul_split N) with (f := f') by omega.
  rewrite cumulP with (f := f') (lo := lo).
  rewrite big_covariant with (g := fun _ => 0) (R := eq);
    try typeclass; cycle 1.
  { introv I. forwards: in_interval_lo I. forwards: in_interval_hi I.
    subst f'; simpl. cases_if~. omega. }
  rewrite~ big_const_Z. ring_simplify.

  rewrite (cumul_split N) with (f := g') by omega.
  rewrite Z.mul_add_distr_l.
  rewrite cumulP with (f := g') (lo := lo).
  rewrite big_covariant with (g := fun _ => 0) (R := eq);
    try typeclass; cycle 1.
  { introv I. forwards: in_interval_lo I. forwards: in_interval_hi I.
    subst g'; simpl. cases_if~. omega. }
  rewrite~ big_const_Z. ring_simplify.

  rewrite cumulP with (f := f').
  rewrite big_covariant with (R := Z.le) (g := (fun i => c * g' i));
    try typeclass; cycle 1.
  { intros. apply Hf'g'. applys* in_interval_lo. }
  rewrite <-big_map_distributive; try typeclass.
  rewrite <-cumulP.
  omega.
Qed.

Lemma dominated_big_sum_with (h : Z -> Z) :
  forall (f g : Z -> Z) (lo : Z),
  ultimately Z_filterType (fun i => 0 < f i) ->
  ultimately Z_filterType (fun i => 0 < g i) ->
  dominated Z_filterType f g ->
  limit Z_filterType Z_filterType h ->
  dominated Z_filterType (fun n => cumul lo (h n) f) (fun n => cumul lo (h n) g).
Proof.
  introv Ufpos Ugpos dom_f_g h_lim.
  eapply dominated_comp_eq.
  - applys~ dominated_big_sum lo dom_f_g.
  - apply h_lim.
  - reflexivity.
  - reflexivity.
Qed.

Lemma dominated_big_sum' :
  forall (f g : Z -> Z -> Z) (h : Z -> Z) (lo : Z),
  ultimately Z_filterType (fun n => forall i, lo <= i -> 0 <= f n i) ->
  ultimately Z_filterType (fun n => forall i, lo <= i -> 0 <= g n i) ->
  dominated (product_filterType Z_filterType Z_filterType)
    (fun '(n, i) => f n i) (fun '(n, i) => g n i) ->
  (forall n, monotonic (le_after lo Z.le) Z.le (fun i : Z => f n i)) ->
  limit Z_filterType Z_filterType h ->
  dominated Z_filterType
    (fun n => cumul lo (h n) (fun i => f n i))
    (fun n => cumul lo (h n) (fun i => g n i)).
Proof.
  introv ? ? D ? ?.
  forwards~ Dcumul: Product.dominated_big_sum_with h Z_filterType f g lo.
  eapply dominated_comp_eq with
    (J := product_filterType Z_filterType Z_filterType)
    (p := fun (i:Z) => (i, i)).
  apply Dcumul.
  limit.
  reflexivity. reflexivity.
Qed.

Lemma dominated_big_sum_bound :
  forall (f : Z -> Z) (lo : Z),
  ultimately Z_filterType (fun i => 0 < f i) ->
  ultimately Z_filterType (fun i => monotonic (le_after i Z.le) Z.le f) ->
  dominated Z_filterType (fun n => cumul lo n f) (fun n => n * f n).
Proof.
  introv. generalize (ultimately_ge_Z lo). filter_intersect.
  rewrite ZP. intros (N & HN).

  (* "Patch" [f] to be always monotonic. *)
  pose (f' := fun x => If x < N then f N else f x).

  eapply dominated_transitive with (fun n => cumul lo n f').
  { apply dominated_cumul_ultimately_eq; exists N; intros; subst f'; simpl.
    cases_if~; omega.
    cases_if~; applys~ HN. auto with zarith. }

  eapply dominated_transitive with (fun n => n * f' n); cycle 1.
  { apply dominated_ultimately_eq; exists N; intros; subst f'; simpl.
    cases_if~; omega. }

  (* Use the version of this lemma on product filters. *)

  pose (f'' := fun (_ : Z) n => f' n).

  forwards~ D: @Product.dominated_big_sum_bound Z_filterType f'' lo.
  { apply filter_universe_alt. intros. subst f'' f'. simpl.
    cases_if; apply Z.lt_le_incl; apply HN; omega. }
  { intros. subst f'' f'. simpl.
    specializes HN N ___. omega. destruct HN as (? & ? & fmon).
    unfold monotonic, le_after in *. intros.
    cases_if; cases_if; auto with zarith. }
  simpl in *. destruct D as [c U]. rewrite productP in U.
  destruct U as (P1 & P2 & UP1 & UP2 & H).
  exists c. revert UP1 UP2; filter_closed_under_intersection.
  introv (? & ?). applys* H.
Qed.

Lemma dominated_big_sum_bound_with (h : Z -> Z) :
  forall (f : Z -> Z) (lo : Z),
  ultimately Z_filterType (fun i => 0 < f i) ->
  ultimately Z_filterType (fun i => monotonic (le_after i Z.le) Z.le f) ->
  limit Z_filterType Z_filterType h ->
  dominated Z_filterType (fun n => cumul lo (h n) f) (fun n => h n * f (h n)).
Proof.
  introv U_f_nonneg f_mon lim_h.
  forwards~ dom_bound: dominated_big_sum_bound f lo.
  applys~ dominated_comp_eq dom_bound lim_h.
Qed.

Lemma dominated_big_sum_bound' :
  forall (f g : Z -> Z -> Z) (h : Z -> Z) (lo : Z),
  ultimately Z_filterType (fun n => forall i, lo <= i -> 0 <= f n i) ->
  ultimately Z_filterType (fun n => forall i, lo <= i -> 0 <= g n i) ->
  dominated (product_filterType Z_filterType Z_filterType)
    (fun '(n, i) => f n i) (fun '(n, i) => g n i) ->
  (forall n, monotonic (le_after lo Z.le) Z.le (fun i : Z => f n i)) ->
  limit Z_filterType Z_filterType h ->
  dominated Z_filterType
    (fun n => cumul lo (h n) (fun i => f n i))
    (fun n => h n * f n (h n)).
Proof.
  introv ? ? D ? ?.
  forwards~ Dcumul: Product.dominated_big_sum_bound_with h Z_filterType. assumption.
  eapply dominated_comp_eq with
    (J := product_filterType Z_filterType Z_filterType)
    (p := fun (i:Z) => (i, i)).
  apply Dcumul.
  limit.
  reflexivity. simpl. reflexivity.
Qed.

(* Special case of [dominated_big_sum_bound], where the function in the big sum
   is constant.
*)

Lemma dominated_big_sum_cst_bound : forall (c : Z) (lo : Z),
  dominated Z_filterType (fun n => cumul lo n (fun (_ : Z) => c)) (fun n => n).
Proof.
  intros. exists_big k Z.
  generalize (ultimately_ge_Z 1) (ultimately_ge_Z lo); filter_closed_under_intersection.
  intros x (one_le_x & lo_le_x).
  rewrite~ cumul_const. rewrite Z.mul_sub_distr_r.
  cut (Z.abs c + Z.abs (lo * c) <= k). { generalize k; clear k. intros. nia. }
  big. close.
Qed.

Lemma dominated_big_sum_cst_bound_with (h : Z -> Z) : forall (c : Z) (lo : Z),
  limit Z_filterType Z_filterType h ->
  dominated Z_filterType (fun n => cumul lo (h n) (fun (_ : Z) => c)) (fun n => h n).
Proof.
  introv lim_h.
  forwards D: dominated_big_sum_cst_bound c lo.
  applys~ dominated_comp_eq D lim_h.
Qed.

(*----------------------------------------------------------------------------*)

(* norm 1 on Z*Z *)
Definition N1 '((x, y) : Z * Z) : Z :=
  Z.abs x + Z.abs y.

(* norm ∞ on Z*Z *)
Definition Ninf '((x, y) : Z * Z) : Z :=
  Z.max (Z.abs x) (Z.abs y).

Lemma ultimately_N1_Ninf : forall P,
  ultimately (measure_filterType N1) P <-> ultimately (measure_filterType Ninf) P.
Proof.
  intros. rewrite !measureP. unfold N1, Ninf in *. split; intros [x0 H].
  { exists x0. intros [x y]. specializes H (x, y). intros. apply H. lia. }
  { exists (2 * x0). intros [x y]. specializes H (x, y). intros. apply H. lia. }
Qed.

Lemma dominated_N1_Ninf : forall f g,
  dominated (measure_filterType N1) f g <->
  dominated (measure_filterType Ninf) f g.
Proof.
  intros. unfold dominated.
  split; intros [c U]; exists c;
  [ rewrite <-ultimately_N1_Ninf | rewrite ultimately_N1_Ninf]; auto.
Qed.

(* more generally, all norms on Z^k are equivalent up to a multiplicative
   constant. *)

Lemma finer_product_N1 :
  finer (product Z_filterType Z_filterType) (Filter.measure N1).
Proof.
  unfold finer. intros P. unfold Filter.measure, invimage, product.
  intros [Q [[x0 Hx0] HH]].
  do 2 exists (fun x => x0 <= x). rewrite !ZP. do 2 (split; eauto).
  intros x y ? ?. apply HH. apply Hx0. unfold N1. lia.
Qed.

Lemma finer_product_Ninf :
  finer (product Z_filterType Z_filterType) (Filter.measure Ninf).
Proof.
  unfold finer. intros P. unfold Filter.measure, invimage, product.
  intros [Q [[x0 Hx0] HH]].
  do 2 exists (fun x => x0 <= x). rewrite !ZP. do 2 (split; eauto).
  intros x y ? ?. apply HH. apply Hx0. unfold Ninf. lia.
Qed.

(*----------------------------------------------------------------------------*)

Require Import TLC.LibEpsilon.

Definition max_between (a b : Z) (f : Z -> Z) :=
  epsilon (fun k => forall x, a <= x <= b -> f x <= k).

Lemma max_betweenP (a b : Z) (f: Z -> Z) :
  a <= b ->
  forall x, a <= x <= b ->
    f x <= (max_between a b f).
Proof.
  unfold max_between. intros * HH. epsilon~ E.
  revert HH. induction_wf: (downto a) b. intros Hab.
  tests: (a = b).
  { exists (f b). intros. assert (x = b) as -> by lia. lia. }
  specializes IH (b-1) __ __.
  { unfold downto. rewrite LibInt.le_zarith, LibInt.lt_zarith. lia. } { lia. }
  destruct IH as [k HH]. exists (Z.max k (f b)). intros x ?.
  tests: (x = b). lia. specializes HH x. lia.
Qed.

(* Lemma max_between_mono : forall a b f g, *)
(*   (forall x, a <= x <= b -> f x <= g x) -> *)
(*   max_between a b f <= max_between a b g. *)
(* Proof. *)
(*   intros * Hfg.  *)

Definition max_between2 (x0 x1 y0 y1 : Z) (f : Z -> Z -> Z) :=
  max_between x0 x1 (fun x => max_between y0 y1 (f x)).

Lemma max_between2P (f : Z -> Z -> Z) (x0 x1 y0 y1 : Z) :
  x0 <= x1 ->
  y0 <= y1 ->
  forall x y, x0 <= x <= x1 -> y0 <= y <= y1 ->
    f x y <= max_between2 x0 x1 y0 y1 f.
Proof.
  intros. unfold max_between2.
  etransitivity. 2: apply max_betweenP. apply max_betweenP. all: lia.
Qed.

Lemma cumul_le : forall lo hi f g,
  (forall i, lo <= i < hi -> f i <= g i) ->
  cumul lo hi f <= cumul lo hi g.
Proof.
  intros. apply big_covariant with (R := Z.le); try typeclass.
  intros. eauto using in_interval_hi, in_interval_lo.
Qed.

Lemma cumul_mul_k_le : forall lo hi c f,
  cumul lo hi (fun x => c * f x) = c * cumul lo hi f.
Proof.
  intros *. induction_wf: (upto hi) lo. unfold cumul. interval_case_l lo hi.
  { intros. cbn. lia. }
  { intros. cbn. unfold cumul, Big.big in IH. rewrite IH. 2: upto. cbn. nia. }
Qed.

Lemma dominated_norm_Z2_big_sum :
  forall (f g : Z -> Z -> Z) (lo : Z),
  ultimately (measure_filterType Ninf) (fun '(x, y) => 0 < g x y) ->
  dominated (measure_filterType Ninf)
    (fun '(x, y) => f x y) (fun '(x, y) => g x y) ->
  dominated (measure_filterType Ninf)
    (fun '(x, y) => cumul lo y (fun i => f x i))
    (fun '(x, y) => cumul lo y (fun i => g x i)).
Proof.
  intros * Ugpos (c & c_pos & U_f_le_g)%dominated_nonneg_const.
  revert Ugpos U_f_le_g; filter_intersect;=> U. simpl in *.

  (* XX *)
  assert (exists N, 0 <= N /\ forall x y, N <= Ninf (x, y) ->
    0 < g x y /\ Z.abs (f x y) <= c * Z.abs (g x y)) as [N [HN0 HN]].
  { cbn in U. unfold invimage in U. destruct U as [Q [UQ HQ]].
    rewrite ZP in UQ. destruct UQ as [N0 HN0]. exists (Z.max 0 N0).
    split; [ lia |]. intros x y **. specializes HQ (x, y) __.
    eauto with zarith. }

  pose_big cc Z. assert (0 <= cc) by big.
  pose (c' := c + cc). exists c'.
  assert (c <= c') as Hcc' by (unfold c'; lia).
  rewrite measureP.
  exists_big N' Z. intros [x y] Hxy.
  assert (N <= N') as HNN' by big.

  tests C: (y <= lo).
  { unfold cumul. rewrite !interval_empty; try lia. cbn -[c']. lia. }
  assert (lo < y) by lia. clear C.

  tests C: (N <= Z.abs x \/ N' <= Z.abs x \/ lo > N' \/ y < N' \/ lo > N \/ y < N).
  { assert (0 <= cumul lo y (g x)).
    { apply cumul_nonneg. intros i ? ?.
      lets~ [? ?]: HN x i __. unfold Ninf in *. all: lia. }
    rewrite~ (Z.abs_eq (cumul lo y (fun i => g x i))).
    assert (HH: forall i, lo <= i < y -> Z.abs (f x i) <= c * g x i).
    { intros. lets~ [? HI]: HN x i __. unfold Ninf in *. all: nia. }
    forwards~ HH1: cumul_le lo y (fun i => Z.abs (f x i)) (fun i => c * g x i);[].
    rewrite cumul_mul_k_le in HH1. rewrite cumul_triangle, HH1.
    change (fun i => g x i) with (g x). nia. }
  assert (Z.abs x < N' /\ Z.abs x < N /\
          N <= Z.abs y /\ lo <= N' /\ N' <= y /\ lo <= N /\ N' <= y)
    as (?&?&?&?&?&?&?) by (unfold Ninf in Hxy; lia). clear C.

  rewrite !(@cumul_split N lo y); try lia.
  rewrite !(@cumul_split N' N y); try lia.
  change (fun i => f x i) with (f x). change (fun i => g x i) with (g x).
  rewrite (Z.abs_triangle (cumul lo N (f x))).
  rewrite (Z.abs_triangle (cumul N N' (f x))).
  rewrite !cumul_triangle, !Z.add_assoc.
  assert (N' - N <= cumul N N' (g x)) as HgNN'.
  { rewrite <-(@cumul_le N N' (fun _ => 1)).
    now rewrite cumul_const; lia.
    intros i **. lets~ [? ?]: HN x i __. unfold Ninf in *. all: lia. }
  pose (Kg := - max_between (-N) N (fun x => - cumul lo N (g x))).
  assert (Kg <= cumul lo N (g x)) as HgloN.
  { unfold Kg. rewrite <-max_betweenP.
    rewrite Z.opp_involutive; reflexivity. all: lia. }
  assert (0 <= cumul lo N (g x) + cumul N N' (g x)).
  { rewrite <-HgNN'. rewrite <-HgloN. enough (N - Kg <= N') by lia. big. }
  assert (0 <= cumul N' y (g x)).
  { apply cumul_nonneg.
    intros i **. lets~ [? ?]: HN x i. unfold Ninf in *. all: lia. }
  rewrite (Z.abs_eq (cumul lo N (g x) + cumul N N' (g x) + cumul N' y (g x)));
    [|lia].
  assert (cumul N' y (fun i => Z.abs (f x i)) <= c' * cumul N' y (g x)).
  { assert (HH: forall i, N' <= i < y -> Z.abs (f x i) <= c * g x i).
    { intros. lets~ [? ?]: HN x i __. unfold Ninf in *. all: nia. }
    forwards~ HH1: cumul_le N' y (fun i => Z.abs (f x i)) (fun i => c * g x i);[].
    rewrite cumul_mul_k_le in HH1. rewrite HH1. nia. }

  assert (cumul N N' (fun i => Z.abs (f x i)) <= c * cumul N N' (g x)).
  { assert (forall i, N <= i < N' -> Z.abs (f x i) <= c * g x i).
    { intros. lets~ [? ?]: HN x i __. unfold Ninf in *. 2: nia. lia. }
    forwards~ HH1: cumul_le N N' (fun i => Z.abs (f x i)) (fun i => c * g x i);[].
    rewrite cumul_mul_k_le in HH1. rewrite HH1. nia. }

  enough (
    cumul lo N (fun i => Z.abs (f x i))
    <= (c + cc) * cumul lo N (g x) + cc * cumul N N' (g x)
  ) by (unfold c' in *; lia).

  pose (L := N - lo).
  pose (K := max_between2 (-N) N lo N (fun x y => Z.abs (f x y))).

  rewrite <-HgloN by lia. rewrite <-HgNN'.
  assert (cumul lo N (fun i => Z.abs (f x i)) <= L * K).
  { transitivity
      (cumul lo N (fun _ => max_between lo N (fun i => Z.abs (f x i)))).
    - apply cumul_le. intros. rewrite <-max_betweenP. reflexivity. all: lia.
    - rewrite cumul_const by lia. unfold L. unfold K.
      apply Z.mul_le_mono_nonneg_l; [lia|].
      unfold max_between2.
      eapply (@max_betweenP (-N) N
        (fun x => max_between lo N (fun y => Z.abs (f x y)))). all: lia. }

  enough (L * K - c * Kg <= cc * (Kg + N' - N)) by lia.
  assert (1 <= Kg + N' - N) as <-. { enough (1 + N - Kg <= N') by lia. big. }
  rewrite Z.mul_1_r. big.
  close. close.
Qed.


Section Nat_bijection.

Open Scope nat_scope.

(* 0, 1, 3, 6, 10, 15, ... *)
Definition triangle_nb (n: nat) :=
  (n * (n + 1) / 2).

Lemma triangle_0 : triangle_nb 0 = 0.
Proof. reflexivity. Qed.
Lemma triangle_S n : triangle_nb (S n) = triangle_nb n + (S n).
Proof.
  unfold triangle_nb.
  assert (n * (n+1) / 2 + S n = ((S n) * 2 + n * (n+1)) / 2) as ->.
  { rewrite Nat.div_add_l; lia. } fequal. lia.
Qed.

Definition nat_prod_encode : nat * nat -> nat :=
  fun '(m, n) => triangle_nb (m + n) + m.

Require Import FunInd Recdef.

Function nat_prod_decode_aux (k m: nat) {wf lt m} : nat * nat :=
  if le_lt_dec m k (* m <= k *) then (m, k - m)
  else nat_prod_decode_aux (S k) (m - S k).
Proof. intros k m Hkm _. lia. apply Nat.lt_wf_0. Qed.

Lemma nat_prod_decode_aux_base k m :
  m <= k -> nat_prod_decode_aux k m = (m, k - m).
Proof.
  revert k m.
  apply (@nat_prod_decode_aux_ind (fun k m x => m <= k -> x = (m, k - m))).
  now auto.
  intros * E _. destruct (le_lt_dec m k). congruence. clear E. lia.
Qed.

Lemma nat_prod_decode_aux_rec_case k m :
  m > k -> nat_prod_decode_aux k m = nat_prod_decode_aux (S k) (m - S k).
Proof.
  revert k m.
  apply (@nat_prod_decode_aux_ind
    (fun k m x => m > k -> x = nat_prod_decode_aux (S k) (m - S k))).
  { intros * E **. destruct (le_lt_dec m k); clear E; lia. }
  { auto. }
Qed.

Definition nat_prod_decode : nat -> nat * nat := nat_prod_decode_aux 0.

Lemma nat_prod_encode_prod_decode_aux k m :
  nat_prod_encode (nat_prod_decode_aux k m) = triangle_nb k + m.
Proof.
  revert k m.
  apply (@nat_prod_decode_aux_ind
    (fun k m x => nat_prod_encode x = triangle_nb k + m)).
  { intros * E. destruct (le_lt_dec m k); [clear E| congruence].
    unfold nat_prod_encode. rewrite le_plus_minus_r; auto. }
  { intros * E ->. destruct (le_lt_dec m k); [congruence | clear E].
    rewrite triangle_S. lia. }
Qed.

Lemma nat_prod_decode_inverse n : nat_prod_encode (nat_prod_decode n) = n.
Proof.
  unfold nat_prod_decode. rewrite nat_prod_encode_prod_decode_aux.
  reflexivity.
Qed.

Lemma nat_prod_decode_triangle_add k m :
  nat_prod_decode (triangle_nb k + m) = nat_prod_decode_aux k m.
Proof.
  revert m. induction k; intros m. reflexivity.
  rewrite triangle_S, <-Nat.add_assoc, IHk.
  now rewrite nat_prod_decode_aux_rec_case, minus_plus by lia.
Qed.

Lemma nat_prod_encode_inverse x : nat_prod_decode (nat_prod_encode x) = x.
Proof.
  destruct x as [m n]. unfold nat_prod_encode.
  rewrite nat_prod_decode_triangle_add.
  rewrite nat_prod_decode_aux_base. fequal; lia. lia.
Qed.

Lemma le_nat_prod_encode_1 n m : n <= nat_prod_encode (n, m).
Proof. unfold nat_prod_encode, triangle_nb. lia. Qed.

Lemma le_nat_prod_encode_2 n m : m <= nat_prod_encode (n, m).
Proof.
  revert n. induction m.
  - intros. unfold nat_prod_encode, triangle_nb. lia.
  - intros n. unfold nat_prod_encode in *.
    rewrite Nat.add_succ_r, triangle_S. specialize (IHm n). lia.
Qed.

Lemma le_nat_prod_encode_input_size : forall n m N,
  (N+1)^2 <= nat_prod_encode (n, m) ->
  N <= n + m.
Proof.
  intros *. unfold nat_prod_encode, triangle_nb.
  assert ((n + m) * (n + m + 1) = (n + m) * (n + m) + (n + m)) as -> by nia.
  intros HH.
  apply Nat.mul_le_mono_r with (p := 2) in HH.
  rewrite Nat.mul_add_distr_r in HH.
  assert (E: forall x, x / 2 * 2 <= x); [| rewrite E in HH; clear E].
  { intros. rewrite Nat.mul_comm, Nat.mul_div_le; lia. }
  rewrite Nat.pow_2_r in HH. nia.
Qed.

(* nat + nat *)

Definition nat_sum_encode : nat + nat -> nat :=
  fun x => match x with inl a => 2 * a | inr a => S (2 * a) end.

Definition nat_sum_decode : nat -> nat + nat :=
  fun n => if Even.even_odd_dec n then inl (n / 2) else inr (n / 2).

Lemma even_double : forall n, Even.even (2 * n).
Proof.
  induction n. constructor.
  assert (2 * S n = S (S (2 * n)))%nat as -> by lia.
  do 2 constructor. auto.
Qed.

Lemma odd_S_double : forall n, Even.odd (S (2 * n)).
Proof.
  intros. constructor. apply even_double.
Qed.

Lemma S_div_mult_2 : forall n, S (2 * n) / 2 = n.
Proof.
  intros. rewrite <-Nat.div2_div.
  now rewrite Div2.div2_double_plus_one.
Qed.

Lemma nat_sum_encode_inverse x : nat_sum_decode (nat_sum_encode x) = x.
Proof.
  unfold nat_sum_encode, nat_sum_decode.
  destruct x as [a|b].
  { destruct (Even.even_odd_dec (2 * a)).
    - fequal. now rewrite LibNatExtra.div_mult_2.
    - exfalso. eapply Even.not_even_and_odd; eauto. apply even_double. }
  { destruct (Even.even_odd_dec (S (2 * b))).
    - exfalso. eapply Even.not_even_and_odd; eauto. apply odd_S_double.
    - fequal. now rewrite S_div_mult_2. }
Qed.

Lemma nat_sum_decode_inverse n : nat_sum_encode (nat_sum_decode n) = n.
Proof.
  unfold nat_sum_encode, nat_sum_decode.
  destruct (Even.even_odd_dec n).
  { now rewrite <-Nat.div2_div, <-Nat.double_twice, <-Div2.even_double. }
  { now rewrite <-Nat.div2_div, <-Nat.double_twice, <-Div2.odd_double. }
Qed.

(* Z *)

Definition nat_Z_encode (x: Z) : nat :=
  nat_sum_encode (
    if Z_le_gt_dec 0 x (* 0 <= x *) then inl (Z.to_nat x)
    else inr (Z.to_nat (- x - 1))
  ).

Definition nat_Z_decode (n: nat): Z :=
  match nat_sum_decode n with inl x => Z.of_nat x | inr x => - Z.of_nat x - 1 end.

Lemma nat_Z_encode_inverse x : nat_Z_decode (nat_Z_encode x) = x.
Proof.
  unfold nat_Z_decode, nat_Z_encode; rewrite nat_sum_encode_inverse.
  destruct (Z_le_gt_dec 0 x); rewrite Z2Nat.id; lia.
Qed.

Lemma nat_Z_decode_inverse n : nat_Z_encode (nat_Z_decode n) = n.
Proof.
  unfold nat_Z_decode, nat_Z_encode.
  case_eq (nat_sum_decode n).
  { intros k Hk; rewrite Nat2Z.id. rewrite <-Hk.
    case_eq (Z_le_gt_dec 0 (Z.of_nat k)).
    { intros. now rewrite nat_sum_decode_inverse. }
    { intros. exfalso. lia. } }
  { intros k Hk. case_eq (Z_le_gt_dec 0 (- Z.of_nat k - 1)).
    { intros. exfalso. lia. }
    { intros. assert (- (- Z.of_nat k - 1) - 1 = Z.of_nat k)%Z as -> by lia.
      rewrite Nat2Z.id. now rewrite <-Hk, nat_sum_decode_inverse. } }
Qed.

Lemma le_nat_Z_encode x : Z.to_nat (Z.abs x) <= nat_Z_encode x.
Proof.
  unfold nat_Z_encode. destruct (Z_le_gt_dec 0 x).
  - cbn. rewrite Z.abs_eq by lia. lia.
  - cbn. rewrite Z.abs_neq by lia.
    rewrite Nat.add_0_r, <-Z2Nat.inj_add by lia.
    rewrite <-Z2Nat.inj_succ by lia.
    apply Z2Nat.inj_le. all:lia.
Qed.

Lemma le_nat_Z_encode_input_size x N :
  2*N+1 <= nat_Z_encode x ->
  N <= Z.to_nat (Z.abs x).
Proof.
  unfold nat_Z_encode. destruct (Z_le_gt_dec 0 x).
  - cbn. rewrite Z.abs_eq by lia. lia.
  - cbn. rewrite Z.abs_neq by lia.
    rewrite !Nat.add_0_r, <-Z2Nat.inj_add by lia.
    rewrite <-Z2Nat.inj_succ, <-Z.add_1_r by lia.
    match goal with |- context [Z.to_nat ?x] => ring_simplify x end.
    rewrite <-(Nat2Z.id (N+N+1)).
    rewrite <-Z2Nat.inj_le by lia. intro.
    rewrite <-(Nat2Z.id N), <-Z2Nat.inj_le by lia.
    rewrite !Nat2Z.inj_add in H. lia.
Qed.

(* Z <-> Z*Z *)

Definition Z_ZZ_encode : Z * Z -> Z :=
  fun '(x, y) => nat_Z_decode (
    nat_prod_encode (nat_Z_encode x, nat_Z_encode y)
  ).

Definition Z_ZZ_decode : Z -> Z * Z :=
  fun x =>
    let '(n, m) := nat_prod_decode (nat_Z_encode x) in
    (nat_Z_decode n, nat_Z_decode m).

Lemma Z_ZZ_decode_inverse x : Z_ZZ_encode (Z_ZZ_decode x) = x.
Proof.
  unfold Z_ZZ_encode, Z_ZZ_decode.
  pose (p := nat_prod_decode (nat_Z_encode x)). fold p.
  rewrite (surjective_pairing p), !nat_Z_decode_inverse.
  rewrite <-(surjective_pairing p). subst p.
  now rewrite nat_prod_decode_inverse, nat_Z_encode_inverse.
Qed.

Lemma Z_ZZ_encode_inverse p : Z_ZZ_decode (Z_ZZ_encode p) = p.
Proof.
  unfold Z_ZZ_encode, Z_ZZ_decode.
  rewrite (surjective_pairing p), !nat_Z_decode_inverse.
  now rewrite nat_prod_encode_inverse, !nat_Z_encode_inverse.
Qed.

Lemma le_Z_ZZ_encode_1 x y :
  (Z.abs x <= Z.abs (Z_ZZ_encode (x, y)))%Z.
Proof.
  unfold Z_ZZ_encode.
  lets: le_nat_prod_encode_1 (nat_Z_encode x) (nat_Z_encode y).
  (* lets: le_nat_Z_encode x. *)
Abort.

End Nat_bijection.

(* WIP.. *)
(*
Parameter i : Z*Z -> Z.
Parameter j : Z -> Z*Z.

Hypothesis ij : forall x, i (j x) = x.
Hypothesis ji : forall x, j (i x) = x.

Hypothesis i_norm_1 : forall x, Ninf x <= Z.abs (i x).

Definition Ninf3 '(x, y, z) := Z.max (Z.abs x) (Z.max (Z.abs y) (Z.abs z)).

Require Import TLC.LibIntTactics.

Lemma dominated_norm_Z3_big_sum :
  forall (f g : Z -> Z -> Z -> Z) (lo : Z),
  ultimately (measure_filterType Ninf3) (fun '(x, y, z) => 0 < g x y z) ->
  dominated (measure_filterType Ninf3)
    (fun '(x, y, z) => f x y z) (fun '(x, y, z) => g x y z) ->
  dominated (measure_filterType Ninf3)
    (fun '(x, y, z) => cumul lo y (fun i => f x y i))
    (fun '(x, y, z) => cumul lo y (fun i => g x z i)).
Proof.
  intros * U D.
  pose (f' := fun x y => f (fst (j x)) (snd (j x)) y).
  pose (g' := fun x y => g (fst (j x)) (snd (j x)) y).

  assert (ultimately (measure_filterType Ninf) (fun '(x, y) => 0 < g' x y)).
  { unfold g'. rewrite measureP. rewrite measureP in U. destruct U as [N U].
    exists N. intros [x y]. intros. refine (U (_,_,_) _). unfold Ninf, Ninf3 in *.

    lets HH: i_norm_1 (j x). rewrite ij in HH. unfold Ninf in HH.
    destruct (j x) as [j0 j1]. cbn.
    rewrite Z.max_assoc.
    assert (HHH: Z.max (Z.max (Z.abs j0) (Z.abs j1)) (Z.abs y) <=  Z.max (Z.abs x) (Z.abs y)).
    { apply Z.max_le_compat_r. auto. }



  lets: @dominated_norm_Z2_big_sum f' g' lo.
*)

(*----------------------------------------------------------------------------*)
(** Some automation *)

Hint Resolve dominated_reflexive : dominated.
Hint Extern 1 (dominated _ (fun _ => ?a) (fun _ => ?b)) =>
  apply dominated_cst : dominated.
Hint Resolve dominated_zero : dominated.
Hint Resolve dominated_cst_id : dominated.
Hint Resolve dominated_cst_limit | 2 : dominated.
Hint Resolve dominated_mul : dominated.
Hint Resolve dominated_mul_cst : dominated.
Hint Resolve dominated_mul_cst_l_1 : dominated.
Hint Resolve dominated_mul_cst_r_1 : dominated.
Hint Resolve dominated_mul_cst_l_2 : dominated.
Hint Resolve dominated_mul_cst_r_2 : dominated.
Hint Resolve dominated_max : dominated.
Hint Resolve dominated_max_distr | 10 : dominated.
Hint Resolve dominated_max_sum : dominated.
Hint Resolve dominated_min : dominated.
Hint Resolve dominated_min_distr | 10 : dominated.
Hint Resolve dominated_sum_max : dominated.
Hint Resolve dominated_sum : dominated.
Hint Resolve dominated_sum_distr : dominated.
Hint Extern 2 (dominated _ (fun _ => Z.sub _ _) _) =>
  apply dominated_sum_distr : dominated.
Hint Resolve dominated_shift : dominated.
Hint Resolve dominated_pow_r_cst_l : dominated.
Hint Resolve dominated_pow_r_cst_r : dominated.
Hint Resolve dominated_pow_l : dominated.
Hint Resolve dominated_cst_pow : dominated.
Hint Resolve dominated_log : dominated.

Hint Extern 100 => try (intros; omega) : dominated_sidegoals.

Hint Extern 999 (dominated _ _ _) => shelve : dominated_fallback.

(* TODO: make the search depth customisable *)

Ltac dominated_setup :=
  try match goal with |- dominated ?A (fun x => ?f) ?g =>
    refine (_ : dominated A (fun x : Filter.sort A => _) _)
  end;
  try match goal with |- dominated ?A ?f (fun x => ?g) =>
    refine (_ : dominated A _ (fun x : Filter.sort A => _))
  end.

Ltac dominated :=
  dominated_setup;
  unshelve (auto 20 with
                zarith typeclass_instances
                ultimately_greater
                limit
                dominated
                dominated_sidegoals
                dominated_fallback).

Ltac dominated_trysolve :=
  dominated_setup;
  auto 20 with
    zarith typeclass_instances
    ultimately_greater
    limit
    dominated
    dominated_sidegoals.
