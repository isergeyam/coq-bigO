Set Implicit Arguments.
Require Import TLC.LibTactics.
(* Load the CFML library, with time credits. *)
Require Import CFML.CFLibCredits.
(* We re-use the methodology of Procrastination, and thus some of the definition
   and tactics *)
Require Export Procrastination.Procrastination.
(* Load the BigO library. *)
Require Export Filter.
Require Export Monotonic.
Require Export Dominated.
Require Export LibFunOrd.
Require Export UltimatelyGreater.
Require Export LibZExtra.
Require Export DominatedNary.
Require Export FilterNary.
Require Export LimitNary.
Require Export Generic.
Require Export TLC.LibIntTactics.
Require Export HeapTactics.
Require Export MathTactics.
Require Export elia.
Require Export PolTac.PolTac.

(********************************************************************)

Record specO
       (A : filterType) (le : A -> A -> Prop)
       (spec : (A -> Z) -> Prop)
       (bound : A -> Z) :=
  SpecO {
      cost : A -> Z;
      spec : spec cost;
      cost_nonneg : forall x, 0 <= cost x;
      cost_monotonic : monotonic le Z.le cost;
      cost_dominated : dominated A cost bound
    }.

(********************************************************************)

(** Properties of the cost function in a specO, as separate lemmas. *)

Lemma monotonic_specO_cost :
  forall A le spec bound (S : @specO A le spec bound),
  monotonic le Z.le (cost S).
Proof.
  intros. apply cost_monotonic.
Qed.

Hint Extern 1 (monotonic _ _ (fun _ => cost ?S _)) =>
  match type of S with
  | @specO _ ?leS _ _ =>
     apply Monotonic.monotonic_comp with (leB := leS)
  end : monotonic.

Hint Extern 1 (monotonic _ _ (cost ?S)) =>
  match type of S with
  | @specO ?AS _ _ _ =>
    apply monotonic_specO_cost with (A := AS)
  end : monotonic.

Lemma monotonic_specO_nonneg :
  forall A le spec bound (S : @specO A le spec bound) x,
  0 <= cost S x.
Proof.
  intros. apply cost_nonneg.
Qed.

Hint Resolve monotonic_specO_nonneg : zarith.

Hint Resolve cost_dominated : dominated.

Instance Le_cost
  (A:filterType) le spec bound (S: specO A le spec bound) (x:A) :
  Le 0 (cost S x).
Proof. apply cost_nonneg. Qed.

(* to debug, should work but doesn't seem to. Maybe try later with typeclasses
   eauto? *)
(* Hint Extern 2 (dominated _ (fun _ => cost ?S _) _) => *)
(*       eapply dominated_transitive; *)
(*       [ apply dominated_comp with (f := cost S); *)
(*         [ apply cost_dominated | .. ] *)
(*       | ]. *)

(** *)

Inductive pack_provide_specO (A:Type) (V:A) : Prop :=
  | provide_specO : pack_provide_specO V.

(** *)

(********************************************************************)
(** rew_cost *)

Ltac rew_cost :=
  (* rew_int: FIXME *)
  repeat (
    rewrite
      ?Z.max_id,
      ?Z.add_0_l, ?Z.add_0_r,
      ?Z.mul_0_l, ?Z.mul_0_r,
      ?Zmax_0_l, ?Zmax_0_r
    by (solve [auto with zarith])
  ).

(********************************************************************)

(* Contravariant specs (wrt the cost function).

   If the spec can be proved contravariant, then the [cost_nonneg] field of
   [specO] can be proved automatically. *)

Definition spec_is_contravariant {A} (spec : (A -> Z) -> Prop) :=
  forall (cost1 cost2 : A -> Z),
  (forall x, cost1 x <= cost2 x) ->
  (spec cost1 -> spec cost2).

(* Tactic that tries to prove that a CFML spec is contravariant.

   It is generally the case for the specs with credits we consider, where the
   cost functions is used once and only in the precondition.

   More precisely, this tactic works with specifications of the form:
   [fun cost -> forall ...., app _ (\$cost (..) \* _) _] or
   [fun cost -> forall ...., app _ (\$cost (..)) _]
*)

Lemma spec_is_contravariant_lemma1 :
  forall A (cost cost' : int) (F: ~~A) Q,
  F (\$ cost') Q ->
  (cost' <= cost) ->
  is_local F ->
  F (\$ cost) Q.
Proof.
  introv HH Hcost L. xapply HH. hsimpl_credits. hsimpl. math.
Qed.

Lemma spec_is_contravariant_lemma2 :
  forall A (cost cost' : int) (F: ~~A) H Q,
  F (\$ cost' \* H) Q ->
  (cost' <= cost) ->
  is_local F ->
  F (\$ cost \* H) Q.
Proof.
  introv HH Hcost L. xapply HH. hsimpl_credits. hsimpl. math.
Qed.

Ltac spec_is_contravariant :=
  match goal with
  | |- spec_is_contravariant _ =>
    let cost1 := fresh "cost" in
    let cost2 := fresh "cost" in
    let Hcosts := fresh "Hcosts" in
    let spec_cost1 := fresh "spec_cost1" in
    intros cost1 cost2 Hcosts spec_cost1;
    intros;
    (first [
        eapply spec_is_contravariant_lemma1; [ | | xlocal]
      | eapply spec_is_contravariant_lemma2; [ | | xlocal]
      ]);
    [ | solve [ apply Hcosts ] ];
    apply spec_cost1; auto
  end.

(********************************************************************)
Definition tagged_cost_fun A (f : A -> Z) : A -> Z :=
  fun x => ??? f x ???.

(********************************************************************)
Definition cleanup_cost
           {A : filterType} (le : A -> A -> Prop)
           (cost : A -> Z)
           (bound : A -> Z) (spec : (A -> Z) -> Prop)
  :=
  sigT (fun cost_clean_eq =>
  sigT (fun cost_clean =>
    monotonic le Z.le cost_clean_eq *
    dominated A cost_clean bound *
    (spec_is_contravariant spec + (forall x, 0 <= cost_clean_eq x)) *
    dominated A cost_clean_eq cost_clean *
    (forall x, cost x = cost_clean_eq x)))%type.

Lemma cleanup_cost_tagged {A : filterType} le cost bound spec:
  @cleanup_cost A le cost bound spec ->
  @cleanup_cost A le (tagged_cost_fun cost) bound spec.
Proof.
  intros (cce & cc & [[[[? ?] ?] ?] ?]). unfold tagged_cost_fun.
  exists cce cc. split~. intros. rewrite credits_refine_eq. auto.
Qed.

Lemma cleanup_cost_alt :
  forall (A: filterType) le cost bound spec,
  @cleanup_cost A le cost bound spec ->
  monotonic le Z.le cost *
  dominated A cost bound *
  (spec cost -> specO A le spec bound).
Proof.
  intros ? ? cost.
  introv (cost_clean_eq & cost_clean & H).
  repeat (destruct H as (H & ?)).
  assert (monotonic le Z.le cost).
  { eapply Monotonic.monotonic_eq; eauto. }
  assert (dominated A cost bound).
  { eapply dominated_eq_l. eapply dominated_transitive; eauto. auto. }

  repeat split; auto; []. intro S.
  match goal with H : _ + _ |- _ => destruct H as [contra | N] end.
  { eapply SpecO with (fun x => Z.max 0 (cost x)).
    - eapply contra with cost; auto with zarith.
    - auto with zarith.
    - Monotonic.monotonic.
    - dominated. }
  { eapply SpecO with cost; auto.
    intros. match goal with H : _ |- _ => rewrite H end. auto. }
Qed.

Lemma cleanup_cost_eq : forall (A: filterType) le cost0 cost1 bound spec,
  (forall (x:A), cost0 x = cost1 x) ->
  cleanup_cost le cost1 bound spec ->
  cleanup_cost le cost0 bound spec.
Proof.
  intros * Hcost [cost_clean_eq [cost_clean [[[? ?] ?] ?]]].
  unfold cleanup_cost. exists cost_clean_eq cost_clean. split~.
  intros. rewrite Hcost. auto.
Qed.

(* TODO: implement using setoid-rewrite? *)
Ltac dominated_cleanup_cost :=
  first [
      apply dominated_sum;
      [ | | dominated_cleanup_cost | dominated_cleanup_cost];
      simpl;
      solve [ ultimately_greater_trysolve ]
    | apply dominated_max;
      [ | | dominated_cleanup_cost | dominated_cleanup_cost];
      simpl;
      solve [ ultimately_greater_trysolve ]
    | apply dominated_big_sum;
      [ | | dominated_cleanup_cost ];
      simpl;
      solve [ ultimately_greater_trysolve ]
    | apply dominated_mul_cst_l_1; dominated_cleanup_cost
    | apply dominated_mul_cst_l_2; dominated_cleanup_cost
    | apply cost_dominated; dominated_cleanup_cost
    | eapply dominated_comp;
      [ apply cost_dominated | limit ]
    | apply dominated_reflexive
    ].

(* workaround because ring_simplify apparently sometimes chokes on
   evars. *)
Ltac hide_evars_then cont :=
  match goal with
    |- context [ ?X ] =>
    is_evar X;
    let hide_X := fresh in
    set (hide_X := X);
    hide_evars_then cont;
    subst hide_X
  | _ =>
    cont tt
  end.

Ltac simple_cleanup_cost :=
  simpl; hide_evars_then ltac:(fun _ => ring_simplify).

Ltac simple_cleanup_cost_eq :=
  simpl; simple_cleanup_cost.

Ltac destruct_pair x :=
  let ty := type of x in
  let ty := eval cbv in ty in
  lazymatch ty with
  | (_ * _)%type =>
    let x1 := fresh "x" in
    let x2 := fresh "x" in
    destruct x as [x1 x2]; destruct_pair x1
  | _ => idtac
  end.

Ltac intro_destructs :=
  let x := fresh "x" in
  intro x; destruct_pair x.

(********************************************************************)

(* body is expected to be a uconstr *)
Ltac intro_cost_expr_1 A cost_name body :=
  simple refine (let cost_name := (fun (x:A) => body) : A -> Z in _); [ shelve .. | ].

(* body is expected to be a uconstr *)
Ltac intro_cost_expr_2 A cost_name body :=
  (* Ugly hack. See https://github.com/coq/coq/issues/6643 *)
  (* Was:
     refine (let cost_name := (fun '(x, y) => body) : A -> Z in _).
   *)
  let pat := fresh "pat" in
  match goal with |- ?G =>
    simple refine (let cost_name := (fun pat => let '(x,y) := pat in body) : A -> Z in _);
    try clear pat;
    [ shelve .. | ]
  end.

(* body is expected to be a uconstr *)
Ltac intro_cost_expr A cost_name body :=
  let A_sort := constr:(Filter.sort A) in
  let A_sort' := (eval compute in A_sort) in
  (* TODO: handle more arities *)
  lazymatch A_sort' with
  | (_ * _)%type => intro_cost_expr_2 A cost_name body
  | _ => intro_cost_expr_1 A cost_name body
  end.

Ltac eexists_cost_expr A :=
  let cost_name := fresh in
  intro_cost_expr A cost_name uconstr:(_);
  exists cost_name;
  subst cost_name.

(********************************************************************)
Definition close_cost (P : Type) := P.
Definition ellipsis {A} (x: A) := x.
(********************************************************************)

Ltac try_prove_nonnegative :=
  first [
      solve [ left; unfold ellipsis; spec_is_contravariant ]
    | right
    ].

Ltac cleanup_cost :=
  try apply cleanup_cost_tagged;
  match goal with |- @cleanup_cost ?A _ ?cost _ _ =>
    unfold cleanup_cost; do 2 (eexists_cost_expr A);
    try subst cost;
    split; [| intro_destructs;
              simple_cleanup_cost_eq;
              reflexivity ];
    split; [| eapply dominated_eq_r;
              [ dominated_cleanup_cost |];
              intro_destructs;
              simple_cleanup_cost;
              reflexivity ];
    split; [ split | try_prove_nonnegative ]
  end.

(********************************************************************)

Lemma specO_prove :
  forall (A : filterType) (le : A -> A -> Prop)
         (cost : A -> Z)
         (bound : A -> Z)
         (spec : (A -> Z) -> Prop),
    spec cost ->
    (spec_is_contravariant spec + (forall x, 0 <= cost x)) ->
    monotonic le Z.le cost ->
    dominated A cost bound ->
    specO A le spec bound.
Proof.
  introv S N M D.
  destruct N as [spec_contra | N].
  { pose (cost' := fun x => Z.max 0 (cost0 x)).
    apply SpecO with (cost := cost'); subst cost'.
    - eapply spec_contra with cost0; auto. math_lia.
    - math_lia.
    - Monotonic.monotonic.
    - dominated. }
  { apply SpecO with (cost := cost0); auto. }
Qed.

Lemma specO_refine_straight_line :
  forall (A : filterType) (le : A -> A -> Prop)
         (cost bound : A -> Z)
         (spec : (A -> Z) -> Prop),
    spec cost ->
    cleanup_cost le cost bound (ellipsis spec) ->
    specO A le spec bound.
Proof.
  introv H1 H2.
  forwards [[? ?] H]: cleanup_cost_alt H2.
  unfold ellipsis in *. apply~ H.
Qed.

Lemma specO_refine_recursive :
  forall (A : filterType) (le : A -> A -> Prop)
         (bound : A -> Z)
         (spec : (A -> Z) -> Prop)
         P P',
    (forall cost,
       monotonic le Z.le cost ->
       dominated A cost bound ->
       Marker.group (P cost) ->
       spec cost) ->
    close_cost
      (ellipsis ((forall cost, P' cost -> P cost) *
       sigT (fun cost =>
         P' cost *
         cleanup_cost le cost bound (ellipsis spec))))%type ->
    specO A le spec bound.
Proof.
  introv H1 H2.
  unfold close_cost in H2.
  destruct H2 as (? & cost & ? & c).
  forwards [[? ?] H]: cleanup_cost_alt c.
  unfold ellipsis in *.
  pose proof Marker.group_fold.
  apply~ H.
Qed.

Ltac close_cost :=
  unfold close_cost; unfold ellipsis;
  split; [ solve [ introv_rec; hnf; cleanup_conj_goal_core ] |];
  hnf.

Ltac xspecO_explicit_cost cost_expr :=
  match goal with |- specO ?A _ _ _ =>
    apply (@specO_prove A _ (cost_expr : A -> Z) _ _);
    [ | try_prove_nonnegative | .. ]
  end.

Ltac xspecO_refine_recursive :=
  eapply specO_refine_recursive.

(** Straight-line case *)

Ltac xspecO_refine_straight_line cost_name :=
  match goal with
    |- specO ?A ?le _ _ =>
    intro_cost_expr A cost_name uconstr:(_);
    eapply (@specO_refine_straight_line A le (@tagged_cost_fun A cost_name));
    [ unfold tagged_cost_fun, cost_name | ]
  end.

Tactic Notation "xspecO" uconstr(cost_expr) :=
  xspecO_explicit_cost cost_expr.

Tactic Notation "xspecO_refine" "straight_line" ident(cost_name) :=
  xspecO_refine_straight_line cost_name.

Tactic Notation "xspecO_refine" "straight_line" :=
  let costf := fresh "costf" in
  xspecO_refine_straight_line costf.

Tactic Notation "xspecO_refine" "recursive" :=
  xspecO_refine_recursive.

Notation "'(...)'" := (ellipsis _) (at level 0).

(* Notations for common [specO]s *)

Notation "'specZ' [ X '\in_O' f ] E" :=
  (specO Z_filterType Z.le (fun X => E) f)
    (X ident, f at level 90, E at level 0,
     format "'[v' 'specZ'  [ X  '\in_O'  f ]  '/'  E ']'", at level 60).

Notation "'spec1' [ X ] E" :=
  (specO unit_filterType eq (fun X => E) (fun tt => 1))
    (X ident, E at level 0,
     format "'[v' 'spec1'  [ X ]  '/'  E ']'", at level 60).

(* Custom CF rules and tactics ************************************************)

(** *)

Class GetCreditsEvar (h h' : hprop) (c : int) :=
  MkGetCreditsEvar : h = h' \* \$ c.

Instance GetCreditsEvar_inst : forall h h' h'' c,
  HeapPreprocessCredits h h' ->
  GetCreditsExpr h' ???c??? h'' ->
  GetCreditsEvar h h'' c.
Proof.
  intros.
  unfold HeapPreprocessCredits, GetCreditsExpr,
    GetCreditsEvar in *.
  rewrite credits_refine_eq in *.
  now subst.
Qed.

Ltac tryif_refine_cost_goal ifyes ifno :=
  first [
    match goal with |- _ ?pre _ =>
      let H := fresh "HGCE" in
      eassert (GetCreditsEvar pre _ _) as H;
      [ once (typeclasses eauto) | ];
      once (ifyes H);
      clear H
    end
  | once (ifno tt)
  ].

(** *)

(* Custom xspec to fetch specO specifications *)

(* FIXME: copy-pasted from CFML *)
Ltac xspec_core_base f :=
  first [ xspec_for_record f
        | xspec_in_hyps_core f
        (* FUTURE: | xspec_in database_spec_credits f *)
        | xspec_in_core database_spec f
        | xspec_app_in_hyps f
        | fail 1 "xspec cannot find specification" ].

(* TODO? S might start with some forall/hypothesis before the specO --
   turn these into evars/subgoals using
   refine (fun X => _ (X _)); swap 1 2; [..|clear X; loop...]
*)
Ltac spec_of_specO :=
  lazymatch goal with
  | |- pack_provide_specO ?S -> _ =>
    intros _; generalize (spec S)
  end.

Ltac xspec_core f ::=
  xspec_core_base f; try spec_of_specO.

(* weaken **************)

Inductive weaken_arg :=
| Auto : weaken_arg
| Expr : int -> weaken_arg.

Class WeakenFindArg (h1 : hprop) (arg : weaken_arg) (h2 : hprop) (c : int) :=
  MkWeakenFindArg : GetCreditsExpr h1 c h2.

Instance WeakenFindArg_auto_unique: forall h h' c,
  HasSingleCreditsExpr h h' c ->
  WeakenFindArg h Auto h' c.
Proof. now unfold HasSingleCreditsExpr, GetCreditsExpr. Qed.

Instance WeakenFindArg_auto_refine: forall h h' c,
  GetCreditsExpr h ???c??? h' ->
  WeakenFindArg h Auto h' c.
Proof.
  intros. unfold WeakenFindArg. now rewrite credits_refine_eq in *. Qed.

Instance WeakenFindArg_expr: forall h h' c,
  GetCreditsExpr h c h' ->
  WeakenFindArg h (Expr c) h' c.
Proof. now unfold GetCreditsExpr. Qed.

(* weaken

   Applies to a goal with some credit cost, and turns it into a goal where the
   number of credits is an evar (so that the _refine tactics can apply).
   Produces a side-condition requiring that the evar cost is less than the
   original cost.

   Is also useful if the original number of credits _is_ an evar, but with a
   context that doesn't allow directly instanting it. Calling this tactic
   introduces a new evar in the local context, plus a subgoal where the user can
   explain how to instantiate the evar with the restricted context.
*)
Lemma weaken_credits arg :
  forall A (cost_weakened cost : int) (F: ~~A) H H' Q,
  WeakenFindArg H arg H' cost ->
  F (\$ ??? cost_weakened ??? \* H') Q ->
  (cost_weakened <= cost) ->
  is_local F ->
  F H Q.
Proof.
  introv -> HH Hcost L.
  xapply HH.
  { hsimpl_credits. }
  { hsimpl. rewrite credits_refine_eq. math. }
Qed.

Ltac weaken_core arg :=
  eapply (@weaken_credits arg);
  [ once (typeclasses eauto) | | | xlocal ].

Tactic Notation "weaken" := weaken_core Auto.
Tactic Notation "weaken" uconstr(arg) :=
  let earg := uconstr:(Expr arg) in
  weaken_core earg.

(** *)

(* stop_refine

   The opposite operation of refine: instantiates the evar for the number of
   credits with 0. *)

Lemma stop_refine_credits :
  forall A (F: ~~A) c H H' Q,
  GetCreditsEvar H H' c ->
  c = 0 ->
  F H' Q ->
  is_local F ->
  F H Q.
Proof.
  introv ? ? HH ?.
  unfold Unify, GetCreditsEvar in *. subst.
  rewrite credits_zero_eq. xapply~ HH.
Qed.

Ltac stop_refine :=
  eapply stop_refine_credits; [
    once (typeclasses eauto)
  | reflexivity | | xlocal ].

(* cutO *)

Lemma cutO_refine :
  forall (A : filterType) le B (bound : A -> Z) (F: ~~B) H Q (a: A),
  forall S : specO A le (fun cost => forall a, F (\$ cost a \* H) Q) bound,
  F (\$ ???(cost S) a??? \* H) Q.
Proof.
  introv. rewrite credits_refine_eq. destruct S. simpl. auto.
Qed.

(* hsimpl *****************************)

(** refine credits *)

Class GetFrame (h1 h2 frame : hprop) :=
  MkGetFrame : h1 = h2 \* frame.

Class GetFrame' (h1 h2 frame : hprop) :=
  MkGetFrame' : GetFrame h1 h2 frame.

Instance GetFrame_of': forall h1 h2 frame,
  GetFrame' h1 h2 frame ->
  GetFrame h1 h2 frame.
Proof. eauto. Qed.

Hint Mode GetFrame' ! - - : typeclass_instances.

Instance GetFrame'_star_l : forall h1 h1' h2 h1'h2 frame,
  GetFrame h1 h1' frame ->
  Star h1' h2 h1'h2 ->
  GetFrame' (h1 \* h2) h1'h2 frame.
Proof.
  introv -> <-. unfold GetFrame', GetFrame.
  now rewrite <-!star_assoc, (star_comm frame).
Qed.

Instance GetFrame'_star_r: forall h1 h2 h2' h1h2' frame,
  GetFrame h2 h2' frame ->
  Star h1 h2' h1h2' ->
  GetFrame' (h1 \* h2) h1h2' frame.
Proof.
  introv -> <-. unfold GetFrame', GetFrame.
  now rewrite star_assoc.
Qed.

Instance GetFrame_frame: forall h,
  IsEvar h ->
  GetFrame h \[] h.
Proof. introv _. unfold GetFrame. now rewrite star_neutral_l. Qed.

Class SplitFrameIfPresent (lhs hsource htarget hsource' htarget' : hprop) :=
  MkSplitFrameIfPresent : hsource \* htarget = hsource' \* htarget'.

Instance SplitFrameIfPresent_has_frame_lhs_emp: forall lhs hs hs' f ht htf,
  IsNotEvar lhs ->
  Unify lhs \[] ->
  GetFrame hs hs' f ->
  Star ht f htf ->
  SplitFrameIfPresent lhs hs ht hs' htf.
Proof.
  introv _ ->. unfold GetFrame. intros ->. unfold Star. intros <-.
  unfold SplitFrameIfPresent.
  now rewrite <-star_assoc, (star_comm f).
Qed.

Instance SplitFrameIfPresent_hasframe: forall lhs hs hs' f H1 H2 ht hs'H1 htH2,
  GetFrame hs hs' f ->
  Unify f (H1 \* H2) ->
  Star hs' H1 hs'H1 ->
  Star ht H2 htH2 ->
  SplitFrameIfPresent lhs hs ht hs'H1 htH2
| 20.
Proof.
  introv -> ->. unfold Star. introv <- <-. unfold SplitFrameIfPresent.
  now rewrite <-!star_assoc, (star_comm H2).
Qed.

Instance SplitFrameIfPresent_noframe: forall lhs hs ht,
  SplitFrameIfPresent lhs hs ht hs ht | 100.
Proof. reflexivity. Qed.

Class SplitGCIfPresent (hsource htarget hsource' htarget' : hprop) :=
  MkSplitGCIfPresent : hsource \* htarget = hsource' \* htarget'.

Instance SplitGCIfPresent_hasGC: forall hs hs' ht htGC,
  RemoveGC hs hs' ->
  Star ht \GC htGC ->
  SplitGCIfPresent hs ht hs htGC.
Proof.
  introv -> <-. unfolds.
  now rewrite <-!star_assoc, (star_comm _ \GC), (star_assoc \GC), GCGC_eq_GC.
Qed.

Instance SplitGCIfPresent_noGC: forall hs ht,
  SplitGCIfPresent hs ht hs ht | 100.
Proof. reflexivity. Qed.

Lemma himpl_credits_subgoal: forall h1 h1' h2 h2' h2'' h2''' l1 l2 hc1 hc2 hc2' hc2'',
  GetCredits h1 h1' l1 ->
  GetCredits h2 h2' l2 ->
  CreditsHeap l1 hc1 ->
  CreditsHeap l2 hc2 ->
  SplitFrameIfPresent h1' h2' hc2 h2'' hc2' ->
  SplitGCIfPresent h2'' hc2' h2''' hc2'' ->
  h1' ==> h2''' ->
  hc1 ==> hc2'' ->
  h1 ==> h2.
Proof.
  introv -> -> -> -> -> -> HH1 HH2. hchange HH1. hchange HH2. hsimpl.
Qed.

(* Fail if the goal does not contain credits, instead of producing a trivial
   subgoal *)
Ltac himpl_credits_subgoal :=
  match goal with |- _ ==> _ =>
  match goal with |- context [ \$ _ ] =>
    eapply himpl_credits_subgoal; [ once (typeclasses eauto) .. | | ]
  end end.

(********************)

(* These cleanup tactics are a bit ad-hoc. Maybe all of [hsimpl_cleanup] should
   be implemented in this style, instead of trying to minimize the diff and
   match the input expected by the existing tactics. *)

Lemma cleanup_emp: forall h1 h1' h2 h2',
  CleanupEmp h1 h1' ->
  CleanupEmp h2 h2' ->
  h1' ==> h2' ->
  h1 ==> h2.
Proof. introv -> ->. eauto. Qed.

Ltac cleanup_emp tt :=
  eapply cleanup_emp; [ once (typeclasses eauto) .. |].

(* This is because HasGC might split the frame evar to introduce a \GC, and we
   might want to get rid of it afterwards.. *)

Lemma hsimpl_cancel_GC_lhs : forall HL HL' HA HR,
  RemoveGC HL HL' ->
  HL' ==> (\GC \* HA) \* HR -> (* keep \GC *)
  HL ==> HA \* \GC \* HR.
Proof.
  introv -> HH. hchange HH.
  rewrite (star_assoc _ \GC), (star_comm _ \GC), <-!star_assoc.
  rewrite (star_assoc \GC), GCGC_eq_GC.
  hsimpl.
Qed.

Ltac hsimpl_cancel_GC_lhs tt :=
  eapply hsimpl_cancel_GC_lhs; [ once (typeclasses eauto) |].

(* TEMPORARY TODO: put into CFML *)
Ltac hsimpl_hook H ::=
  match H with
  | \GC => hsimpl_cancel_GC_lhs tt
  end.

(* Terminates goals of the form:

  H ==> H
  ... ==> ?H  (by instantiating H with the left-hand side)
  ... ==> \GC  (by potentially producing "affine .." subgoals)

  and does nothing on other goals.
*)
Ltac hsimpl_cleanup_trysolve :=
  try apply pred_incl_refl;
  try hsimpl_hint_remove tt;
  try remove_empty_heaps_right tt;
  try remove_empty_heaps_left tt;
  try apply hsimpl_gc;
  try affine.

Ltac hsimpl_cleanup tt ::=
  try apply hsimpl_stop;
  try apply hsimpl_stop;
  try cleanup_emp tt;
  try himpl_credits_subgoal;
  match goal with
  | |- context [ \$ ??? _ ??? ] =>
    (* Avoid instantiating the frame with the credits in that case, and keep
       them in a separate goal (propagating the \$ ???_??? in the frame is rarely
       something that we want to do). *)
       idtac
  | |- _ ==> _ =>
    hsimpl_cleanup_trysolve
  | _ =>
    idtac
  end.

Goal forall H1 H2 c2, exists c1 H3,
  H1 \* \$ ???c1??? ==> H2 \* \$ c2 \* H3.
Proof.
  intros. do 2 eexists. hsimpl.
Abort.

Goal forall H1 c2, exists c1 H3,
  H1 \* \$ ???c1??? ==> H1 \* \$ c2 \* H3.
Proof.
  intros. do 2 eexists. hsimpl; [].
Abort.

(*************************)

(* Tactics on heap implications with credits *)

Lemma piggybank_inst_with_expr x : forall h1 h2 h1' h2' p,
  GetCreditsEvar h1 h1' p ->
  GetCreditsExpr h2 x h2' ->
  Unify p x ->
  h1' ==> h2' ->
  h1 ==> h2.
Proof. introv -> -> -> HH. xchange HH. hsimpl. Qed.

Ltac piggybank_inst_with_expr x :=
  eapply (@piggybank_inst_with_expr x); [ once (typeclasses eauto) .. |].

Tactic Notation "piggybank:" uconstr(x) :=
  piggybank_inst_with_expr x.

Lemma piggybank_refine_with_expr x : forall h1 h2 h1' h2' p p',
  GetCreditsEvar h1 h1' p ->
  GetCreditsExpr h2 x h2' ->
  Unify p (x + p') ->
  \$ ???p'??? \* h1' ==> h2' ->
  h1 ==> h2.
Proof.
  introv -> -> -> HH. rewrite credits_split_eq, <-(credits_refine_eq p').
  now xchange HH.
Qed.

Ltac piggybank_refine_with_expr x :=
  eapply (@piggybank_refine_with_expr x); [ once (typeclasses eauto) .. |].

Tactic Notation "piggybank+" uconstr(x) :=
  piggybank_refine_with_expr x.

Definition Piggybank (c : int) := c.

Ltac set_Piggybank :=
  match goal with |- context [ Piggybank ?x ] =>
    let p := fresh "p" in
    set (p := x)
  end.

Class ChooseIneqOrEq (rhs: hprop) (cmp: int -> int -> Prop) :=
  MkChooseIneqOrEq : (rhs = rhs \* \GC /\ cmp = Z.le) \/ (cmp = eq).

Instance ChooseIneqOrEq_ineq: forall rhs,
  HasGC rhs ->
  ChooseIneqOrEq rhs Z.le.
Proof. intros. unfolds. left~. Qed.

Instance ChooseIneqOrEq_eq: forall rhs,
  ChooseIneqOrEq rhs eq | 100.
Proof. intros. right~. Qed.

Lemma piggybank_credits_ineq: forall h1 h2 l1 l2 h1' h1'' h2' p l1' c1 c2 cmp,
  ChooseIneqOrEq h2 cmp ->
  GetCreditsEvar h1 h1' p ->
  GetCredits h1' h1'' l1 ->
  GetCredits h2 h2' l2 ->
  AddIntList l2 c2 ->
  Snoc l1 (Piggybank ???p???) l1' ->
  AddIntList l1' c1 ->
  cmp c2 c1 ->
  h1'' ==> h2' ->
  h1 ==> h2.
Proof.
  introv Hcmp -> -> -> -> -> -> Hc HH. unfold ChooseIneqOrEq in Hcmp.
  rewrite big_add_snoc in Hc. unfold heap_is_credits_list in *. hchange HH.
  unfold Piggybank in *. rewrite credits_refine_eq in Hc.
  destruct Hcmp as [ [-> ->] | -> ].
  { hsimpl_credits. math. }
  { rewrite Hc. hsimpl_credits. }
Qed.

Lemma piggybank_inst_0_credits_ineq: forall h1 h2 l1 l2 h1' h1'' h2' p c1 c2 cmp,
  ChooseIneqOrEq h2 cmp ->
  GetCreditsEvar h1 h1' p ->
  Unify p 0 ->
  GetCredits h1' h1'' l1 ->
  GetCredits h2 h2' l2 ->
  AddIntList l2 c2 ->
  AddIntList l1 c1 ->
  cmp c2 c1 ->
  h1'' ==> h2' ->
  h1 ==> h2.
Proof.
  introv Hcmp -> -> -> -> -> -> Hc HH. unfold ChooseIneqOrEq in Hcmp.
  unfold heap_is_credits_list in *. hchange HH. rewrite credits_zero_eq.
  destruct Hcmp as [[-> ->] | ->].
  { hsimpl_credits. math. }
  { rewrite Hc. hsimpl_credits. }
Qed.

(* This is because HasGC might split the frame evar to introduce a \GC, and we
   might want to get rid of it afterwards.. *)
Lemma cleanup_GC_star_evar: forall h1 h2,
  h1 ==> h2 ->
  h1 ==> \GC \* h2.
Proof.
  introv HH. hchange HH. hsimpl.
Qed.

Ltac cleanup_GC_star_evar :=
  match goal with |- _ ==> \GC \* ?h =>
    is_evar h;
    apply cleanup_GC_star_evar
  end.

Ltac piggybank_credits_ineq :=
  eapply piggybank_credits_ineq;
  [ once (typeclasses eauto) ..
  | set_Piggybank
  | try cleanup_GC_star_evar;
    hsimpl_cleanup_trysolve
  ].

Tactic Notation "piggybank:" "*" :=
  piggybank_credits_ineq.

Ltac solve_trivial_ineq :=
  match goal with
  | |- 0 <= 0 => apply Z.le_refl
  | |- 0 = 0 => apply eq_refl
  end.

Ltac piggybank_inst_0_credits_ineq :=
  eapply piggybank_inst_0_credits_ineq;
  [ once (typeclasses eauto) ..
  | try solve_trivial_ineq
  | try cleanup_GC_star_evar; hsimpl_cleanup_trysolve ].

Tactic Notation "piggybank:" "*0" :=
  piggybank_inst_0_credits_ineq.

(* TODO: also handle inequalities (x <= y + Piggybank p) *)
Lemma piggybank_credits_ineq_done : forall x p,
  p = x ->
  x <= Piggybank ???p???.
Proof. introv ->. rewrite credits_refine_eq. reflexivity. Qed.

Lemma piggybank_credits_eq_done : forall x p,
  p = x ->
  x = Piggybank ???p???.
Proof. introv ->. rewrite credits_refine_eq. reflexivity. Qed.

Ltac piggybank_credits_ineq_done :=
  match goal with |- context [ Piggybank ?p ] => subst p end;
  first [ apply piggybank_credits_ineq_done
        | apply piggybank_credits_eq_done ];
  reflexivity.

Tactic Notation "piggybank:" "*" "done" :=
  piggybank_credits_ineq_done.

(*********************************)

(* "Pay with piggybank" (riskier):
   ????c??? \* H1 ==> \$ a \* \$ b \* H2  ~>  c := a + b

   even if there are other credits in the left-hand side
*)

Lemma pay_with_piggybank: forall h1 h1' h2 h2' c1 l2 c2,
  GetCreditsEvar h1 h1' c1 ->
  GetCredits h2 h2' l2 ->
  AddIntList l2 c2 ->
  Unify c1 c2 ->
  h1' ==> h2' ->
  h1 ==> h2.
Proof.
  introv -> -> -> -> H. xchange H. hsimpl.
Qed.

Ltac piggybank_pay_rhs :=
  eapply pay_with_piggybank; [ once (typeclasses eauto) .. |];
  hsimpl_cleanup_trysolve.

Tactic Notation "piggybank:" "*rhs" :=
  piggybank_pay_rhs.

(** current hsimpl_credits: join the lhs, substract the rhs *)

Lemma substract_left_right_credits: forall h1 h1' h2 h2' l1 l2 c1 c1c2,
  GetCredits h1 h1' l1 ->
  GetCredits h2 h2' l2 ->
  AddIntList l1 c1 ->
  SubIntList c1 l2 c1c2 ->
  \$ c1c2 \* h1' ==> h2' ->
  h1 ==> h2.
Proof.
  introv -> -> -> -> HH.
  rewrite big_sub_big_add in HH.
  unfold heap_is_credits_list.
  assert (big_add l1 = (big_add l1 - big_add l2) + big_add l2) as -> by math.
  rewrite credits_split_eq.
  hchange HH. hsimpl.
Qed.

Ltac substract_credits :=
  match goal with |- context [ \$ _ ] =>
    eapply substract_left_right_credits; [ once (typeclasses eauto) .. |];
    hsimpl_cleanup_trysolve
  end.

(* TEMPORARY we can redefine hsimpl_credits as follows: *)

Ltac hsimpl_credits_core ::=
  hsimpl; try substract_credits.

(*****************************************)

Ltac hcancel_autorefine_credits :=
  hcancel; try piggybank: *rhs.

Ltac hsimpl_autorefine_credits :=
  hsimpl; try piggybank: *rhs.

Ltac xapp_xapply_with_simpl K ::=
  first
  [ applys K  (* useful for specifications that are CF *)
  | xapply_core K ltac:(fun _ => hsimpl_autorefine_credits) ltac:(fun _ => try xok) ].

Ltac xapplys_base H ::=
  xpull_check_not_needed tt;
  xapply_core H ltac:(fun tt => hcancel_autorefine_credits) ltac:(fun tt => hsimpl_autorefine_credits).

(* FIXME FIXME: fix xchange instead *)
Ltac xopen_core t ::=
  let C1 := xopen_constr t in
  ltac_database_get database_xopen C1;
  let K := fresh "TEMP" in
  intros K; xchange_base ltac:(fun tt => hsimpl; hsimpl_cleanup_trysolve) (K t) __; clear K.

Ltac xclose_core args ::=
  let args := list_boxer_of args in
  let C1 := xclose_constr args in
  ltac_database_get database_xclose C1;
  let K := fresh "TEMP" in
  intros K;
  let E := constr:((boxer K)::args) in
  xchange_base ltac:(fun tt => hsimpl; hsimpl_cleanup_trysolve) E __;
  clear K.

(* xcf ******************************************)

(* This is to ensure that credits are put at the head of the precondition. *)

Ltac xcf_post tt ::=
  cbv beta;
  remove_head_unit tt;
  hclean.

(* xpay *****************************************)

Lemma xpay_refine :
  forall A (F: hprop -> (A -> hprop) -> Prop),
  forall cost cost' H H' Q,
  is_local F ->
  GetCreditsEvar H H' cost ->
  cost = 1 + cost' ->
  F (\$ ???cost'??? \* H') Q ->
  (Pay_ ;; F) H Q.
Proof.
  introv L -> -> HH. rewrite credits_refine_eq in *.
  xpay_start tt.
  { unfold pay_one. rewrite credits_split_eq. hsimpl. }
  xapplys HH.
Qed.

Ltac xpay_refine_core HGCE :=
  eapply xpay_refine; [ xlocal | apply HGCE | reflexivity | xtag_pre_post ].

Ltac standard_xpay tt :=
  (xpay_start tt; [ unfold pay_one; hsimpl | xtag_pre_post ]).

Ltac xpay_core tt ::=
  tryif_refine_cost_goal
    xpay_refine_core
    standard_xpay.

(* xapply *****************************)

(* This is useful for cases where the goal is

     [F (\$ ????c??? \* H) (Q \* \$ x)]

   and we do xapp/xapply: we want to split ?c to be able to pay for [\$ x]
   later...
*)

Lemma local_frame_gc_with_credits :
  forall B H1 H2 (Q1: B->hprop) (F:~~B) H H' Q c c1 c2,
  GetCreditsEvar H H' c ->
  c = c1 + c2 ->
  is_local F ->
  F H1 Q1 ->
  \$ ???c1??? \* H' ==> H1 \* H2 ->
  Q1 \*+ (\$ ???c2??? \* H2) ===> Q \*+ \GC ->
  F H Q.
Proof.
  introv -> -> L F1 HI1 HI2. rewrite credits_refine_eq in *.
  rewrite credits_split_eq.
  xapply F1. xchange HI1. hsimpl. xchange HI2. hsimpl.
Qed.

Ltac cfml_postcondition_contains_credits tt :=
  let Q := cfml_get_postcondition tt in
  lazymatch Q with
  | context [ \$ _ ] => constr:(true : bool)
  | _ => constr:(false : bool)
  end.

Ltac xapply_refine_core H cont1 cont2 HGCE :=
  forwards_nounfold_then H ltac:(fun K =>
    match cfml_postcondition_is_evar tt with
    | true => eapply local_frame; [ xlocal | sapply K | cont1 tt | try xok ]
    | false =>
      match cfml_postcondition_contains_credits tt with
      | true =>
        eapply local_frame_gc_with_credits;
        [ apply HGCE | reflexivity | xlocal | sapply K | cont1 tt | cont2 tt ]
      | false =>
        eapply local_frame_gc; [ xlocal | sapply K | cont1 tt | cont2 tt ]
      end
    end).

Ltac xapply_standard_core H cont1 cont2 tt :=
  forwards_nounfold_then H ltac:(fun K =>
  match cfml_postcondition_is_evar tt with
  | true => eapply local_frame; [ xlocal | sapply K | cont1 tt | try xok ]
  | false => eapply local_frame_gc; [ xlocal | sapply K | cont1 tt | cont2 tt ]
  end).

Ltac xapply_core H cont1 cont2 ::=
  tryif_refine_cost_goal
    ltac:(xapply_refine_core H cont1 cont2)
    ltac:(xapply_standard_core H cont1 cont2).

(* xret *******************************)

Lemma refine_zero_credits : forall A (F:~~A) H H' c (Q : A -> hprop),
  GetCreditsEvar H H' c ->
  c = 0 ->
  local F H' Q ->
  local F H Q.
Proof.
  introv -> -> HH. now rewrite credits_zero_eq, star_neutral_r.
Qed.

Ltac refine_zero_credits HGCE :=
  eapply refine_zero_credits; [ apply HGCE | reflexivity | ].

Ltac try_refine_zero_credits :=
  tryif_refine_cost_goal ltac:(refine_zero_credits) ltac:(fun _ => idtac).

Ltac xret_apply_lemma tt ::=
  try_refine_zero_credits;
  first [ apply xret_lemma_unify
        | apply xret_lemma ].

Ltac xret_no_gc_core tt ::=
  try_refine_zero_credits;
  first [ apply xret_lemma_unify
        | eapply xret_no_gc_lemma ].

(* xseq *******************************)

Lemma xseq_refine :
  forall (A : Type) cost cost1 cost2 F1 F2 H H' (Q : A -> hprop),
  GetCreditsEvar H H' cost ->
  cost = cost1 + cost2 ->
  is_local F1 ->
  is_local F2 ->
  (exists Q',
    F1 (\$ ???cost1??? \* H') Q' /\
    F2 (\$ ???cost2??? \* Q' tt) Q) ->
  (F1 ;; F2) H Q.
Proof.
  introv -> -> L1 L2 (Q' & H1 & H2). rewrite credits_refine_eq in *.
  xseq_pre tt. apply local_erase. eexists. split.
  { xapply H1. credits_split. hsimpl. }
  { xapply H2. hsimpl. hsimpl. }
Qed.

Ltac xseq_refine_core HGCE :=
  eapply xseq_refine; [ apply HGCE | reflexivity | xlocal | xlocal | ].

Ltac xseq_standard_core tt :=
  apply local_erase.

Ltac xseq_core cont0 cont1 ::=
  (tryif_refine_cost_goal xseq_refine_core xseq_standard_core);
  cont0 tt;
  split; [ | cont1 tt ];
  xtag_pre_post.

(* xlet *****************************************)

Lemma xlet_refine :
  forall
    (A B : Type) cost cost1 cost2
    (F1 : hprop -> (A -> hprop) -> Prop)
    (F2 : A -> hprop -> (B -> hprop) -> Prop)
    (H H' : hprop) (Q : B -> hprop),
  GetCreditsEvar H H' cost ->
  cost = cost1 + cost2 ->
  is_local F1 ->
  (forall x, is_local (F2 x)) ->
  (exists (Q' : A -> hprop),
    F1 (\$ ???cost1??? \* H') Q' /\
    (forall r, F2 r (\$ ???cost2??? \* Q' r) Q)) ->
  cf_let F1 F2 H Q.
Proof.
  introv -> -> L1 L2 (Q' & H1 & H2). rewrite credits_refine_eq in *.
  unfold cf_let.
  eexists. split.
  { xapply H1. credits_split. hsimpl. }
  { intro r. specializes L2 r. xapply H2; hsimpl. }
Qed.

Ltac xlet_refine_core cont0 cont1 cont2 HGCE :=
  apply local_erase;
  match goal with |- cf_let ?F1 (fun x => _) ?H ?Q =>
    eapply xlet_refine; [ apply HGCE | reflexivity | xlocal | intro; xlocal | ];
    cont0 tt;
    split; [ | cont1 x; cont2 tt ];
    xtag_pre_post
  end.

Ltac xlet_standard_core cont0 cont1 cont2 tt :=
  apply local_erase;
  match goal with |- cf_let ?F1 (fun x => _) ?H ?Q =>
    cont0 tt;
    split; [ | cont1 x; cont2 tt ];
    xtag_pre_post
  end.

Ltac xlet_core cont0 cont1 cont2 ::=
  tryif_refine_cost_goal
    ltac:(xlet_refine_core cont0 cont1 cont2)
    ltac:(xlet_standard_core cont0 cont1 cont2).

(* xif ********************************)

Lemma xif_refine : forall (A: Type) cost cost1 cost2 cond (F1 F2: ~~A) H H' Q,
  GetCreditsEvar H H' cost ->
  cost = Z.max cost1 cost2 ->
  is_local F1 ->
  is_local F2 ->
  ((cond = true -> F1 (\$ ???cost1??? \* H') Q) /\
   (cond = false -> F2 (\$ ???cost2??? \* H') Q)) ->
  (If_ cond Then F1 Else F2) H Q.
Proof.
  introv -> -> L1 L2 (H1 & H2). rewrite credits_refine_eq in *.
  apply local_erase.
  split; intro; [xapply~ H1 | xapply~ H2]; hsimpl_credits;
  math_lia.
Qed.

Ltac xif_refine_core HGCE :=
  eapply xif_refine; [ apply HGCE | reflexivity | xlocal | xlocal | ].

Ltac xif_standard_core tt :=
  xuntag tag_if; apply local_erase.

Ltac xif_base cont1 cont2 ::=
  xpull_check_not_needed tt;
  xif_check_post_instantiated tt;
  let cont tt :=
    tryif_refine_cost_goal xif_refine_core xif_standard_core;
    split; [ cont1 tt | cont2 tt ];
    xtag_pre_post
  in
  match cfml_get_tag tt with
  | tag_if => cont tt
  | tag_let => xlet; [ cont tt | instantiate ]
  end.

(* xif_guard: prototype *)

Lemma xif_guard_refine :
  forall (A: Type) cost cost1 cost2 (cond cond': bool) (F1 F2: ~~A) H H' Q,
  GetCreditsEvar H H' cost ->
  (cost = If cond' then cost1 else cost2) ->
  (cond = cond') ->
  is_local F1 ->
  is_local F2 ->
  ((cond = true -> F1 (\$ ???cost1??? \* H') Q) /\
   (cond = false -> F2 (\$ ???cost2??? \* H') Q)) ->
  (If_ cond Then F1 Else F2) H Q.
Proof.
  introv -> -> costE L1 L2 (H1 & H2). rewrite credits_refine_eq in *.
  apply local_erase. rewrite costE.
  split; intro C; rewrite C; cases_if; [xapply~ H1 | xapply~ H2].
Qed.

Ltac xif_guard_refine_core cont HGCE :=
  eapply xif_guard_refine;
  [ apply HGCE | reflexivity | try reflexivity | xlocal | xlocal | ];
  [ .. | split; cont tt; xtag_pre_post ].

Ltac xif_guard_core H :=
  tryif_refine_cost_goal
    ltac:(xif_guard_refine_core ltac:(fun _ => intro H; xif_post H))
    ltac:(fun tt => fail 100 "No credit evar found").

Tactic Notation "xif_guard" "as" ident(H) :=
  xif_guard_core H.
Tactic Notation "xif_guard" :=
  let H := fresh "C" in xif_guard as H.

(* xguard ***************************************)

Lemma xguard_refine :
  forall A (cost cost' : int) (F: ~~A) (G: Prop) H H' Q,
  GetCreditsEvar H H' cost ->
  (cost = If G then cost' else 0) ->
  G ->
  F (\$ ???cost'??? \* H') Q ->
  F H Q.
Proof.
  introv -> -> HG HH. rewrite credits_refine_eq in *. cases_if.
  now rewrite star_comm.
Qed.

Ltac xguard G :=
  tryif_refine_cost_goal
    ltac:(fun HGCE =>
      eapply xguard_refine; [ apply HGCE | reflexivity | eexact G | ])
    ltac:(fun tt =>
      fail 100 "No credit evar found").

(* xfor *****************************************)

(* TODO: prove using xfor_inv_case_lemma_refine instead of directly *)
Lemma xfor_inv_lemma_pred_refine :
  forall
    (I : int -> hprop)
    cost (cost_body : int -> int)
    (a : int) (b : int) (F : int-> ~~unit) H H1 H',
  GetCreditsEvar H H1 cost ->
  cost = cumul a b cost_body ->
  (a <= b) ->
  (forall i, a <= i < b -> F i (\$ ???cost_body i??? \* I i) (# I(i+1))) ->
  (H1 ==> I a \* H') ->
  (forall i, is_local (F i)) ->
  (For i = a To (b - 1) Do F i Done_)
    H
    (# I b \* H').
Proof.
Admitted. (* TODO *)


Lemma xfor_inv_case_lemma_refine : forall (I:int->hprop),
   forall (cost : int) (cost_body : int -> int),
   forall (a:int) (b:int) (F:int->~~unit) H H1 (Q:unit->hprop),
   GetCreditsEvar H H1 cost ->
   ((a <= b) -> exists H',
          (H1 ==> I a \* H')
       /\ (forall i, is_local (F i))
       /\ (forall i, a <= i <= b -> F i (\$ ???cost_body i??? \* I i) (# I(i+1)))
       /\ (cost = cumul a b cost_body)
       /\ (I (b+1) \* H' ==> Q tt \* \GC)) ->
   ((a > b) ->
          (cost = 0)
       /\ (H1 ==> Q tt \* \GC)) ->
   (For i = a To b Do F i Done_) H Q.
Proof.
Admitted. (* TODO *)

Lemma xfor_inv_lemma_refine : forall (I:int->hprop),
  forall cost (cost_body : int -> int),
  forall (a:int) (b:int) (F:int->~~unit) H H1 H',
  GetCreditsEvar H H1 cost ->
  (cost = cumul a (b + 1) cost_body) ->
  (a <= b+1) ->
  (forall i, a <= i <= b -> F i (\$ ???cost_body i??? \* I i) (# I(i+1))) ->
  (H1 ==> I a \* H') ->
  (forall i, is_local (F i)) ->
  (For i = a To b Do F i Done_)
    H
    (# I (b+1) \* H').
Proof using.
Admitted. (* TODO *)

Lemma xfor_inv_void_lemma_refine :
  forall (a:int) (b:int) (F:int->~~unit) H H' (cost : int),
  GetCreditsEvar H H' cost ->
  cost = 0 ->
  (a > b) ->
  (For i = a To b Do F i Done_) H (# H').
Proof using.
Admitted. (* TODO *)

Ltac xfor_inv_refine_core I HGCE :=
  first [
      eapply (@xfor_inv_lemma_pred_refine I)
    | eapply (@xfor_inv_lemma_refine I) ];
  [ apply HGCE | reflexivity | | xtag_pre_post | | intro; xlocal ].

Ltac xfor_inv_standard_core I tt :=
  first [
      apply (@xfor_inv_lemma_pred I)
    | apply (@xfor_inv_lemma I) ];
  [ | xtag_pre_post | | intro; xlocal ].

Ltac xfor_inv_core I ::=
  xfor_pre_ensure_evar_post ltac:(fun _ =>
    tryif_refine_cost_goal
      ltac:(xfor_inv_refine_core I)
      ltac:(xfor_inv_standard_core I)).

Ltac xfor_inv_void_core tt ::=
  xfor_pre_ensure_evar_post ltac:(fun _ =>
    tryif_refine_cost_goal
      ltac:(fun HGCE =>
        eapply (@xfor_inv_void_lemma_refine);
        [ apply HGCE | reflexivity ])
      ltac:(fun tt =>
        apply (@xfor_inv_void_lemma))).

(* TODO: xfor_inv_case *)

(* xcase ****************************************)

Lemma cf_max_credits_weaken_l :
  forall B (F : ~~B) H Q c1 c2,
    is_local F ->
    F (\$ ???c1??? \* H) Q ->
    F (\$ Z.max c1 c2 \* H) Q.
Proof.
  introv ? HH. rewrite credits_refine_eq in *. xapply HH. hsimpl_credits.
  hsimpl. math_lia.
Qed.

Lemma cf_max_credits_weaken_r :
  forall B (F : ~~B) H Q c1 c2,
    is_local F ->
    F (\$ ???c2??? \* H) Q ->
    F (\$ Z.max c1 c2 \* H) Q.
Proof.
  introv ? HH. rewrite credits_refine_eq in *. xapply HH. hsimpl_credits.
  hsimpl. math_lia.
Qed.

Lemma xcase_refine :
  forall (B:Type) (Case1 Case2: ~~B) c c1 c2 H H' (Q: B -> hprop),
    GetCreditsEvar H H' c ->
    c = Z.max c1 c2 ->
    (Case1 (\$ c \* H') Q) ->
    (Case2 (\$ c \* H') Q) ->
    (tag tag_case (local (fun H Q => Case1 H Q /\ Case2 H Q))) H Q.
Proof.
  introv -> -> HT HF. unfold tag. apply local_erase.
  now rewrite star_comm.
Qed.

Ltac xcase_refine_sidecondition_1 :=
  eapply cf_max_credits_weaken_l; [ xlocal |].

Ltac xcase_refine_sidecondition_2 :=
  eapply cf_max_credits_weaken_r; [ xlocal |].

Ltac xcase_core H cont1 cont2 ::=
  tryif_refine_cost_goal
    ltac:(fun HGCE =>
      eapply xcase_refine; [
        apply HGCE | reflexivity
      | introv H; xcase_refine_sidecondition_1; cont1 tt
      | introv H; xcase_refine_sidecondition_2; xtag_negpat H; cont2 tt ];
      xtag_pre_post)
    ltac:(fun tt =>
      (* original CFML implementation *)
      xuntag tag_case; apply local_erase; split;
      [ introv H; cont1 tt
      | introv H; xtag_negpat H; cont2 tt ];
      xtag_pre_post).

Ltac xcase_no_intros_core cont1 cont2 ::=
  tryif_refine_cost_goal
    ltac:(fun HGCE =>
      eapply xcase_refine; [
        apply HGCE | reflexivity
      | pose ltac_mark; introv ?; xcase_refine_sidecondition_1; gen_until_mark;
        cont1 tt
      | pose ltac_mark; introv ?; xcase_refine_sidecondition_2; gen_until_mark;
        cont2 tt
      ];
      xtag_pre_post)
    ltac:(fun tt =>
      (* original CFML implementation *)
      xuntag tag_case; apply local_erase; split;
      [ cont1 tt
      | cont2 tt ];
      xtag_pre_post).

Ltac xcase_post_cfml H :=
  (* original CFML implementation *)
  try solve [ discriminate | false; congruence ];
  try (symmetry in H; inverts H; xclean_trivial_eq tt).

(* Use backtracking to instantiate the goal with zero credits only if we manage
   to prove it afterwards *)
Ltac xcase_post H ::=
  tryif_refine_cost_goal
    ltac:(fun HGCE =>
      first [
        refine_zero_credits HGCE;
        solve [ xcase_post_cfml H ]
      | xcase_post_cfml H ])
    ltac:(fun tt =>
      xcase_post_cfml H).

(* xfail ****************************************)

Ltac xfail_core tt ::=
  xpull_check_not_needed tt;
  xuntag tag_fail;
  try_refine_zero_credits;
  apply local_erase;
  xtag_pre_post.

(* xdone ****************************************)

(* Unfortunately, this is not enough: we cannot override the previous uses of
   the notation. This is why we also need to redefine the tactics that were
   using xdone... (see below). *)

Tactic Notation "xdone" :=
  xuntag tag_done;
  try_refine_zero_credits;
  apply local_erase; split.

Ltac xmatch_case_core cont_case ::=
  match cfml_get_tag tt with
  | tag_done => xdone
  | tag_fail => xfail
  | tag_case => cont_case tt
  | _ => fail 100 "unexpected tag in xmatch_case"
  end.

Ltac xstep_once tt :=
  match cfml_get_tag tt with
  | tag_ret => xret
  | tag_apply => xapp
  | tag_none_app => xapp
  | tag_record_new => xapp
  | tag_val => xval
  | tag_fun => xfun
  | tag_let => xlet
  | tag_match => xmatch
  | tag_case => xcase
  | tag_fail => xfail
  | tag_done => xdone
  | tag_alias => xalias
  | tag_seq => xseq
  | tag_if => xif
  | tag_for => fail 1
  | tag_while => fail 1
  | tag_assert => xassert
  | tag_pay => xpay
  | _ =>
     match goal with
     | |- _ ==> _ => first [ xsimpl | fail 2 ]
     | |- _ ===> _ => first [ xsimpl | fail 2 ]
     end
  end.

(*******************)

(* TODO: move to CFML *)

Tactic Notation "xapp_spec_no_simpl" constr(H) :=
  xapp_no_simpl_core H (>>) ltac:(fun _ => idtac).
Tactic Notation "xapp_spec_no_simpl" constr(H) constr(E) :=
  xapp_no_simpl_core H E ltac:(fun _ => idtac).
