Set Implicit Arguments.
Require Import TLC.LibTactics.
Require Import TLC.LibIntTactics.
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
(* Load the custom CFML tactics with support for big-Os *)
Require Import CFMLBigO.
(* Load the examples CF definitions. *)
Require Import Examples_ml.

(* Prove specifications for auxiliary functions [tick] and [rand].

   - [tick ()] just does one step of computation and consumes one credit

   - [rand n] returns an integer between 0 and n.

     It is used to account for the case where a function specification only
     relates the arguments and the result value with an inequality.
*)

Lemma tick_spec :
  app tick [tt]
    PRE (\$1)
    POST (fun (tt:unit) => \[]).
Proof. xcf. xpay. xret. hsimpl. Qed.

Hint Extern 1 (RegisterSpec tick) => Provide tick_spec.

Lemma rand_spec :
  forall (n:Z),
  0 <= n ->
  app rand [n]
    PRE (\$1)
    POST (fun m => \[0 <= m <= n]).
Proof.
  intros n N.
  xcf. xpay. xret. hsimpl. math.
Qed.

Hint Extern 1 (RegisterSpec rand) => Provide rand_spec.

(* [tick3 ()]: calls [tick ()] three times.

   First, prove a big-O specification by providing the exact cost function
   upfront (here, λ(). 4).

   The specification is stated using [specO], which takes several arguments:

   - a filter; here [unit_filterType] as [tick3] is "O(1)"
   - a (pre-order) relation on the domain (the cost function must be monotonic
     wrt this relation)
   - the specification, as a function [abstract cost function -> Prop]
   - the big-O bound for the cost function
*)
Lemma tick3_spec :
  specO
    unit_filterType eq
    (fun cost =>
       app tick3 [tt]
           PRE (\$ cost tt)
           POST (fun (tt:unit) => \[]))
    (fun tt => 1).
Proof.
  xspecO (fun _ => 4).

  { xcf.
    xpay.
    (* after a [pay] or a [xapp], one needs to justify that one has enough
       credits in the precondition to pay for the operation. *)
    hsimpl_credits; math.
    xseq.
    xapp. hsimpl_credits; math.
    xapp. hsimpl_credits; math.
    xapp. }

  (* Justify that the cost function is monotonic and dominated by
     the bound given in the specification ([fun tt => 1]). *)
  { monotonic. }
  { dominated. }
Qed.

Hint Extern 1 (RegisterSpec tick3) => Provide (provide_specO tick3_spec).

Lemma credits_move_post : forall A (F:~~A) c Q,
  is_local F ->
  F \[] (Q \*+ \$ (-c)) ->
  F (\$ c) Q.
Proof.
  introv HL HF. xframe (\$ c). apply HF. intros ?.
  hsimpl. rewrite credits_join_eq, Z.add_opp_diag_r, credits_zero_eq.
  hsimpl.
Qed.

Lemma tick3_spec2 :
  specO
    unit_filterType eq
    (fun cost =>
       app tick3 [tt]
           PRE (\$ cost tt)
           POST (fun (tt:unit) => \[]))
    (fun tt => 1).
Proof.
  xspecO_refine recursive. intros. xcf.
  (* apply credits_move_post; [ xlocal |]. *)
  xpay.
  match goal with |- ?H ==> _ =>
    apply pred_incl_trans with (H \* \$ 0);
    only 1: rewrite credits_zero_eq; hsimpl
  end.
  asserts_rewrite~ (0 = 1 + -1). rewrite <-credits_join_eq. hsimpl.
  xapp.
  match goal with |- ?H ==> _ =>
    apply pred_incl_trans with (H \* \$ 0);
    only 1: rewrite credits_zero_eq; hsimpl
  end.
  asserts_rewrite~ (0 = 1 + -1). rewrite <-credits_join_eq. hsimpl.
  xapp.
  match goal with |- ?H ==> _ =>
    apply pred_incl_trans with (H \* \$ 0);
    only 1: rewrite credits_zero_eq; hsimpl
  end.
  asserts_rewrite~ (0 = 1 + -1). rewrite <-credits_join_eq. hsimpl.
  xapp.
  match goal with |- ?H ==> _ =>
    apply pred_incl_trans with (H \* \$ 0);
    only 1: rewrite credits_zero_eq; hsimpl
  end.
  asserts_rewrite~ (0 = 1 + -1). rewrite <-credits_join_eq.

  (* (*!*) hsimpl *)
  rewrite !credits_join_eq. hsimpl_credits. rewrite le_zarith.
  ring_simplify. defer.

  close_cost.
Abort.

(*
Lemma tick3_spec2 :
  specO
    unit_filterType eq
    (fun cost =>
       app tick3 [tt]
           PRE (\$ cost tt)
           POST (fun (tt:unit) => \[]))
    (fun tt => 1).
Proof.
  xspecO_refine recursive. intros. xcf.
  (* apply credits_move_post; [ xlocal |]. *)
  xpay.


  instantiate (1 := (\$ (-1)) \* _).
  rewrite star_assoc.
  rewrite credits_join_eq, Z.add_opp_diag_r, credits_zero_eq. hsimpl.
  xapp.
  instantiate (1 := \$ (-1) \* _).
  rewrite star_assoc.
  rewrite (credits_join_eq 1), Z.add_opp_diag_r, credits_zero_eq. hsimpl.
  xapp.
  instantiate (1 := \$ (-1) \* _).
  rewrite (star_assoc (\$ 1)).
  rewrite (credits_join_eq 1), Z.add_opp_diag_r, credits_zero_eq. hsimpl.
  xapp.
  hsimpl_credits. rewrite le_zarith.
  ring_simplify.
*)

(* [tick3 ()]: prove the same specification, this time using the mechanism to
   refine cost functions semi-automatically.

   In simple cases like this one, [cleanup_cost] is able to completely clean up
   the refined cost function. [monotonic] is also able to automatically prove
   monotonicity of the refined cost function *before* cleanup.

   The monotonicity goal is (at the moment) about the "uncleaned" cost function,
   because the "cleaning" process produces a cost function that is not equal to the
   uncleaned one, and only dominates it.
*)
Lemma tick3_spec2 :
  specO
    unit_filterType eq
    (fun cost =>
       app tick3 [tt]
           PRE (\$ cost tt)
           POST (fun (tt:unit) => \[]))
    (fun tt => 1).
Proof.
  xspecO_refine straight_line.
  xcf.
  xpay.
  xseq. xapp.
  xapp. xapp.

  cleanup_cost.

  monotonic.
  dominated.
Qed.

(* [tick31]: Using a big-O spec for an auxiliary function. *)
Lemma tick31_spec :
  specO
    unit_filterType eq
    (fun cost =>
       app tick31 [tt]
           PRE (\$ cost tt)
           POST (fun (tt:unit) => \[]))
    (fun _ => 1).
Proof.
  xspecO_refine straight_line.
  xcf. xpay.
  xapp. (* usual spec *)
  xapp. (* big-O spec *)

  cleanup_cost.

  monotonic.
  dominated.
Qed.

(* [loop1 n]: loops from 1 to n, calls [tick (); tick ()] at each iteration.

   The custom rule [xfor_inv] refines the cost function to a [cumul] of the cost
   of the loop's body.

   Also, demo of a convenince wrapper notation for [specO] on [Z_filterType].
*)
Lemma loop1_spec :
  specZ [cost \in_O (fun n => n)]
    (forall (n: Z),
       0 <= n ->
       app loop1 [n]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[])).
Proof.
  xspecO_refine straight_line.
  intros n N.
  xcf.
  xpay.

  xfor_inv (fun (i:int) => \[]). math.
  { intros i Hi.
    xpay.
    xseq.
    xapp. xapp. }
  hsimpl. hsimpl.

  cleanup_cost.

  { monotonic. }

  { dominated.
    rewrite dominated_big_sum_bound.
    { apply dominated_mul_cst_l_2. reflexivity. }
    ultimately_greater.
    apply filter_universe_alt. monotonic.
  }
Qed.

Hint Extern 1 (RegisterSpec loop1) => Provide (provide_specO loop1_spec).

(* [let1]: a program of the form [let m = ... in ...] where the cost of the body
   of the [let] depends on [m].

   As [m] is a locally-bound variable, one needs to come up with a cost for the
   body that is independent from [m]. In this simple example, it suffices to
   inline the definition of [m]. *)
Lemma let1_spec :
  specO
    Z_filterType Z.le
    (fun cost =>
       forall n,
       0 <= n ->
       app let1 [n]
         PRE (\$ cost n)
         POST (fun (tt:unit) => \[]))
    (fun n => n).
Proof.
  xspecO_refine straight_line.
  intros n N.

  xcf.
  xpay.

  xlet.
  { xseq. xapp. xret. }
  { xpull. intro Hm. weaken. xapp. math.
    (* This sub-goal is produced by our custom [xlet], and requires the user to
    come up with a cost-function (hence the meta-variable) which only depends on
    [n]. *)
    (* Here, it suffices to inline the definition of [m]. *)
    subst m.
    (* [reflexivity] then unifies both sides, instantiating the meta-variable
    and solving the goal. *)
    reflexivity. }

  cleanup_cost.
  monotonic.
  dominated.
Qed.

(* In the previous example, we got away with using [reflexivity] to instantiate
   the evar in [... <= ?Goal{x:=n}].

   In more general cases, we want to manually give an instantiation for the
   evar. One way of doing that is by applying the following (trivial) lemma,
   giving an instantiation for [b]. *)
Lemma le_than (b: Z): forall a, a <= b -> a <= b.
Proof. auto. Qed.

Arguments le_than : clear implicits.

(* [let2]: of the form [let m = ... in ...], where the cost of the body depends
   on [m].

   This time however, [m] is only related to [n] by an inequality (we
   know [m <= n]). We cannot simply [subst] the definition of [m]. Instead we
   use monotonicity of cost functions and [le_than].
*)
Lemma let2_spec :
  specO
    Z_filterType Z.le
    (fun cost => forall n,
         0 <= n ->
         app let2 [n]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[]))
    (fun n => n).
Proof.
  dup.
  { (* either anticipate, and call weaken beforehand *)
    xspecO_refine straight_line. intros n N.
    xcf. xpay. xlet.
    { xapp~. }
    { xpull. intro Hm. (* here *) weaken. xapp. math.
      apply (le_than (cost loop1_spec n)).
      apply cost_monotonic. math. }
    cleanup_cost. monotonic. dominated. }

  { (* or use the fancy/half broken piggybank tactics *)
    xspecO_refine straight_line. intros n N.
    xcf. xpay. xlet. { xapp~. }
    { xpull. intro Hm. (* no weaken *) xapp. math.
      Fail piggybank: *rhs. (* expected: lhs and rhs do not unify *)
      piggybank: *. transitivity (cost loop1_spec n). now apply cost_monotonic.
      piggybank: * done. }
    cleanup_cost. monotonic. dominated. }
Qed.

(* [loop2]: Similarly, we can have a for-loop where the value of the starting
   and finishing indices is not precisely known, but one can bound their
   difference. *)
Lemma loop2_spec :
  specO
    Z_filterType Z.le
    (fun cost =>
       forall n,
         0 <= n ->
         app loop2 [n]
             PRE (\$ cost n)
             POST (fun (tt:unit) => \[]))
    (fun n => n).
Proof.
  xspecO_refine straight_line.
  intros n N.

  xcf. xpay.

  xlet. { xapp~. }
  xpull. intros Ha.
  xlet. { xapp~. }
  xpull. intros Hb.

  weaken. xfor_inv (fun (i:int) => \[]). math.
  { intros i Hi. xpay. xapp. }
  { hsimpl. }
  { hsimpl. }
  { (* At this point, we can simply reduce [cumul] of a constant to a product.
    *)
    rewrite cumulP. rewrite big_const_Z.
    (* Do some cleanup, and work around the fact that [ring_simplify] chokes on
    evars... *)
    hide_evars_then ltac:(fun _ => ring_simplify).
    apply (le_than (2 * n)).
    math. }

  cleanup_cost.

  monotonic.
  dominated.
Qed.

(* [if1]: Similarly, a program of the form [if cond then ... else ...], where
   the cost of branches can only be related to the input parameter by an
   inequality. *)
Lemma if1_spec :
  specO
    Z_filterType Z.le
    (fun cost => forall n (cond: bool),
         0 <= n ->
         app if1 [n cond]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[]))
    (fun n => n).
Proof.
  dup.
  { xspecO_refine straight_line.
    intros n cond N.
    xcf. xpay.
    xapp~. intro Ha.
    xapp~. intro Hb.

    xif.
    { weaken. xapp. math.
      (* Bound the cost of the branch by something that only depends on [n], using
         the fact that [loop1_cost] is monotonic. *)
      apply (le_than (cost loop1_spec n)). apply cost_monotonic. math. }
    { weaken. xapp. math. apply (le_than (cost loop1_spec n)). apply cost_monotonic. math. }

    cleanup_cost.
    monotonic.
    dominated. }

  { xspecO_refine straight_line. intros n cond N.
    xcf. xpay. xapp~. intro Ha. xapp~. intro Hb.
    xif.
    { xapp. math. piggybank: *. transitivity (cost loop1_spec n).
      now apply cost_monotonic. piggybank: * done. }
    { xapp. math. piggybank: *. transitivity (cost loop1_spec n).
      now apply cost_monotonic. piggybank: * done. }
    cleanup_cost. monotonic. dominated. }
Qed.

(* [looploop]: nested for-loops *)
Lemma looploop_spec :
  specO
    Z_filterType Z.le
    (fun cost => forall n,
       0 <= n ->
       app looploop [n]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[]))
    (fun n => n ^ 2).
Proof.
  xspecO_refine straight_line.
  intros n N.
  xcf. xpay.

  xfor_inv (fun (i:int) => \[]). auto.
  { intros i I.
    xpay. xfor_inv (fun (j:int) => \[]). math.
    { intros j J. xpay. xapp. }
    { hsimpl. } { hsimpl. }
  }
  { hsimpl. } { hsimpl. }

  cleanup_cost.
  (* FIXME *) (* monotonic. *) admit.

  dominated.
  { rewrite dominated_big_sum_bound.
    { apply dominated_mul. reflexivity.
      dominated. rewrite dominated_big_sum_bound. dominated.
      ultimately_greater.
      (* todo: improve *)
      eapply ultimately_monotonic_of_monotonic.
      monotonic. }
    ultimately_greater. ultimately_greater. (* FIXME *)
    (* todo: improve *)
    eapply ultimately_monotonic_of_monotonic.
    monotonic.
  }
Admitted.

(**
   WIP: attempts at abstracting the big-O cost of the inner loop, in the middle
   of the proof.
 *)

Lemma cutO_refine :
  forall (A : filterType) le (bound : A -> Z) (F: A -> hprop -> Prop) H,
  forall S : specO A le (fun mycost => forall a, F a (\$ (mycost a) \* H)) bound,
  forall (a:A),
  F a (\$ ⟨(cost S) a⟩ \* H).
Proof.
  intros. destruct S. simpl. rewrite credits_refine_eq. eauto.
Qed.

Lemma cutO_refine' :
  forall (A : filterType) le (bound : A -> Z) (spec: (A -> Z) -> Prop),
  forall S : specO A le spec bound,
  spec (cost S).
Proof.
  intros. destruct S. simpl in *. auto.
Qed.

Lemma xfor_inv_lemma_pred_refine :
  forall
    (I : int -> hprop) (loop_cost : int)
    (bound : int -> int)
    (a : int) (b : int) (F : int-> ~~unit) H H',
  (a <= b) ->
  forall S :
  specO Z_filterType Z.le (fun mycost =>
    forall i, a <= i < b -> F i (\$ (mycost i) \* I i) (# I(i+1))) bound,
  (H ==> I a \* H') ->
  (forall i, is_local (F i)) ->
  (cumul a b (fun i => (cost S i)) <= loop_cost) ->
  (For i = a To (b - 1) Do F i Done_) (\$ loop_cost \* H) (# I b \* H').
Proof.
  admit.
Admitted.

(* ... *)
Hypothesis dominated_big_sum_Z_alt :
  forall (f g : Z -> Z) (lo : Z),
  (forall i, lo <= i -> 0 <= f i) ->
  (forall i, lo <= i -> 0 <= g i) ->
  dominated Z_filterType f g ->
  monotonic (le_after lo Z.le) Z.le f ->
  dominated Z_filterType (fun n => cumul lo n f) (fun n => cumul lo n g).

Lemma looploop_spec' :
  specO
    Z_filterType Z.le
    (fun cost => forall n,
       0 <= n ->
       app looploop [n]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[]))
    (fun n => n ^ 2).
Proof.
  xspecO_refine straight_line.
  intros n N.
  xcf. xpay.

  xfor_inv (fun (i:int) => \[]).
  math. intros i Hi.
  Set Printing Existential Instances.

  match goal with |- PRE (\$ ⟨?f i⟩ \* _) POST _ CODE _ =>
    set (mycost := f)
  end.
  revert i Hi.

  unshelve eapply cutO_refine'
    with (A := Z_filterType) (le := Z.le) (bound := fun (i:int) => i).
  (* { xspecO_refine straight_line. intros. xpay. *)
  (*   xfor_inv (fun (_:int) => \[]). math. intros. xpay. xapp~. hsimpl. hsimpl. *)
  (*   cleanup_cost. monotonic. dominated. admit. (* ok *) } *)

  (*
  x : Z_filterType
  ============================
  specZ [mycost \in_O (fun i : int => i)]
   (forall i : int,
    0 <= i < x ->
    PRE \$mycost i \* \[]
    POST fun _ : unit => \[]
    CODE Pay_ ;; (For _ = 0 To (i - 1) Do
                  Pay_ ;; App tick tt;
                   Done_)  )
  *)
  { abstract skip. }
  hsimpl. hsimpl.

  cleanup_cost.
  { admit. }
  { cut (dominated Z_filterType
           (fun x => x * (cost (looploop_spec'_subproof x)) x)
           (fun n => n * n)). { admit. (* monotonicity *) }
    cut (dominated Z_filterType
           (fun x => cost (looploop_spec'_subproof x) x) (fun x => x)).
    { intro. dominated. }
    (* ... *)
    admit.
  }
Admitted.

Lemma looploop_spec'_alt :
  specO
    Z_filterType Z.le
    (fun cost => forall n,
       0 <= n ->
       app looploop [n]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[]))
    (fun n => n ^ 2).
Proof.
  xspecO_refine straight_line.
  intros n N.
  xcf. xpay.

  xfor_inv (fun (i:int) => \[]).
  math. intros i Hi.
  Set Printing Existential Instances.

  unshelve eapply cutO_refine
    with (A := Z_filterType) (a := i) (le := Z.le) (bound := fun (i:int) => i).
  simpl.

  (*
  x : Z_filterType
  i : int
  ============================
  specZ [mycost \in_O (fun i0 : int => i0)]
   (forall a : int,
    PRE \$mycost a \* \[]
    POST fun _ : unit => \[]
    CODE Pay_ ;; (For _ = 0 To (a - 1) Do
                  Pay_ ;; App tick tt;
                   Done_)  )
  *)

  (* { simpl. xspecO_refine straight_line. intros. xpay. *)
  (*   xfor_inv (fun (_:int) => \[]). admit. (* fixme *) intros. xpay. xapp. hsimpl. hsimpl. *)
  (*   cleanup_cost. simpl. monotonic. admit. (* ok *) } *)
  { abstract skip. }

  hsimpl. hsimpl.
  cleanup_cost.
  { monotonic. }
  { dominated. dup.
    { etransitivity.
      (* apply dominated_big_sum. *) (* ... *)
      apply dominated_big_sum_Z_alt.
      { auto with zarith. }
      2: apply cost_dominated.
      { auto with zarith. }
      { monotonic.
        apply monotonic_after_of_monotonic. monotonic. }
      { admit. } }

    { cut (dominated Z_filterType
                     (fun x => x * cost looploop_spec'_alt_subproof x)
                     (fun n => n^2)). { admit. (* monotonicity *) }
      (* .. *) eapply dominated_eq_r; swap 1 2.
      { intro. (* argh *) hide_evars_then ltac:(fun _ => rewrite Z.pow_2_r).
        reflexivity. }
      dominated. } }
Admitted.

(*
Lemma looploop_spec :
  specO
    Z_filterType Z.le
    (fun cost => forall n,
       0 <= n ->
       app looploop [n]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[]))
    (fun n => n ^ 2).
Proof.
  xspecO.
  intros n N.
  xcf. xpay.

  xfor_pre_ensure_evar_post ltac:(fun _ => idtac).
  unshelve eapply xfor_inv_lemma_pred_refine
  with (bound := fun _ => n)
       (I := fun i => \[]).
  shelve.
  - admit.
  - auto.
  - hsimpl.
  - intro. xlocal.
  - reflexivity.
  - hsimpl.
  - subst cost.
    unfold cleanup_cost.
    apply dominated_max0.
    eapply dominated_sum. Focus 3. apply dominated_reflexive. ultimately_greater.
    Focus 2.
    apply dominated_max0.
    apply dominated_big_sum' with (g := fun n i => n).
    Focus 3.
    (* apply dominated_max0. *) (* ehhh *)
    apply dominated_max0_product.

    Check cost_dominated.

    apply dominated_reflexive.

    ultimately_greater.
    apply filter_universe_alt. auto using cost_nonneg.
    intros. apply monotonic_after_of_monotonic. monotonic. applys cost_monotonic Z_filterType. (* xx *)
    limit.

    simpl.
    apply ultimately_ge_0_cumul_nonneg_Z. auto using cost_nonneg.

  - admit.
  - simpl.
    apply dominated_sum_distr. apply dominated_cst_id.
    eapply dominated_transitive.
    { apply dominated_big_sum'.
      { apply filter_universe_alt. auto using cost_nonneg. }
      Focus 2.
      {
*)

(**
   WIP: attempts at semi-manually handling recursive functions.
*)

(* NB: Adding the precondition [0 <= n] to the specification doesn't help
   simplifying the cost functions and getting rid of the Z.max. Indeed, [specO]
   requires that the provided cost function is always nonnegative — which is not
   the case of e.g. [fun n => n + 1].
*)
Lemma rec1_spec :
  specO
    Z_filterType Z.le
    (fun cost => forall n,
         app rec1 [n]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[]))
    (fun n => n).
Proof.
  xspecO (fun n => Z.max 0 n + 1).
  intro n.
  induction_wf: (downto 0) n.

  xcf. weaken.
  xpay.
  (* when the sub-cost functions for the branches of the if need to talk about of/depend on
  the condition... *)
  xif_guard. (* xif *) xret. hsimpl. (* xguard C *) xapp. math.

  cases_if; math_lia.

  monotonic.
  dominated.
Qed.

Require Import Procrastination.Procrastination.

Lemma rec1_spec2 :
  specO
    Z_filterType Z.le
    (fun cost => forall n,
         app rec1 [n]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[]))
    (fun n => n).
Proof.
  begin defer.

  evar (a : int). evar (b : int).
  defer a_nonneg: (0 <= a).
  defer b_nonneg: (0 <= b).

  xspecO (fun n => a * Z.max 0 n + b).
  intro n.
  induction_wf: (wf_downto 0) n.

  xcf. weaken.
  xpay. xif. xret. hsimpl. xguard C. xapp. math.

  cases_if. rew_cost.
  { generalize n C. defer. }
  { generalize n C. defer. }

  monotonic.
  dominated.
  end defer.

  (* XX *)
Abort.

Lemma rec1_spec3 :
  specO
    Z_filterType Z.le
    (fun cost => forall n,
         app rec1 [n]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[]))
    (fun n => n).
Proof.
  begin defer assuming a b.

  defer a_nonneg: (0 <= a).
  defer b_nonneg: (0 <= b).

  xspecO (fun n => a * Z.max 0 n + b).
  intro n.
  induction_wf: (wf_downto 0) n.

  xcf. weaken.
  xpay. xif. xret. hsimpl. xguard C. xapp. math.

  cases_if.
  { generalize n C. defer. }
  { generalize n C. defer. }

  monotonic.
  dominated.
  end defer.

  simpl. exists 1 1. splits; math_nia.
Qed.

Lemma rec1_spec4 :
  specO
    Z_filterType Z.le
    (fun cost => forall n,
         0 <= n ->
         app rec1 [n]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[]))
    (fun n => n).
Proof.
  begin defer assuming a b.

  defer a_nonneg: (0 <= a).
  defer b_nonneg: (0 <= b).

  xspecO (fun n => Z.max 0 (a * n + b)).
  intros n.
  induction_wf: (wf_downto 0) n. intro N.

  xcf. weaken.
  xpay. xif. xret. hsimpl. xguard C. xapp. math. math.

  cases_if.
  { generalize n N C. defer. }
  { generalize n N C. defer. }

  monotonic.
  dominated.
  end defer.

  simpl. exists 1 1. splits.
  math. math. math_nia. math_nia.
Qed.

Lemma rec1_spec5 :
  specO
    Z_filterType Z.le
    (fun cost => forall n,
         0 <= n ->
         app rec1 [n]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[]))
    (fun n => n).
Proof.
  begin defer assuming a b.

  defer a_nonneg: (0 <= a).
  defer b_nonneg: (0 <= b).

  xspecO (fun n => a * n + b).
  intro n. induction_wf: (wf_downto 0) n. intro N.

  xcf. weaken.
  xpay. xif. xret. hsimpl. xguard C. xapp. math. math.

  cases_if.
  { generalize n N C. defer. }
  { generalize n N C. defer. }

  monotonic.
  dominated.
  end defer.

  simpl. exists 1 1. splits.
  math. math. math_nia. math_nia.
Qed.

Lemma rec1_spec6 :
  specO
    Z_filterType Z.le
    (fun cost => forall n,
         0 <= n ->
         app rec1 [n]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[]))
    (fun n => n).
Proof.
  xspecO_refine recursive. intros rec_cost ? ? ?.
  intro n. induction_wf: (wf_downto 0) n. intro N.

  xcf. weaken.
  xpay. xif_guard. xret. hsimpl. xapp. math. math.

  cases_if.
  { ring_simplify. generalize n N. defer. }
  { generalize n N C. defer. }

  close_cost.

  simpl.
  begin defer assuming a b. exists (fun (n:Z_filterType) => a * n + b).
  defer a_nonneg: (0 <= a). repeat split.
  { intros ? H. cancel n. defer. }
  { intros n N N'. cancel n. defer. }

  cleanup_cost.
  { monotonic. }
  { dominated. }
  end defer. elia.
Qed.


Parameter tree : Type.
Parameter size : tree -> Z.
Parameter height : tree -> Z.
Parameter balanced : tree -> Prop.

Parameter search : func.

Parameter search_spec :
  specZ [cost \in_O (fun n => n)]
    (forall (t: tree),
       app search [t]
         PRE (\$ cost (height t))
         POST (fun (_:Z) => \[])).

Hypothesis tree_height_bound : forall (t: tree),
  balanced t ->
  height t <= Z.log2 (size t).

Hypothesis height_nonneg : forall t, 0 <= height t.

Lemma search_spec_balanced :
  specZ [cost \in_O (fun n => Z.log2 n)]
    (forall (t: tree),
       balanced t ->
       app search [t]
         PRE (\$ cost (size t))
         POST (fun (_:Z) => \[])).
Proof.
  xspecO_refine straight_line. intros t HB.
  weaken. xapplys search_spec.
  apply cost_monotonic. (* apply tree_height_bound. *)
  rewrite tree_height_bound. sets sz: (size t). reflexivity.
  assumption.

  cleanup_cost. monotonic. dominated.
Qed.

(**********)

Parameter search_spec' :
  specO (@invimage_filterType Z_filterType tree height) eq
    (fun cost => forall (t: tree),
       app search [t]
         PRE (\$ cost t)
         POST (fun (_:Z) => \[]))
    (fun x => height x).

Parameter search_spec'' :
  specO (@invimage_filterType Z_filterType tree size) eq
    (fun cost => forall (t: tree),
       app search [t]
         PRE (\$ cost t)
         POST (fun (_:Z) => \[]))
    (fun x => height x).

Lemma search_spec_balanced' :
  specO (within_filterType (@invimage_filterType Z_filterType tree height) balanced) eq
    (fun cost => forall (t: tree),
       balanced t ->
       app search [t]
         PRE (\$ cost t)
         POST (fun (_:Z) => \[]))
    (fun x => Z.log2 (size x)).
Proof.
  xspecO_refine straight_line. intros. xapplys search_spec'.
  try apply cleanup_cost_tagged.
  match goal with |- @cleanup_cost ?A _ ?cost _ _ =>
    unfold cleanup_cost; do 2 (eexists_cost_expr A);
    subst cost;
    split; [| reflexivity];
    split; [| apply dominated_reflexive];
    split; [| try_prove_nonnegative];
    split
  end.
  monotonic.
  etransitivity.
  { eapply dominated_comp_eq. apply (cost_dominated search_spec').
    2: reflexivity. 2: reflexivity.
    cbn. rewrite limitP. intros ? H. rewrite withinP. revert H.
    filter_closed_under_intersection. eauto. }

  apply dominated_ultimately_le.
  rewrite withinP, invimageP. eexists (fun _ => True).
  split; auto using filter_universe. intros.
  rewrite Z.abs_eq; [| apply height_nonneg].
  rewrite Z.abs_eq; [| apply Z.log2_nonneg].
  apply~ tree_height_bound.
Qed.

Lemma invimage_mono_finer : forall A f g,
  (forall a, f a <= g a) ->
  finer (invimage Z_filterType A f) (invimage Z_filterType A g).
Proof.
  introv Hfg Uf. unfold invimage in *. destruct Uf as [Q [UQ HQ]].
  destruct UQ as [n0 Hn].
  exists (fun x => n0 <= x /\ Q x). split.
  { exists n0. eauto. }
  introv [? ?]. apply HQ. apply Hn. transitivity (f a). 2: apply Hfg. auto.
Qed.

Goal ultimately (invimage_filterType Z_filterType tree (fun _ => 0)) (fun t => 1 <= size t).
  apply invimage_mono_finer with size.
  admit.
  cbn.
  unfold invimage. exists (fun n => 1 <= n). split. apply ultimately_ge_Z.
  auto.
Admitted.

Goal ultimately (invimage_filterType Z_filterType tree (fun _ => 0)) (fun t => 1 <= size t).
  rewrite invimageP.
  exists (fun n:Z => 1 <= n). split. apply ultimately_ge_Z. eauto with zarith.
Qed.

Lemma search_spec_balanced'' :
  specO (within_filterType (@invimage_filterType Z_filterType tree size) balanced) eq
    (fun cost => forall (t: tree),
       balanced t ->
       app search [t]
         PRE (\$ cost t)
         POST (fun (_:Z) => \[]))
    (fun x => Z.log2 (size x)).
Proof.
  xspecO_refine straight_line. intros. xapplys search_spec''.
  try apply cleanup_cost_tagged.
  match goal with |- @cleanup_cost ?A _ ?cost _ _ =>
    unfold cleanup_cost; do 2 (eexists_cost_expr A);
    subst cost;
    split; [| reflexivity];
    split; [| apply dominated_reflexive];
    split; [| try_prove_nonnegative];
    split
  end.
  monotonic.
  etransitivity.
  { eapply dominated_comp_eq. apply (cost_dominated search_spec'').
    3: reflexivity. 2: reflexivity. cbn. rewrite limitP.
    intros ? H. rewrite withinP. revert H. filter_closed_under_intersection. auto. }
  cbn.
  apply dominated_ultimately_le.
  rewrite withinP, invimageP. eexists (fun _ => True).
  split; auto using filter_universe. intros.
  rewrite Z.abs_eq; [| apply height_nonneg].
  rewrite Z.abs_eq; [| apply Z.log2_nonneg].
  apply~ tree_height_bound.
Qed.

(**********)

Parameter array_append : func.

Notation "'len'" := (LibListZ.length).

Definition array_append_sum :=
  specZ [cost \in_O (fun n => n)]
    (forall (A: Type) (a1 a2: list A),
       app array_append [a1 a2]
         PRE (\$ cost (len a1 + len a2))
         POST (fun (_:list A) => \[])).

Definition array_append_2 :=
  specO
    (product_filterType Z_filterType Z_filterType) ZZle
    (fun cost => forall (A: Type) (a1 a2: list A),
      app array_append [a1 a2]
        PRE (\$ cost (len a1, len a2))
        POST (fun (_:list A) => \[]))
    (fun '(m, n) => m + n).

Goal array_append_sum -> array_append_2.
  unfold array_append_sum, array_append_2. intro S.
  xspecO (fun '(m, n) => cost S (m + n)).
  { intros. xapply~ S. }
  { intros [m n] [m' n'] [? ?]. apply (cost_monotonic S). math. }
  { eapply dominated_comp_eq with (f:=cost S) (p:=(fun '(m,n)=>m+n)).
    now eapply cost_dominated. now limit. all: now intros [? ?]; eauto. }
Qed.

(**********)

Parameter fn : func.
Parameter g : Z * Z -> Z.

Definition S2 :=
  specO
    (product_filterType Z_filterType Z_filterType) ZZle
    (fun cost => forall (m n: Z),
      app fn [m n]
        PRE (\$ cost (m, n))
        POST (fun (_:unit) => \[]))
    g.

Definition S :=
  specZ [cost \in_O (fun n => n)]
    (forall (m n: Z),
       app fn [m n]
         PRE (\$ cost (g (m, n)))
         POST (fun (_:unit) => \[])).

Goal
  monotonic ZZle Z.le g ->
  limit (product_filterType Z_filterType Z_filterType) Z_filterType g ->
  S ->
  S2.
  unfold S, S2. intros Mg Lg S.
  xspecO (fun '(m, n) => cost S (g (m, n))).
  { intros. xapply~ S. }
  { intros [m n] [m' n'] [? ?].
    apply (cost_monotonic S). apply Mg. unfold ZZle. math. }
  { eapply dominated_comp_eq with (f:=cost S) (p:=g).
    now eapply cost_dominated. now limit.
    all: intros [? ?]; eauto. }
Qed.
