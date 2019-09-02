Set Implicit Arguments.
Require Import CFML.CFLib CFML.CFLibCredits.
Require Import BinaryRandomAccessList_ml.
Require Import TLC.LibListZ LibZExtra TLC.LibIntTactics.
Require Import Filter Monotonic Dominated CFMLBigO.
Require Import Procrastination.Procrastination.

Require Import Generic DominatedNary LimitNary.
Require Import UltimatelyGreater.

Open Scope Z_scope.
Open Scope liblist_scope.

Notation "'int'" := Z.

Module BinaryRandomAccessListSpec.

Import BinaryRandomAccessList_ml.

(** invariant *)

Section Polymorphic.
Variables (a : Type).

Inductive btree : int -> tree_ a -> list a -> Prop :=
  | btree_nil : forall x,
      btree 0 (Leaf x) (x::nil)
  | btree_cons : forall p p' n t1 t2 L1 L2 L',
      btree p t1 L1 ->
      btree p t2 L2 ->
      p' = p+1 ->
      n = 2^p' ->
      L' = L1 ++ L2 ->
      btree p' (Node n t1 t2) L'.

Inductive inv : int -> rlist_ a -> list a -> Prop :=
  | inv_nil : forall p,
      0 <= p ->
      inv p nil nil
  | inv_cons : forall p (t: tree_ a) ts d L L' T,
      inv (p+1) ts L ->
      L' <> nil ->
      0 <= p ->
      (match d with
       | Zero => L = L'
       | One t => btree p t T /\ L' = T ++ L
       end) ->
      inv p (d :: ts) L'.

Definition Rlist (s: rlist_ a) (L: list a) :=
  inv 0 s L.

End Polymorphic.

Arguments btree [a].
Arguments inv [a].

(** Automation *)

(* Use [maths] hints and properties about btrees in ~-suffixed tactics *)
Create HintDb bral.
Ltac auto_tilde ::= eauto with maths bral.

(* Do not try to unfold Z.mul, e.g. in [2 * n] *)
Opaque Z.mul.

(* Hint Constructors btree inv. *)
(* Hint Extern 1 (@lt nat _ _ _) => rew_list; math. *)
(* Hint Resolve ZNth_zero ZUpdate_here ZUpdate_not_nil. *)
Hint Resolve app_not_empty_l app_not_empty_r.
Hint Extern 1 (0 <= length _) => math : zarith.

(** useful facts *)

Fixpoint tree_size {a: Type} (t:tree_ a) : nat :=
  match t with
  | Leaf _ => 0%nat
  | Node _ t1 t2 => (1 + tree_size t1 + tree_size t2)%nat
  end.

Definition Size {a: Type} (t:tree_ a) :=
  match t with
  | Leaf _ => 1
  | Node w _ _ => w
  end.

Lemma btree_size_correct : forall a p t L,
  @btree a p t L -> Size t = 2^p.
Proof. introv Rt. inverts~ Rt. Qed.

Lemma btree_size_pos : forall a p t L,
  @btree a p t L -> 0 <= p.
Proof. introv Rt. inductions Rt; math. Qed.

Hint Resolve btree_size_pos : bral.

Lemma btree_length_correct : forall a t p L,
  @btree a p t L -> length L = 2^p.
Proof.
  introv Rt. induction Rt. auto.
  subst. rew_list. rewrite~ pow2_succ.
Qed.

Lemma btree_size_length : forall a t p L,
  @btree a p t L -> length L = Size t.
Proof.
  intros. erewrite~ btree_size_correct. erewrite~ btree_length_correct.
Qed.

Lemma btree_not_empty : forall a p t L,
  @btree a p t L -> L <> nil.
Proof.
  introv Rt. intro; subst.
  forwards~: btree_length_correct. rew_list in *.
  forwards~: @pow2_ge_1 p. math.
Qed.

Hint Resolve btree_not_empty : bral.

Lemma inv_size_pos : forall a p ts L,
  @inv a p ts L ->
  0 <= p.
Proof. introv I. destruct~ I. Qed.

Hint Resolve inv_size_pos : bral.

Lemma inv_ts_not_empty : forall a p ts L,
  @inv a p ts L ->
  ts <> nil ->
  L <> nil.
Proof. introv I. destruct~ I. Qed.

Hint Resolve inv_ts_not_empty : bral.

Lemma inv_L_not_empty : forall a p ts L,
  @inv a p ts L ->
  L <> nil ->
  ts <> nil.
Proof. introv I H. destruct~ I. congruence. Qed.

Hint Resolve inv_L_not_empty : bral.

Lemma inv_to_empty : forall a p L,
  @inv a p nil L -> L = nil.
Proof. introv RL. inverts~ RL. Qed.

Lemma inv_from_empty : forall a p ts,
  @inv a p ts nil -> ts = nil.
Proof. introv RL. inverts RL; auto_false. Qed.

Ltac inv :=
  match goal with
  | I : inv _ nil ?L |- _ =>
    let H := fresh in
    pose proof (@inv_to_empty _ _ L I) as H;
    rewrite H in *; clear H; clear L
  | I : inv _ ?ts nil |- _ =>
    let H := fresh in
    pose proof (@inv_from_empty _ _ ts I) as H;
    rewrite H in *; clear H; clear ts
  end;
  rew_list in *.

Lemma group_ineq : forall n m, 0 <= n - m -> m <= n.
Proof. intros. math. Qed.

(* True but useless *)
(*
Lemma inv_length_correct : forall a ts p L,
    @inv a p ts L ->
    If ts = nil then
      length L = 0
    else
      (2 ^ p <= length L <= 2 ^ (length ts + p) - 2 ^ p).
Proof.
  induction ts.
  - intros. case_if. rewrites~ (>> to_empty ___).
  - { rename a0 into d. case_if; intros p L Rdts.
      - { inverts Rdts as. intros L0 T _t Rts Lnnil ?. forwards IH: IHts Rts.
          forwards~: pow2_ge_1 p.
          destruct d; intros; subst.
          - { assert (ts <> nil). { intro TS. apply Lnnil. subst. applys~ to_empty. }
              case_If. destruct IH as [IH1 IH2]. split.
              - rew_ineq <- IH1. rew_pow~ 2 p.
              - rewrite~ length_cons. rew_ineq IH2. rew_pow~ 2 p. }
          - { case_If.
              - { unpack; subst. forwards~: (>> to_empty ___); subst. split.
                  - forwards~: (>> length_correct ___). rew_list~.
                  - rew_length~. forwards~ Tlen: (>> length_correct ___). rew_pow~ 2 p. }
              - { destruct IH as [IH1 IH2]; unpack; subst.
                  split; forwards~ Tlen: (>> length_correct ___); rew_length~.
                  rew_ineq IH2. rewrite Tlen. rew_pow~ 2 p. } } } }
Qed.
*)

Lemma pow_r_eq : forall x y b,
  x = y -> b ^ x = b ^ y.
Proof. intros; subst~. Qed.

Local Ltac epow tac :=
  erewrite pow_r_eq; [ tac | auto_tilde ].

Tactic Notation "epow" ":" tactic(tac) :=
  epow tac.

Lemma inv_ts_len : forall a ts (p:int) L,
    @inv a p ts L ->
    ts <> nil ->
    2 ^ (p + (length ts) - 1) <= length L.
Proof.
  induction ts as [| d ts IHts ].
  { intros. false. }
  { intros p L Rdts _. inverts Rdts as. intros L0 T _t Rts Lnnil ? ?.
    destruct ts.
    - { (* ts = nil // interesting case *)
        destruct d; intros; subst. (* [d] must be a [One t] for the invariant to hold. *)
        - inv. false.
        - inv. unpack; subst. erewrite~ btree_length_correct. epow: reflexivity. }
    - { forwards IH: IHts Rts. congruence.
        destruct d; unpack; subst; rew_list in *.
        + epow: apply IH.
        + epow: rewrite IH. math. } }
Qed.

Lemma ts_bound : forall a ts p L,
    @inv a p ts L ->
    2 ^ (length ts) <= 2 * (length L) + 1.
Proof.
  destruct ts; rew_list; intros.
  { change (2^0) with 1. math. }
  { forwards I: inv_ts_len H. congruence.
    erewrite pow_r_eq in I; [| rew_list; ring_simplify; reflexivity].
    rew_pow~ 2 1. change (2^1) with 2.
    rew_pow~ 2 p in I. rewrite~ <-I.
    forwards~: pow2_ge_1 p. forwards~: Z.pow_nonneg 2 (length ts). math_nia. }
Qed.

Lemma ts_bound_log : forall a ts p L,
    @inv a p ts L ->
    length ts <= Z.log2 (2 * (length L) + 1).
Proof.
  intros. forwards~: ts_bound. forwards~: Z.log2_le_mono. rewrites~ Z.log2_pow2 in *.
Qed.

(* Useless *)
(*
Lemma p_bound_log : forall a ts p L,
    @inv a p ts L -> If ts <> nil then p <= Z.log2 (length L) else True.
Proof.
  introv Rts. forwards~ inv_bounds: inv_length_correct. case_If.
  - case_If. destruct inv_bounds as [I1 _].
    forwards~: Z.log2_le_mono. rewrites~ Z.log2_pow2 in *.
    inverts~ Rts.
  - auto.
Qed.
*)

(** Verification *)

Lemma empty_spec :
  forall a, Rlist (@empty a) (@nil a).
Proof. intros. rewrite (empty__cf a). constructors~. Qed.

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

Lemma is_empty_spec :
  spec1 [cost]
    (forall a (l: rlist_ a),
     app is_empty [l]
       PRE (\$ cost tt)
       POST (fun (b: bool) => \[b = isTrue (l = nil)])).
Proof.
  xspecO_refine straight_line. xcf. xgo~.
  cleanup_cost. monotonic. dominated.
Qed.

Hint Extern 1 (RegisterSpec is_empty) => Provide (provide_specO is_empty_spec).

(* private *)
Lemma size_spec :
  spec1 [cost]
    (forall a (t: tree_ a),
     app size [t]
       PRE (\$ cost tt)
       POST (fun (n: int) => \[n = Size t])).
Proof.
  xspecO_refine straight_line. xcf. xgo~.
  cleanup_cost. monotonic. dominated.
Qed.

Hint Extern 1 (RegisterSpec size) => Provide (provide_specO size_spec).

Lemma link_spec :
  spec1 [cost]
    (forall a (t1 t2: tree_ a) p L1 L2,
     btree p t1 L1 -> btree p t2 L2 ->
     app link [t1 t2]
       PRE (\$ cost tt)
       POST (fun t' => \[btree (p+1) t' (L1 ++ L2)])).
Proof.
  xspecO_refine straight_line. xcf. xgo. constructors~.
  erewrite btree_size_correct in * by eauto. rewrite~ pow2_succ.
  cleanup_cost. monotonic. dominated.
Qed.

Hint Extern 1 (RegisterSpec link) => Provide (provide_specO link_spec).

Lemma cons_tree_spec_aux :
  specZ [cost \in_O (fun n => n)]
    (forall a (t: tree_ a) (ts: rlist_ a) p T L,
     btree p t T -> inv p ts L ->
     app cons_tree [t ts]
       PRE (\$ cost (length ts))
       POST (fun ts' => \[inv p ts' (T ++ L)])).
Proof.
  xspecO_refine recursive. intros ? ? ? ? a t ts. revert t.
  { induction ts; introv Rt Rts; inverts Rts; xcf.
    - weaken.
      xpay. xgo~.
      { constructors~. constructors~. }
      { rew_list. rewrite !Z.max_id. rewrite Z.add_0_r. defer. }
    - weaken. xpay.
      xmatch; unpack; subst.
      { xret. hsimpl. constructors~. }
      { xapps~. intros. xapps~. intros.
        xret. hsimpl. constructors~. rew_list~. }

    rew_cost. rew_list. generalize (length ts) (length_nonneg ts). defer. }

  close_cost. begin defer assuming a b.
  exists (fun n => a * n + b). repeat split.
  { ring_simplify. defer. }
  { introv HH. cancel z; case_max; defer. }

  cleanup_cost.
  { assert (0 <= a) by (deferred; math_lia). monotonic. }
  { dominated. }

  end defer. elia.
Qed.

Lemma cons_tree_spec_aux' :
  specZ [cost \in_O (fun n => n)]
    (forall a (t: tree_ a) (ts: rlist_ a) p T L,
     btree p t T -> inv p ts L ->
     app cons_tree [t ts]
       PRE (\$ cost (length ts))
       POST (fun ts' => \[inv p ts' (T ++ L)])).
Proof.
  begin defer assuming a b.
  xspecO (fun n => a * n + b). intros A t ts. revert t.
  { induction ts; introv Rt Rts; inverts Rts; xcf.
    - weaken.
      xpay. xgo~.
      { constructors~. constructors~. }
      { rew_list. rew_cost. defer. }
    - weaken. xpay.
      xmatch; unpack; subst.
      { xret. hsimpl. constructors~. }
      { xapps~. intros. xapps~. intros.
        xret. hsimpl. constructors~. rew_list~. }
      rew_list. rew_cost. cancel (length ts).
      all: case_max; auto with zarith; defer. }

  { assert (0 <= a) by (deferred; math_lia). monotonic. }
  { dominated. }

  end defer. elia.
Qed.

Lemma cons_tree_spec :
  specZ [ cost \in_O Z.log2 ]
    (forall a (t: tree_ a) (ts: rlist_ a) p T L,
     btree p t T -> inv p ts L ->
     app cons_tree [t ts]
       PRE (\$ cost (length L))
       POST (fun ts' => \[inv p ts' (T ++ L)])).
Proof.
  xspecO_refine straight_line. intros. weaken. xapplys~ cons_tree_spec_aux.
  apply cost_monotonic. rewrite~ ts_bound_log. generalize (length L). reflexivity.
  cleanup_cost. monotonic. dominated.
Qed.

Hint Extern 1 (RegisterSpec cons_tree) => Provide (provide_specO cons_tree_spec).

Lemma cons_spec :
  specZ [cost \in_O Z.log2]
    (forall a (x: a) (l: rlist_ a) L,
     Rlist l L ->
     app cons [x l]
       PRE (\$ cost (length L))
       POST (fun l' => \[Rlist l' (x::L)])).
Proof.
  xspecO_refine straight_line. xcf. xpay.
  weaken. xapp~. constructors~. hsimpl. rew_list~ in *.
  generalize (length L). reflexivity.
  cleanup_cost. (* FIXME: cleanup_cost should replace [cost cons_tree_spec] by its bound *)
  monotonic. dominated.
Qed.

Hint Extern 1 (RegisterSpec cons) => Provide (provide_specO cons_spec).

Lemma uncons_tree_spec_aux :
  specZ [cost \in_O (fun n => n)]
    (forall a (ts: rlist_ a) p L,
     inv p ts L -> ts <> nil ->
     app uncons_tree [ts]
       PRE (\$ cost (length ts))
       POST (fun '(t', ts') =>
         \[exists T' L', btree p t' T' /\ inv p ts' L' /\ L = T' ++ L'])).
Proof.
  begin defer assuming a b. xspecO (fun n => a * n + b).
  induction ts as [| t ts']; introv Rts Ne; inverts Rts as.
  { xcf; xgo. }
  { introv ? I. intros. xcf. weaken. xpay. xmatch.
    { xcleanpat. inv. unpack; subst.
      xrets. exists. splits~. constructors~. rew_list~. }
    { forwards: inv_ts_not_empty I. congruence. xcleanpat.
      unpack; subst. xrets. exists. splits~. constructors~. }
    { xcleanpat. xapp~ as [t l]. intros; unpack; subst. xgo.
      - match goal with
        | B: btree _ (Node _ ?t1_ ?t2_) _, I: inv _ _ ?L_ |- _ =>
          rename t1_ into t1; rename t2_ into t2; rename L_ into L;
          inverts B
        end; subst.
        match goal with
        | H1: btree _ t1 ?L1_, H2: btree _ t2 ?L2_, E: (?p + 1) = (?p' + 1) |- _ =>
          rename L1 into L1; rename L2 into L2;
          maths (p = p'); clear E
        end; subst.
        eexists L1, (L2 ++ L). splits~. constructors~. rew_list~.
      - match goal with B: btree _ _ _ |- _ => inverts B end; subst.
        { math. } { jauto. } }

    rew_cost. rew_list. cancel (length ts'). all: case_max; defer. }

  { assert (0 <= a) by (deferred; math_lia). monotonic. }
  { dominated. }

  end defer. elia.
  Grab Existential Variables.  apply heap_is_gc. (* XXX *)
Qed.

Lemma uncons_tree_spec :
  specZ [cost \in_O Z.log2]
    (forall a (ts: rlist_ a) p L,
     inv p ts L -> ts <> nil ->
     app uncons_tree [ts]
       PRE (\$ cost (length L))
       POST (fun '(t', ts') =>
         \[exists T' L', btree p t' T' /\ inv p ts' L' /\ L = T' ++ L'])).
Proof.
  xspecO_refine straight_line. intros. weaken. xapplys~ uncons_tree_spec_aux.
  apply cost_monotonic. rewrite~ ts_bound_log. generalize (length L); reflexivity.
  cleanup_cost. monotonic. dominated.
Qed.

Hint Extern 1 (RegisterSpec uncons_tree) => Provide (provide_specO uncons_tree_spec).

Lemma head_spec :
  specZ [cost \in_O Z.log2]
    (forall a (l: rlist_ a) L,
     Rlist l L -> l <> nil ->
     app head [l]
       PRE (\$ cost (length L))
       POST (fun (x:a) => \[exists L', L = x :: L'])).
Proof.
  xspecO_refine straight_line. xcf. weaken. xpay. xapp~ as [t ts].
  intros (? & ? & B & I & ?); subst. xmatch.
  { xrets. inverts B. rew_list~. }
  { xfail. inverts* B; subst. forwards~: btree_size_pos. math. }
  rew_cost. generalize (length L); reflexivity.
  cleanup_cost. monotonic. dominated.
Qed.

Hint Extern 1 (RegisterSpec head) => Provide (provide_specO head_spec).

Lemma tail_spec :
  specZ [cost \in_O Z.log2]
    (forall a (l: rlist_ a) L,
     Rlist l L -> l <> nil ->
     app tail [l]
       PRE (\$ cost (length L))
       POST (fun tl => \[exists TL x, Rlist tl TL /\ L = x :: TL])).
Proof.
  xspecO_refine straight_line. xcf. weaken. xpay. xapp~ as [t ts].
  intros (? & ? & B & I & ?); subst. xmatch. xrets. inverts B; subst.
  { rew_list~ in *. }
  { forwards~: btree_size_pos. math. }
  rew_cost. generalize (length L); reflexivity.
  cleanup_cost. monotonic. dominated.
Qed.

Hint Extern 1 (RegisterSpec tail) => Provide (provide_specO tail_spec).

Lemma lookup_tree_spec :
  specZ [cost \in_O (fun n => n)]
    (forall a `{Inhab a} i (t: tree_ a) p L,
     btree p t L ->
     0 <= i < length L ->
     app lookup_tree [i t]
       PRE (\$ cost p)
       POST (fun x => \[ x = L[i] ])).
Proof.
  begin defer assuming a b. xspecO (fun n => a * n + b).
  intros a_ Ia i t. revert i.
  induction t; introv BT Bi; inverts BT; xcf.
  { weaken. xgo. subst. rewrite~ read_zero. rew_list~ in *.
    rew_cost. defer. }
  { weaken. xpay. xmatch. subst.
    match goal with B1: btree ?p _ _, B2: btree ?p _ _ |- _ =>
      forwards~: btree_length_correct B1; forwards~: btree_length_correct B2
    end. rew_list in Bi.
    xif; rewrites~ pow_succ_quot in *.
    { xapplys~ IHt1. rewrite read_app. case_if~. }
    { xapplys~ IHt2. rewrite read_app. case_if~.
      now match goal with H: length L1 = _ |- _ => rewrite H end. }

    rew_cost. subst. cancel p0. case_max; auto; defer. apply~ btree_size_pos.
    case_max; defer. }
  { assert (0 <= a) by (deferred; math_lia). monotonic. } { dominated. }
  end defer. elia.
Qed.

Hint Extern 1 (RegisterSpec lookup_tree) => Provide (provide_specO lookup_tree_spec).

Lemma update_tree_spec :
  specZ [cost \in_O (fun n => n)]
    (forall a `{Inhab a} i (x: a) (t: tree_ a) p L,
     btree p t L ->
     0 <= i < length L ->
     app update_tree [i x t]
       PRE (\$ cost p)
       POST (fun t' => \[btree p t' L[i := x]])).
Proof.
  begin defer assuming a b. xspecO (fun n => a * n + b).
  intros a_ Ia i x t. revert i x. induction t; introv BT Bi; inverts BT; xcf.
  { weaken. xgo~. subst. rewrite update_zero. constructors. now rew_list~ in *.
    rew_cost. defer. }
  { weaken. xpay. xmatch. subst. xcleanpat.
    match goal with B1: btree ?p _ _, B2: btree ?p _ _ |- _ =>
      forwards~: btree_length_correct B1; forwards~: btree_length_correct B2
    end. rew_list in Bi.
    xif; rewrites~ pow_succ_quot in *.
    { xapp_spec~ IHt1. intros. xret. hsimpl.
      rewrite~ update_app_l. constructors~. }
    { xapp_spec~ IHt2. intros. xret. hsimpl.
      erewrite~ update_app_r. constructors~. all: math. }

    rew_cost. subst. cancel p0. case_max; auto; defer. apply~ btree_size_pos.
    case_max; defer. }
  { assert (0 <= a) by (deferred; math). monotonic. } { dominated. }
  end defer. elia.
Qed.

Hint Extern 1 (RegisterSpec update_tree) => Provide (provide_specO update_tree_spec).

Definition product_positive_order :=
  product_filterType positive_filterType Z_filterType.

Lemma limit_positive_order_x_plus_y :
  limit product_positive_order Z_filterType (fun '(x,y) => x + y).
Proof.
  apply_nary (@limit_sum_ultimately_ge_l_nary 0).
  - apply ultimately_lift1. rewrite~ positiveP.
  - limit.
Qed.

Hint Resolve limit_positive_order_x_plus_y : limit.

Lemma limit_positive_0 :
  limit Z_filterType positive_filterType (fun _ => 0).
Proof.
  rewrite limitP. intros. rewrite positiveP, ZP in *.
  exists~ 0.
Qed.

Hint Resolve limit_positive_0 : limit.

(* XX *)
Ltac fold_product :=
  rewrite_strat (subterms (fold (product_filterType positive_filterType Z_filterType))).

Lemma dominated_positive_order_x_x_plus_y :
  dominated product_positive_order
    (fun '(x, y) => x) (fun '(x,y) => x + y).
Proof.
  apply_nary dominated_sum_r_nonneg_1_nary; fold_product.
  { (* ultimately_greater FIXME *)
    apply ultimately_lift1. rewrite~ positiveP. }
  { apply ultimately_lift2. ultimately_greater. }
  dominated.
Qed.

Hint Resolve dominated_positive_order_x_x_plus_y.

Lemma dominated_positive_order_y_x_plus_y :
  dominated product_positive_order
    (fun '(x, y) => y) (fun '(x,y) => x + y).
Proof.
  apply_nary dominated_sum_r_nonneg_2_nary; fold_product.
  { apply ultimately_lift1. rewrite~ positiveP. }
  { apply ultimately_lift2. ultimately_greater. }
  reflexivity.
Qed.

Hint Resolve dominated_positive_order_y_x_plus_y.

(* HACK HACK HACK

   - Partly because of https://github.com/coq/coq/issues/6805 which introduces
   buggy definitions in the context of side-goals spawned by setoid_rewrite;

   - Partly because we call [math] on one of these side-goals (through
   [auto_tilde] then [eauto with maths]), and CFML.CFTactics redefined [math_0]
   (called by math) to call [xclean] -- which in turns messes up with the buggy
   definition...
*)
Ltac math_0 ::=
  repeat (match goal with x := Morphisms.do_subrelation : _ |- _ => clear x end);
  xclean.

(* - est-ce qu'on sait prouver cette spec directement ? il semblerait que non *)
(* - est-ce que cette spec découle de la spec avec filtre produit ? oui! *)
(* - si on a cette spec, est-ce qu'on sait bien prouver la spec finale ?
     oui. (sans trop de surprise) *)
Definition lookup_spec_ind__external_forall :=
  forall p,
  0 <= p ->
  specO Z_filterType Z.le
    (fun cost =>
     forall a i (ts: rlist_ a) L,
     inv p ts L ->
     0 <= i < length L ->
     app lookup [i ts]
       PRE (\$ cost (length ts))
       POST (fun x => \[Nth (abs i) L x]))
    (fun n => n).

Definition lookup_spec_ind__nonstandard_product :=
  specO product_positive_order ZZle
    (fun cost =>
     forall a i (ts: rlist_ a) p L,
     inv p ts L ->
     0 <= i < length L ->
     app lookup [i ts]
       PRE (\$ cost (p, length ts))
       POST (fun x => \[Nth (abs i) L x]))
    (fun '(m,n) => m + n).

Definition lookup_spec__final :=
  specZ [cost \in_O Z.log2]
    (forall a i (ts: rlist_ a) L,
     Rlist ts L ->
     0 <= i < length L ->
     app lookup [i ts]
       PRE (\$ cost (length L))
       POST (fun x => \[Nth (abs i) L x])).

Goal lookup_spec_ind__nonstandard_product -> lookup_spec_ind__external_forall.
Proof.
  intro S.
  unfold lookup_spec_ind__external_forall, lookup_spec_ind__nonstandard_product in *.
  intros p NP.
  destruct S.
  eapply (@SpecO _ _ _ _ (fun len_ts => cost (p, len_ts))); auto.
  { monotonic. }
  { etransitivity.
    eapply dominated_comp_eq. apply cost_dominated.
    2: intros; reflexivity.
    { rewrite limitP. intros P UP. unfold product_positive_order in UP.
      rewrite productP in UP. destruct UP as (P1 & P2 & UP1 & UP2 & HH).
      rewrite positiveP, ZP in *. destruct UP2 as (n0 & HP2).
      exists (Z.max 0 n0). intros. apply HH. apply UP1. auto. apply HP2.
      eapply Z.max_lub_r. eauto. }
    { simpl. reflexivity. }
    dominated.
  }
Qed.

Goal lookup_spec_ind__external_forall -> lookup_spec__final.
Proof.
  intro S.
  unfold lookup_spec_ind__external_forall, lookup_spec__final in *.
  specializes S 0 __. xspecO (fun len_L => cost S (Z.log2 (2 * len_L + 1))).
  intros. weaken. xapplys~ S. apply cost_monotonic. rewrite~ ts_bound_log. math.
  monotonic.
  { etransitivity. apply dominated_comp. apply cost_dominated.
    unfold product_positive_order. limit. dominated. }
Qed.

Lemma lookup_spec_ind :
  specO product_positive_order ZZle
    (fun cost =>
     forall a `{Inhab a} i (ts: rlist_ a) p L,
     inv p ts L ->
     0 <= i < length L ->
     app lookup [i ts]
       PRE (\$ cost (p, length ts))
       POST (fun x => \[x = L[i]]))
    (fun '(m,n) => m + n).
Proof.
  xspecO_refine recursive. intros costf ? ? ?.
  intros a_ Ia i ts. revert i. induction ts; introv I Bi.
  { inv. math. }
  { inverts I. xcf. weaken. xpay. xmatch. { xapps~. }
    xcleanpat. unpack; subst. xapps~. xif.
    { xapps~. erewrite~ btree_size_length. math. hsimpl.
      rewrite read_app. case_if~.
      false. forwards~: btree_size_length b. }
    { xapps~. forwards~: btree_size_length. rew_list~ in *.
      xapps~. hsimpl. rewrite read_app. case_if~.
      now match goal with H: length T = _ |- _ => rewrite H end. }

    rew_list. rew_cost.
    asserts~ [HH1 HH2]: (0 <= p /\ 0 <= length ts).
    generalize p (length ts) HH1 HH2; defer. }

  close_cost.

  (* ici on est un peu triste car les équations de récurrence (et la solution
     qu'il faut deviner) sont polluées par les fonctions de coût opaques pour
     les fonctions auxiliaires.

     Mais on ne voit pas bien comment faire mieux.
   *)

  begin defer assuming a b c d.
  exists (fun '(m,n) => a * m + b * n + c * cost lookup_tree_spec (m+n) + d).
  repeat split.
  { intros m n Hm Hn. math_rewrite (m+(1+n) = m+1+n).
    rewrite~ (cost_monotonic lookup_tree_spec m (m+1+n)).
    cancel (cost lookup_tree_spec (m+1+n)). case_max; auto with zarith; defer.
    cancel m; cancel n. all: repeat case_max; auto with zarith. all: defer. }
  cleanup_cost.
  { intros [m n] [m' n'] [Hm Hn].
    assert (0 <= a /\ 0 <= b /\ 1 <= c) as (?&?&?) by (deferred; math_lia).
    forwards~ M: cost_monotonic lookup_tree_spec (m + n) (m' + n').
    rewrite~ M. auto with zarith. }

  repeat apply_nary dominated_sum_distr_nary;
    try apply_nary dominated_mul_cst_l_1_nary; dominated.
  eapply dominated_comp_eq with
    (J := Z_filterType) (p := fun '(t,x) => t + x).
  apply (cost_dominated lookup_tree_spec). limit.
  intros [? ?]. reflexivity. intros [? ?]. reflexivity.

  end defer. elia.
Qed.

Lemma lookup_spec :
  specZ [cost \in_O Z.log2]
    (forall a `{Inhab a} i (ts: rlist_ a) L,
     Rlist ts L ->
     0 <= i < length L ->
     app lookup [i ts]
       PRE (\$ cost (length L))
       POST (fun x => \[x = L[i]])).
Proof.
  xspecO (fun x => cost lookup_spec_ind (0, Z.log2 ((2 * x) + 1))).
  { intros. weaken. xapplys~ lookup_spec_ind.
    apply cost_monotonic. splits~. unfold Rlist in *. rewrite~ ts_bound_log.
    math. }

  { monotonic. }
  { etransitivity. apply dominated_comp. apply cost_dominated.
    unfold product_positive_order. limit. dominated. }
Qed.

Lemma update_spec_ind :
  specO product_positive_order ZZle (fun cost =>
    forall a `{Inhab a} i (x: a) (ts: rlist_ a) p L,
    inv p ts L ->
    0 <= i < length L ->
    app update [i x ts]
      PRE (\$ cost (p, length ts))
      POST (fun ts' => \[inv p ts' L[i := x]]))
  (fun '(m, n) => m + n).
Proof.
  xspecO_refine recursive. intros costf ? ? ?.
  intros a_ Ia i x ts. revert i x. induction ts; introv I Bi.
  { inv. math. }
  { inverts I; xcf. weaken. xpay.
    xmatch.
    { subst. xapps~. intros; unpack. xret~. hsimpl~. constructors~.
      intros Hnil. rewrite <-length_zero_eq_eq_nil in Hnil.
      now rewrite length_update in Hnil. }
    xapps~. unpack; subst.
    forwards~: btree_length_correct. forwards~: btree_size_correct.
    xif.
    { xapps~. intros. xret. hsimpl. rewrite~ update_app_l. constructors~. }
    { xapps~. xapps~. now rew_list~ in *. intros. xret. hsimpl.
      erewrite update_app_r with (i := 2^p). constructors~. all: math. }

    rew_list. rew_cost. asserts~ [HH1 HH2]: (0 <= p /\ 0 <= length ts).
    generalize p (length ts) HH1 HH2; defer. }

  close_cost.
  begin defer assuming a b c d.
  exists (fun '(m, n) => a*m + b*n + c*cost update_tree_spec (m+n) + d).
  split.
  { intros m n Hm Hn. math_rewrite (m+(1+n) = m+1+n).
    rewrite~ (cost_monotonic update_tree_spec m (m+1+n)).
    cancel (cost update_tree_spec (m+1+n)). case_max; auto with zarith; defer.
    cancel m; cancel n. all: repeat case_max. all: defer. }
  cleanup_cost.
  { intros [m n] [m' n'] [Hm Hn].
    assert (0 <= a /\ 0 <= b /\ 0 <= c) by (deferred; math_lia); unpack.
    forwards~ M: cost_monotonic update_tree_spec (m+n) (m'+n').
    auto with zarith. }

  repeat apply_nary dominated_sum_distr_nary;
    try apply_nary dominated_mul_cst_l_1_nary; dominated.
  eapply dominated_comp_eq with
    (J := Z_filterType) (p := fun '(t,x) => t + x).
  apply (cost_dominated update_tree_spec). limit.
  intros [? ?]. reflexivity. intros [? ?]. reflexivity.

  end defer. elia.
Qed.

Lemma update_spec :
  specZ [cost \in_O Z.log2]
    (forall a `{Inhab a} i (x: a) (ts: rlist_ a) L,
     Rlist ts L ->
     0 <= i < length L ->
     app update [i x ts]
       PRE (\$ cost (length L))
       POST (fun l' => \[Rlist l' L[i := x]])).
Proof.
  xspecO (fun x => cost update_spec_ind (0, Z.log2 ((2 * x) + 1))).
  { intros. weaken. xapplys~ update_spec_ind.
    apply cost_monotonic. splits~. rewrite~ ts_bound_log. math. }
  { monotonic. }
  { etransitivity. apply dominated_comp. apply cost_dominated.
    unfold product_positive_order. limit. dominated. }
Qed.

End BinaryRandomAccessListSpec.
