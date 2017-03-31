Set Implicit Arguments.
Require Import TLC.LibTactics.
(* Load the CFML library, with time credits. *)
Require Import CFML.CFLibCredits.
(* Load the BigO library. *)
Require Import Dominated.
Require Import BigEnough.
Require Import LibEvars.
Require Import EvarsFacts.
Require Import UltimatelyGreater.

(********************************************************************)

Definition ceil (x : Z) : Z :=
  match x with
  | Z0 => Z0
  | Zpos p => Zpos p
  | Zneg _ => Z0
  end.
  (* Z.max 0 x. *)

Lemma ceil_max_0 : forall x, ceil x = Z.max 0 x.
Proof.
  intro x. destruct x.
  - reflexivity.
  - simpl. auto with zarith.
  - simpl. auto with zarith.
Qed.

Lemma ceil_pos : forall x, 0 <= ceil x.
Proof. intros. rewrite ceil_max_0. math_lia. Qed.

Hint Resolve ceil_pos : zarith.

Lemma ceil_eq : forall x, 0 <= x -> ceil x = x.
Proof. intros. rewrite ceil_max_0. math_lia. Qed.

Lemma ceil_add_eq : forall x y,
    0 <= x ->
    0 <= y ->
    ceil (x + y) = ceil x + ceil y.
Proof. intros. rewrite !ceil_max_0. math_lia. Qed.

Lemma ceil_add_le : forall x y,
  ceil (x + y) <= ceil x + ceil y.
Proof. intros. rewrite !ceil_max_0. math_lia. Qed.

Lemma ceil_max : forall x y,
  ceil (Z.max x y) = Z.max (ceil x) (ceil y).
Proof. intros. rewrite !ceil_max_0. math_lia. Qed.

Lemma ceil_ceil : forall x, ceil (ceil x) = ceil x.
Proof. intros. rewrite !ceil_max_0. math_lia. Qed.

Lemma ceil_ceil_add : forall x y, ceil (ceil x + ceil y) = ceil x + ceil y.
Proof.
  intros x y.
  rewrite ceil_add_eq; try apply ceil_pos.
  rewrite !ceil_ceil. reflexivity.
Qed.

Lemma ceil_ge_nonpos :
  forall x y, x <= 0 -> x <= ceil y.
Proof.
  intros x y.
  rewrite !ceil_max_0. math_lia.
Qed.

Hint Resolve ceil_ge_nonpos : zarith.

Lemma ceil_ge :
  forall x y, x <= y -> x <= ceil y.
Proof.
  intros. rewrite !ceil_max_0. math_lia.
Qed.

Hint Resolve ceil_ge : zarith.

Lemma dominated_ceil : forall A f g,
    dominated A f g ->
    dominated A (fun x => ceil (f x)) g.
Proof.
  introv (c & U). exists c.
  revert U; filter_closed_under_intersection.
  intros.
  assert (I: Z.abs (ceil (f a)) <= Z.abs (f a)). {
    rewrite ceil_max_0. math_lia.
  }
  rewrite I. assumption.
Qed.

(********************************************************************)

Record specO
       (A : filterType)
       (spec : (A -> Z) -> Prop)
       (bound : A -> Z) :=
  SpecO {
      cost : A -> Z;
      spec : spec cost;
      cost_nonneg : forall x, 0 <= cost x;
      cost_dominated : dominated A cost bound
    }.

Definition cleanup_cost (A : filterType) (cost cost_clean : A -> Z) :=
  dominated A cost cost_clean.

Lemma specO_prove :
  forall (A : filterType) (cost cost_clean bound : A -> Z)
         (spec : (A -> Z) -> Prop),
    spec cost ->
    cleanup_cost A cost cost_clean ->
    (forall x, 0 <= cost x) ->
    dominated A cost_clean bound ->
    specO A spec bound.
Proof.
  intros ? cost cost_clean bound.
  introv S D1 N D2.
  econstructor; eauto.
  rewrite D1. assumption.
Qed.

Ltac xspecO_base cost :=
  match goal with
    |- specO ?A _ _ =>
    let cost_clean := fresh "cost_clean" in
    refine (let cost := (fun (x : A) => ceil _ ) : A -> Z in _);
    evar (cost_clean : A -> Z);
    eapply (@specO_prove A cost cost_clean);
    subst cost_clean;
    [ unfold cost | | intro; apply ceil_pos | subst cost ]
  end.

Tactic Notation "xspecO" constr(cost) :=
  xspecO_base cost.

Tactic Notation "xspecO" :=
  let cost := fresh "cost" in
  xspecO_base cost.

Ltac dominated_cleanup_cost :=
  first [
      apply dominated_ceil; dominated_cleanup_cost
    | apply dominated_sum;
      [ | | dominated_cleanup_cost | dominated_cleanup_cost];
      simpl;
      ultimately_greater
    | apply dominated_max;
      [ | | dominated_cleanup_cost | dominated_cleanup_cost];
      simpl;
      ultimately_greater
    | apply dominated_big_sum;
      [ | | dominated_cleanup_cost ];
      simpl;
      ultimately_greater
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
  intro; simpl; hide_evars_then ltac:(fun _ => ring_simplify).

Ltac cleanup_cost :=
  unfold cleanup_cost;
  eapply dominated_eq_r;
  [ dominated_cleanup_cost |];
  simple_cleanup_cost;
  reflexivity.


(* Custom CF rules and tactics ************************************************)

Lemma refine_cost_setup_intro_emp :
  forall A (F: ~~A) cost Q,
  F (\$ cost \* \[]) Q ->
  F (\$ cost) Q.
Proof.
  introv H. rewrite star_neutral_r in H. auto.
Qed.

Ltac is_refine_cost_goal :=
  match goal with
    |- _ (\$ ceil _) _ => apply refine_cost_setup_intro_emp
  | |- _ (\$ ceil _ \* _) _ => idtac
  end.

(* hpull & hclean *********************)

Ltac is_credits H :=
  match H with
  | \$ _ => idtac
  | \$_nat _ => idtac
  | _ => fail 1
  end.

Ltac bring_credits_to_head H :=
  match H with
  | context [?A \* \$ ?x \* _] =>
    tryif is_credits A then fail
    else rewrite (star_comm_assoc A (\$ x))
  | context [?A \* \$ ?x] =>
    tryif is_credits A then fail
    else rewrite (star_comm A (\$ x))
  | context [?A \* \$_nat ?x \* _] =>
    tryif is_credits A then fail
    else rewrite (star_comm_assoc A (\$_nat x))
  | context [?A \* \$_nat ?x] =>
    tryif is_credits A then fail
    else rewrite (star_comm A (\$_nat x))
  end.

Ltac bring_credits_to_head_of_pre tt :=
  repeat on_formula_pre bring_credits_to_head.

Goal forall H1 H2 H3 H' p n m,
    \$ p \* \$ n \* \$_nat m \* H1 \* H2 \* H3 ==> H' ->
    \$ p \* H1 \* H2 \* \$ n \* H3 \* \$_nat m ==> H'.
Proof.
  intros. dup.
  (* detailed *)
  on_formula_pre bring_credits_to_head.
  on_formula_pre bring_credits_to_head.
  on_formula_pre bring_credits_to_head.
  on_formula_pre bring_credits_to_head.
  on_formula_pre bring_credits_to_head.
  assumption.
  (* short *)
  bring_credits_to_head_of_pre tt.
  assumption. (* demo *)
Qed.

Ltac hpull_main tt ::=
  hpull_setup tt;
  (repeat (hpull_step tt));
  bring_credits_to_head_of_pre tt;
  hpull_cleanup tt.

Ltac hclean_main tt ::=
  hclean_setup tt;
  (repeat (hclean_step tt));
  bring_credits_to_head_of_pre tt;
  hclean_cleanup tt.

(* hsimpl *****************************)

Lemma inst_credits_cost :
  forall (credits : int) H H' H'',
  (0 <= credits) ->
  H ==> H' \* H'' ->
  \$ ceil credits \* H ==> H' \* \$ credits \* H''.
Proof.
  introv P HH.
  rewrite ceil_eq; auto.
  xchange HH. hsimpl_credits.
Qed.

Lemma cancel_credits_cost :
  forall (cost credits : int) H H' H'',
  (credits <= cost) ->
  (0 <= credits) ->
  \$ (cost - credits) \* H ==> H' \* H'' ->
  \$ ceil cost \* H ==> H' \* \$ credits \* H''.
Proof.
  intros cost_ credits. intros ? ? ? I N H.
  rewrite ceil_eq; [| math].
  applys~ hsimpl_cancel_credits_int_1.
Qed.

Ltac inst_credits_cost_core credits cont :=
  first [ eapply inst_credits_cost; [ auto with zarith | cont tt ]
        | eapply cancel_credits_cost; [ | auto with zarith | cont tt ]
        ].

Ltac inst_credits_cost cont :=
  match goal with
    |- _ ==> _ \* \$ ?credits \* _ =>
    inst_credits_cost_core credits cont
  end.

(* \$_nat ? *)
Ltac hsimpl_inst_credits_cost_setup tt :=
  match goal with
  | |- \$ ceil ?cost ==> _ => is_evar cost; apply hsimpl_start_1
  | |- \$ ceil ?cost \* _ ==> _ => is_evar cost
  | |- \$ ceil (?cost _) ==> _ => is_evar cost; apply hsimpl_start_1
  | |- \$ ceil (?cost _) \* _ ==> _ => is_evar cost
  end;
  match goal with
  | |- _ ==> _ \* \$ _ => apply hsimpl_starify
  | |- _ ==> _ \* \$ _ \* _ => idtac
  end.

Ltac hsimpl_inst_credits_cost cont :=
  tryif hsimpl_inst_credits_cost_setup tt then
    inst_credits_cost cont
  else
    cont tt.

Ltac hsimpl_setup process_credits ::=
  prepare_goal_hpull_himpl tt;
  try (check_arg_true process_credits; credits_join_left_repeat tt);
  hsimpl_left_empty tt;
  hsimpl_inst_credits_cost ltac:(fun _ => apply hsimpl_start).

(* xcf ******************************************)

(* This is to ensure that credits are put at the head of the precondition. *)

Ltac xcf_post tt ::=
  cbv beta;
  remove_head_unit tt;
  hclean.

(* xpay *****************************************)

Lemma xpay_refine :
  forall A (cost cost' : Z)
         (F: hprop -> (A -> hprop) -> Prop) H Q,
  (cost = 1 + ceil cost') ->
  is_local F ->
  F (\$ ceil cost' \* H) Q ->
  (Pay_ ;; F) (\$ ceil cost \* H) Q.
Proof.
  introv E L HH. rewrite E.
  xpay_start tt.
  { unfold pay_one.
    rewrite ceil_eq; [| forwards: ceil_pos cost'; math_lia ].
    credits_split.
    hsimpl_credits. math. forwards~: ceil_pos cost'. }
  xapply HH. hsimpl_credits. hsimpl.
Qed.

Ltac xpay_core tt ::=
  tryif is_refine_cost_goal then
    (eapply xpay_refine; [ reflexivity | xlocal | ])
  else
    (xpay_start tt; [ unfold pay_one; hsimpl | ]).

(* xret *******************************)

Lemma xret_refine : forall cost A (x : A) H (Q : A -> hprop),
  (cost = 0) ->
  local (fun H' Q' => H' ==> Q' x) H Q ->
  local (fun H' Q' => H' ==> Q' x) (\$ ceil cost \* H) Q.
Proof.
  introv E HH.
  rewrite E. rewrite ceil_eq; [| math]. rewrite credits_int_zero_eq. rewrite star_neutral_l.
  assumption.
Qed.

Ltac xret_inst_credits_zero :=
  apply xret_refine; [ reflexivity | ].

Ltac xret_apply_lemma tt ::=
  (tryif is_refine_cost_goal then xret_inst_credits_zero else idtac);
  first [ apply xret_lemma_unify
        | apply xret_lemma ].

Ltac xret_no_gc_core tt ::=
  (tryif is_refine_cost_goal then xret_inst_credits_zero else idtac);
  first [ apply xret_lemma_unify
        | eapply xret_no_gc_lemma ].

(* xseq *******************************)

Lemma xseq_refine :
  forall (A : Type) cost cost1 cost2 F1 F2 H (Q : A -> hprop),
  (cost = ceil cost1 + ceil cost2) ->
  is_local F1 ->
  is_local F2 ->
  (exists Q',
    F1 (\$ ceil cost1 \* H) Q' /\
    F2 (\$ ceil cost2 \* Q' tt) Q) ->
  (F1 ;; F2) (\$ ceil cost \* H) Q.
Proof.
  introv E L1 L2 (Q' & H1 & H2).
  rewrite E.
  xseq_pre tt. apply local_erase. eexists. split.
  { xapply H1. rewrite ceil_add_eq; try apply ceil_pos. repeat rewrite ceil_ceil.
    forwards: ceil_pos cost1. forwards: ceil_pos cost2.
    credits_split. hsimpl. math. math. }
  { xapply H2. hsimpl. hsimpl. }
Qed.

Ltac xseq_core cont0 cont1 ::=
  (tryif is_refine_cost_goal then
     eapply xseq_refine; [ reflexivity | xlocal | xlocal | ]
   else
     apply local_erase);
  cont0 tt;
  split; [ | cont1 tt ];
  xtag_pre_post.

(* xlet *****************************************)

Lemma xlet_refine :
  forall
    (A B : Type) cost cost1 cost2
    (F1 : hprop -> (A -> hprop) -> Prop)
    (F2 : A -> hprop -> (B -> hprop) -> Prop)
    (H : hprop) (Q : B -> hprop),
  (cost = ceil cost1 + ceil cost2) ->
  is_local F1 ->
  (forall x, is_local (F2 x)) ->
  (exists (Q' : A -> hprop),
    F1 (\$ ceil cost1 \* H) Q' /\
    (forall r, F2 r (\$ ceil cost2 \* Q' r) Q)) ->
  cf_let F1 F2 (\$ ceil cost \* H) Q.
Proof.
  introv E L1 L2 (Q' & H1 & H2).
  rewrite E.
  unfold cf_let.
  eexists. split.
  { xapply H1. rewrite ceil_add_eq; try apply ceil_pos. repeat rewrite ceil_ceil.
    forwards: ceil_pos cost1. forwards: ceil_pos cost2.
    credits_split. hsimpl. math. math. }
  { intro r. specializes L2 r. xapply H2; hsimpl. }
Qed.

Ltac xlet_core cont0 cont1 cont2 ::=
  apply local_erase;
  match goal with |- cf_let ?F1 (fun x => _) ?H ?Q =>
    tryif is_refine_cost_goal then (
      eapply xlet_refine;
      [ reflexivity | xlocal | intro; xlocal | ]
    ) else idtac;
    cont0 tt;
    split; [ | cont1 x; cont2 tt ];
    xtag_pre_post
  end.

(* xif ********************************)

Lemma xif_refine : forall (A: Type) cost cost1 cost2 cond (F1 F2: ~~A) H Q,
  (cost = Z.max (ceil cost1) (ceil cost2)) ->
  is_local F1 ->
  is_local F2 ->
  ((cond = true -> F1 (\$ ceil cost1 \* H) Q) /\
   (cond = false -> F2 (\$ ceil cost2 \* H) Q)) ->
  (If_ cond Then F1 Else F2) (\$ ceil cost \* H) Q.
Proof.
  introv costE L1 L2 (H1 & H2).
  apply local_erase. rewrite costE.
  forwards: ceil_pos cost1. forwards: ceil_pos cost2.
  split; intro; [xapply~ H1 | xapply~ H2];
  hsimpl_credits; try math; rewrite ceil_max; rewrite !ceil_ceil;
  math_lia.
Qed.

Ltac xif_base cont1 cont2 ::=
  xpull_check_not_needed tt;
  xif_check_post_instantiated tt;
  let cont tt :=
    tryif is_refine_cost_goal then (
      eapply xif_refine;
      [ reflexivity | xlocal | xlocal | ]
    ) else (
      xuntag tag_if;
      apply local_erase
    );
    split; [ cont1 tt | cont2 tt ];
    xtag_pre_post
  in
  match cfml_get_tag tt with
  | tag_if => cont tt
  | tag_let => xlet; [ cont tt | instantiate ]
  end.

(* xfor *****************************************)

(* TODO: prove using xfor_inv_case_lemma_refine instead of directly *)
Lemma xfor_inv_lemma_pred_refine :
  forall
    (I : int -> hprop) (cost : int)
    (cost_body : int -> int)
    (a : int) (b : int) (F : int-> ~~unit) H H',
  (a <= b) ->
  (forall i, a <= i < b -> F i (\$ ceil (cost_body i) \* I i) (# I(i+1))) ->
  (H ==> I a \* H') ->
  (forall i, is_local (F i)) ->
  (cumul (fun i => ceil (cost_body i)) a b <= cost) ->
  (For i = a To (b - 1) Do F i Done_) (\$ ceil cost \* H) (# I b \* H').
Proof.
  introv a_le_b HI HH Flocal Icost.
  assert (cost_nonneg : 0 <= cost0). {
    rewrite cumulP in Icost. rewrite big_nonneg_Z. apply Icost.
    intros. simpl. apply ceil_pos.
  }
  applys xfor_inv_case_lemma
    (fun (i: int) => \$ cumul (fun i => ceil (cost_body i)) i b \* I i);
  intros C.
  { eexists. splits~.
    - hchange HH. hsimpl.
      rewrite~ ceil_eq. hsimpl_credits. math. admit. (* ok *)
    - intros i Hi.
      (* xframe (\$cumul f (i + 1) n). auto. *) (* ?? *)
      xframe_but (\$ceil (cost_body i) \* I i). auto.
      assert (forall f, cumul f i b = f i + cumul f (i + 1) b) as cumul_lemma by admit.
      rewrite cumul_lemma; clear cumul_lemma.
      credits_split. hsimpl. admit. (* ok *)
      admit. (* ok *)
      applys HI. math.
      xsimpl_credits.
    - math_rewrite ((b - 1) + 1 = b). hsimpl. }
  { xchange HH. math_rewrite (a = b). xsimpl. }
Qed.

Lemma xfor_inv_case_lemma_refine : forall (I:int->hprop),
   forall (cost : int) (cost_body : int -> int),
   forall (a:int) (b:int) (F:int->~~unit) H (Q:unit->hprop),
   ((a <= b) -> exists H',
          (H ==> I a \* H')
       /\ (forall i, is_local (F i))
       /\ (forall i, a <= i <= b -> F i (\$ ceil (cost_body i) \* I i) (# I(i+1)))
       /\ (cumul (fun i => ceil (cost_body i)) a b <= cost)
       /\ (I (b+1) \* H' ==> Q tt \* \GC)) ->
   ((a > b) ->
          (0 <= cost)
       /\ (H ==> Q tt \* \GC)) ->
   (For i = a To b Do F i Done_) (\$ ceil cost \* H) Q.
Proof.
  introv Ha_le_b Ha_gt_b.
  assert (cost_nonneg : 0 <= cost0). {
    destruct (Z.le_gt_cases a b) as [a_le_b | a_gt_b].
    - specializes~ Ha_le_b ___. destruct Ha_le_b as (? & H').
      rewrite cumulP in H'. rewrite big_nonneg_Z. apply H'.
      intros. simpl. apply ceil_pos.
    - specializes~ Ha_gt_b ___. math.
  }
  applys xfor_inv_case_lemma
    (fun (i:int) => \$ cumul (fun i => ceil (cost_body i)) i b \* I i).
  - intro a_le_b. specializes~ Ha_le_b.
    destruct Ha_le_b as (H' & H1 & Hl & H2 & Hcumul & H3).
    eexists. splits.
    + hchange H1. hsimpl.
      rewrite~ ceil_eq. hsimpl_credits. math. admit. (* ok *)
    + intros i Hi.
      xframe_but (\$ ceil (cost_body i) \* I i). auto.
      assert (forall f, cumul f i b = f i + cumul f (i + 1) b) as cumul_lemma by admit.
      rewrite cumul_lemma; clear cumul_lemma.
      credits_split. hsimpl. admit. (* ok *)
      admit. (* ok *)
      applys H2. math. xsimpl_credits.
    + xchange H3. admit. (* todo *)
  - intro a_gt_b. specializes~ Ha_gt_b. math. destruct Ha_gt_b as (? & HH).
    (* todo *) admit.
Qed.

Lemma xfor_inv_lemma_refine : forall (I:int->hprop),
  forall (cost : int) (cost_body : int -> int),
  forall (a:int) (b:int) (F:int->~~unit) H H',
  (a <= b+1) ->
  (forall i, a <= i <= b -> F i (\$ ceil (cost_body i) \* I i) (# I(i+1))) ->
  (H ==> I a \* H') ->
  (forall i, is_local (F i)) ->
  (cumul (fun i => ceil (cost_body i)) a (b+1) <= cost) ->
  (For i = a To b Do F i Done_) (\$ ceil cost \* H) (# I (b+1) \* H').
Proof using.
  introv ML MI MH Mloc HI. applys xfor_inv_case_lemma_refine I; intros C.
  { exists H'. splits~. admit. (* ok *) hsimpl. }
  { splits. admit. (* ok *) xchange MH. math_rewrite (a = b + 1). xsimpl. }
Qed.

Lemma xfor_inv_void_lemma_refine :
  forall (a:int) (b:int) (F:int->~~unit) H (cost : int),
  (a > b) ->
  (0 <= cost) ->
  (For i = a To b Do F i Done_) (\$ ceil cost \* H) (# H).
Proof using.
  introv ML MC.
  applys xfor_inv_case_lemma_refine (fun (i:int) => \[]); intros C.
  { false. }
  { splits~. xsimpl. }
  Unshelve. exact (fun _ => 0).
Qed.

Ltac xfor_inv_core I ::=
  xfor_pre_ensure_evar_post ltac:(fun _ =>
    tryif is_refine_cost_goal then (
      first [ eapply (@xfor_inv_lemma_pred_refine I)
            | eapply (@xfor_inv_lemma_refine I) ];
      [ | xtag_pre_post | | intro; xlocal | try reflexivity ]
   ) else (
     first [ apply (@xfor_inv_lemma_pred I)
           | apply (@xfor_inv_lemma I) ];
     [ | | xtag_pre_post ]
   )).

Ltac xfor_inv_void_core tt ::=
  xfor_pre_ensure_evar_post ltac:(fun _ =>
    tryif is_refine_cost_goal then
      eapply (@xfor_inv_void_lemma_refine)
    else
      apply (@xfor_inv_void_lemma)).

(* TODO: xfor_inv_case *)