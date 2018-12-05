Require Import CFML.CFLib.
Open Scope Z_scope.

(** Utilities *)

Class IsEvar {A : Type} (x: A) :=
  MkIsEvar : True.

Hint Extern 0 (IsEvar ?x) =>
  (is_evar x; exact I) : typeclass_instances.

Class IsNotEvar {A : Type} (x: A) :=
  MkIsNotEvar : True.

Hint Extern 0 (IsNotEvar ?x) =>
  (tryif is_evar x then fail else exact I) : typeclass_instances.

Class Unify {A : Type} (x y : A) :=
  MkUnify : x = y.

Instance Unify_refl: forall A (x : A),
  Unify x x.
Proof. reflexivity. Qed.

(********************************************************************)

(* Iterated (+) *)
Definition big_add (l : list int) : int :=
  List.fold_left Z.add l 0.

Definition big_add_acc (l : list int) (acc : int) : int :=
  List.fold_left Z.add l acc.

(* Boilerplate equations *)
Lemma big_add_nil:
  big_add nil = 0.
Proof. reflexivity. Qed.

Lemma big_add_cons: forall x l,
  big_add (x :: l) = big_add_acc l x.
Proof. intros. reflexivity. Qed.

Lemma big_add_acc_nil acc:
  big_add_acc nil acc = acc.
Proof. reflexivity. Qed.

Lemma big_add_acc_cons x l acc:
  big_add_acc (x :: l) acc = big_add_acc l (acc + x).
Proof. reflexivity. Qed.

(* Lemmas *)
Lemma big_add_of_acc: forall l acc,
  big_add_acc l acc = big_add l + acc.
Proof.
  induction l; intros;
  rewrite ?big_add_nil, ?big_add_acc_nil, ?big_add_cons, ?big_add_acc_cons.
  - math.
  - rewrite (IHl (acc + a)), (IHl a). math.
Qed.

Lemma big_add_app: forall l1 l2,
  big_add (l1 ++ l2) = big_add l1 + big_add l2.
Proof.
  induction l1; intros; rew_list; rewrite ?big_add_nil, ?big_add_cons.
  - math.
  - rewrite !big_add_of_acc, IHl1. math.
Qed.

(* Iterated (-) *)
Definition big_sub (x : int) (l : list int) : int :=
  List.fold_left Z.sub l x.

(* Boilerplate equations *)
Lemma big_sub_nil x:
  big_sub x nil = x.
Proof. reflexivity. Qed.

Lemma big_sub_cons x y l:
  big_sub x (y :: l) = big_sub (x - y) l.
Proof. reflexivity. Qed.

(* Lemmas *)
Lemma big_sub_big_add: forall l x,
  big_sub x l = x - big_add l.
Proof.
  induction l; intros;
  rewrite ?big_sub_nil, ?big_add_nil, ?big_sub_cons, ?big_add_cons.
  - now rewrite Z.sub_0_r.
  - rewrite !IHl, (big_add_of_acc _ a). math.
Qed.

(********************************************************************)

Class AddIntList (l : list int) (c : int) :=
  MkAddIntList : c = big_add l.

Class AddIntListAcc (l : list int) (acc c : int) :=
  MkAddIntListAcc : c = big_add_acc l acc.

Hint Mode AddIntList ! - : typeclass_instances.
Hint Mode AddIntListAcc ! ! - : typeclass_instances.

Instance AddIntList_nil:
  AddIntList nil 0.
Proof. reflexivity. Qed.

Instance AddIntList_cons: forall x l c,
  AddIntListAcc l x c ->
  AddIntList (x :: l) c.
Proof.
  introv ->. unfold AddIntList, AddIntListAcc.
  simpl. now rewrite big_add_cons.
Qed.

Instance AddIntListAcc_nil: forall acc,
  AddIntListAcc nil acc acc.
Proof. reflexivity. Qed.

Instance AddIntListAcc_cons: forall x l acc c,
  AddIntListAcc l (acc + x) c ->
  AddIntListAcc (x :: l) acc c.
Proof. introv ->. reflexivity. Qed.

Goal True.
  eassert (AddIntList (0 :: 1 :: 2 :: 3 :: nil) _).
  typeclasses eauto.
Abort.

Class SubIntList (x : int) (l : list int) (y : int) :=
  MkSubIntList : y = big_sub x l.

Hint Mode SubIntList - ! - : typeclass_instances.

Instance SubIntList_nil: forall x,
  SubIntList x nil x.
Proof. reflexivity. Qed.

Instance SubIntList_cons: forall x y l z,
  SubIntList (x - y) l z ->
  SubIntList x (y :: l) z.
Proof. introv ->. reflexivity. Qed.

Goal True.
  eassert (SubIntList 42 (0 :: 1 :: 2 :: nil) _).
  typeclasses eauto.
Abort.

(********************************************************************)
(* Refine credits marker *)
Lemma credits_refine_def :
  { credits_refine | forall (c : int), credits_refine c = c }.
Proof. exists (fun (x:int) => x). eauto. Qed.

Definition credits_refine := proj1_sig credits_refine_def.

Notation " ⟨ c ⟩ " := (credits_refine c) (format "⟨ c ⟩").
Hint Opaque credits_refine : typeclass_instances.
Global Opaque credits_refine.

Lemma credits_refine_eq c:
  ⟨ c ⟩ = c.
Proof. apply (proj2_sig credits_refine_def). Qed.

(**********************************************************)
(* Hack: it seems we can get into trouble if we do not manually instantiate
   credits expressions of the form "\$ ?c x" into a lambda.

   See https://github.com/coq/coq/issues/6643
 *)

Class CreditsPreprocessEta (c1 c2 : int) :=
  MkCreditsPreprocessEta : c1 = c2.

Hint Extern 0 (CreditsPreprocessEta ⟨?c1 _⟩ ?c2) =>
  (is_evar c1;
   let cf := fresh in
   pose (cf := c1);
   unshelve instantiate (1 := _) in (Value of cf);
   [ refine (fun _ => _); shelve | hnf ];
   clear cf;
   reflexivity) : typeclass_instances.

Instance CreditsPreprocessEta_default: forall c,
  CreditsPreprocessEta c c | 100.
Proof. reflexivity. Qed.

(* Preprocess all credits in a heap expression *)

Class HeapPreprocessCredits (h1 h2 : hprop) :=
  MkHeapPreprocessCredits : h1 = h2.

Class HeapPreprocessCredits' (h1 h2 : hprop) :=
  MkHeapPreprocessCredits' : HeapPreprocessCredits h1 h2.

Instance HeapPreprocessCredits_of': forall h1 h2,
  HeapPreprocessCredits' h1 h2 ->
  HeapPreprocessCredits h1 h2.
Proof. eauto. Qed.

Hint Mode HeapPreprocessCredits' ! - : typeclass_instances.

Instance HeapPreprocessCredits'_star: forall h1 h1' h2 h2',
  HeapPreprocessCredits h1 h1' ->
  HeapPreprocessCredits h2 h2' ->
  HeapPreprocessCredits' (h1 \* h2) (h1' \* h2').
Proof.
  intros. unfold HeapPreprocessCredits', HeapPreprocessCredits in *.
  now subst.
Qed.

Instance HeapPreprocessCredits'_credits: forall c c',
  CreditsPreprocessEta c c' ->
  HeapPreprocessCredits' (\$ c) (\$ c').
Proof.
  intros.
  unfold CreditsPreprocessEta,
    HeapPreprocessCredits', HeapPreprocessCredits in *. now subst.
Qed.

Instance HeapPreprocessCredits_default: forall h,
  HeapPreprocessCredits h h | 100.
Proof. intros. now unfold HeapPreprocessCredits. Qed.

(**********************************************************)
(* Star: Like "\*" but cleans up \[] *)

Class Star (h1 h2 h3 : hprop) :=
  MkStar : h1 \* h2 = h3.

Class Star'l (h1 h2 h3 : hprop) :=
  MkStar'l : Star h1 h2 h3.

Class Star'r (h1 h2 h3 : hprop) :=
  MkStar'r : Star h1 h2 h3.

Instance Star_of'l: forall h1 h2 h3,
  Star'l h1 h2 h3 ->
  Star h1 h2 h3.
Proof. eauto. Qed.

Instance Star_of'r: forall h1 h2 h3,
  Star'r h1 h2 h3 ->
  Star h1 h2 h3.
Proof. eauto. Qed.

Hint Mode Star'l ! - - : typeclass_instances.
Hint Mode Star'r - ! - : typeclass_instances.

Instance Star'_emp_l: forall h, Star'l \[] h h.
Proof. intros. apply star_neutral_l. Qed.

Instance Star'_emp_r: forall h, Star'r h \[] h.
Proof. intros. apply star_neutral_r. Qed.

Instance Star_default: forall h1 h2, Star h1 h2 (h1 \* h2) | 2.
Proof. reflexivity. Qed.

(**********************************************************)
(* CleanupEmp: removes the \[] in a heap by recursively applying Star *)

Class CleanupEmp (h1 h2 : hprop) :=
  MkCleanupEmp : h1 = h2.

Class CleanupEmp' (h1 h2 : hprop) :=
  MkCleanupEmp' : CleanupEmp h1 h2.

Instance CleanupEmp_of': forall h1 h2,
  CleanupEmp' h1 h2 ->
  CleanupEmp h1 h2.
Proof. eauto. Qed.

Hint Mode CleanupEmp' ! - : typeclass_instances.

Instance CleanupEmp'_star: forall h1 h1' h2 h2' h1h2',
  CleanupEmp h1 h1' ->
  CleanupEmp h2 h2' ->
  Star h1' h2' h1h2' ->
  CleanupEmp' (h1 \* h2) h1h2'.
Proof. introv -> -> ->. now unfold CleanupEmp. Qed.

Instance CleanupEmp_default: forall h,
  CleanupEmp h h | 10.
Proof. reflexivity. Qed.

Goal forall H1 H2, exists H3,
  H1 ==> H2 \* H3 ->
  \[] \* (H1 \* \[])  ==> H2 \* \[] \* H3.
Proof.
  intros. eexists. intros HH1.
  assert (L: forall h1 h1' h2 h2',
    CleanupEmp h1 h1' ->
    CleanupEmp h2 h2' ->
    h1' ==> h2' ->
    h1 ==> h2).
  { introv -> ->. eauto. }
  eapply L; [ once (typeclasses eauto) .. |].
  apply HH1.
Abort.

(**********************************************************)
(* Concat: typeclass-level list concatenation.
   NB: must only be called on fully concrete lists. *)

Class Concat {A} (l1 l2 l3 : list A) :=
  MkApp : l1 ++ l2 = l3.

Instance Concat_nil: forall A (l: list A), Concat nil l l.
Proof. intros. reflexivity. Qed.

Instance Concat_cons: forall A x (l1 l2 l3: list A),
  Concat l1 l2 l3 ->
  Concat (x :: l1) l2 (x :: l3).
Proof. intros. unfold Concat in *. subst. reflexivity. Qed.

(**********************************************************)
(* GetCredits: gets the list of credits sub-expressions *)

(* Iterated \$ *)
Definition heap_is_credits_list (l : list int) : hprop :=
  \$ big_add l.

Notation "\$* l" := (heap_is_credits_list l) (at level 40).

Lemma credits_list_nil: \$* nil = \[].
Proof. unfold heap_is_credits_list. now rewrite big_add_nil, credits_zero_eq. Qed.

Lemma credits_list_cons x l: \$* (x :: l) = \$ x \* \$* l.
Proof.
  unfold heap_is_credits_list.
  now rewrite big_add_cons, big_add_of_acc, credits_split_eq, star_comm.
Qed.

Lemma credits_list_app l1 l2:
  \$* (l1 ++ l2) = \$* l1 \* \$* l2.
Proof.
  unfold heap_is_credits_list.
  now rewrite big_add_app, credits_split_eq.
Qed.

(*****************)

Class GetCredits (h1 h2 : hprop) (l : list int) :=
  MkGetCredits : h1 = h2 \* heap_is_credits_list l.

Class GetCredits' (h1 h2 : hprop) (l : list int) :=
  MkGetCredits' : GetCredits h1 h2 l.

Instance GetCredits_of': forall h1 h2 l,
  GetCredits' h1 h2 l ->
  GetCredits h1 h2 l.
Proof. eauto. Qed.

Hint Mode GetCredits' ! - - : typeclass_instances.

Instance GetCredits'_star: forall h1 h1' h2 h2' h1h2' l1 l2 l1l2,
  GetCredits h1 h1' l1 ->
  GetCredits h2 h2' l2 ->
  Star h1' h2' h1h2' ->
  Concat l1 l2 l1l2 ->
  GetCredits' (h1 \* h2) h1h2' l1l2.
Proof.
  intros. unfold GetCredits', GetCredits, Star, Concat in *.
  subst. rewrite credits_list_app.
  rewrite <-!star_assoc. fequal.
  rewrite star_comm, <-star_assoc. fequal.
  now rewrite star_comm.
Qed.

Instance GetCredits'_credits: forall c,
  GetCredits' (\$ c) \[] (c :: nil).
Proof.
  intros. unfold GetCredits', GetCredits.
  now rewrite star_neutral_l, credits_list_cons, credits_list_nil,
    star_neutral_r.
Qed.

Instance GetCredits_no_credits: forall h,
  GetCredits h h nil
| 100.
Proof.
  intros. unfold GetCredits. now rewrite credits_list_nil, star_neutral_r.
Qed.

Goal forall H1 H2 H3 a b c, exists H d,
  (H1 \* \$* (b :: nil) ==> (H2 \* H \* H3) \* \$* (a :: d :: c :: nil)) ->
  \$ b \* H1 ==> H2 \* H \* (\$ a \* \$ d \* (H3 \* \$ c)).
Proof.
  intros. do 2 eexists. intros.
  asserts L: (forall h1 h1' h2 h2' l1 l2,
    GetCredits h1 h1' l1 ->
    GetCredits h2 h2' l2 ->
    h1' \* \$* l1 ==> h2' \* \$* l2 ->
    h1 ==> h2).
  { intros. unfold GetCredits in *. now subst. }
  eapply L. typeclasses eauto. typeclasses eauto.


  eassumption.
Abort.

(**********************************************************)
(* GetCreditsExpr: gets the first number of credits that matches [c].

   NB: initially [c] can be an evar (in which case it gets unified with the evar
   found in [h1]), or not (in which case the search succeeds iff a corresponding
   number of credits is found). *)

Class GetCreditsExpr (h1 : hprop) (c : int) (h2 : hprop) :=
  MkGetCreditExpr : h1 = h2 \* \$ c.

Hint Mode GetCreditsExpr ! - - : typeclass_instances.

Instance GetCreditsExpr_star_l: forall h1 h2 h1' h1'h2 c,
  GetCreditsExpr h1 c h1' ->
  Star h1' h2 h1'h2 ->
  GetCreditsExpr (h1 \* h2) c h1'h2
| 2.
Proof.
  intros. unfold GetCreditsExpr, Star in *. subst.
  rewrite <-star_assoc, (star_comm (\$ c)), star_assoc.
  reflexivity.
Qed.

Instance GetCreditsExpr_star_r: forall h1 h2 h2' h1h2' c,
  GetCreditsExpr h2 c h2' ->
  Star h1 h2' h1h2' ->
  GetCreditsExpr (h1 \* h2) c h1h2'
| 3 (* search left first *).
Proof.
  intros. unfold GetCreditsExpr, Star in *. subst.
  rewrite star_assoc. reflexivity.
Qed.

Instance GetCreditsExpr_evars: forall c1 c2,
  IsEvar c1 ->
  IsEvar c2 ->
  Unify c1 c2 ->
  GetCreditsExpr (\$ c1) c2 \[].
Proof.
  introv ? ? ->. unfold GetCreditsExpr in *. subst.
  now rewrite star_neutral_l.
Qed.

(* This is a bit coarse grained, but we want to support querying for ⟨?x⟩ with
   ⟨_⟩ for example, *and* if there is a ?x, we do not want to instantiate it
   with ⟨_⟩... *)
Instance GetCreditsExpr_notevar: forall c1 c2,
  IsNotEvar c1 ->
  Unify c1 c2 ->
  GetCreditsExpr (\$ c1) c2 \[].
Proof.
  introv ? ->. unfold GetCreditsExpr in *. subst. now rewrite star_neutral_l.
Qed.

Goal forall H1 H2 H3 a b c, exists H d,
  \$b \* H1 ==> (H2 \* H \* \$a \* H3 \* \$c) \* \$⟨d⟩ ->
  \$b \* H1 ==> (H2 \* H \* \$⟨d⟩ \* H3 \* \$c) \* \$a ->
  \$ b \* H1 ==> H2 \* H \* (\$ a \* \$ ⟨d⟩ \* (H3 \* \$ c)).
Proof.
  intros. do 2 eexists. intros HH1 HH2.
  asserts L: (forall c h1 h2 h2',
    GetCreditsExpr h2 c h2' ->
    h1 ==> h2' \* \$ c ->
    h1 ==> h2).
  { intros. unfold GetCreditsExpr in *. now subst. }
  dup.
  { eapply (L ⟨_⟩). typeclasses eauto. apply HH1. }
  dup.
  { eapply (L a). typeclasses eauto. apply HH2. }
  rewrite credits_refine_eq.
  eapply (L ⟨_⟩). Fail typeclasses eauto.
Abort.

(**********************************************************)

Class HasSingleCreditsExpr (h h' : hprop) (c : int) :=
  MkHasSingleCreditsExpr : h = h' \* \$ c.

Lemma HasSingleCreditsExpr_of_GetCredits: forall h h' cs c,
  GetCredits h h' cs ->
  cs = c :: nil ->
  HasSingleCreditsExpr h h' c.
Proof.
  intros. unfold GetCredits, HasSingleCreditsExpr in *.
  subst. now rewrite credits_list_cons, credits_list_nil, star_neutral_r.
Qed.

(* FUTURE: could that be expressed as a "Hint Committed" in the future?
   (when these get implemented). *)
Hint Extern 0 (HasSingleCreditsExpr ?h ?h' ?c) =>
  (eapply HasSingleCreditsExpr_of_GetCredits;
   [ once (typeclasses eauto) | reflexivity ]) : typeclass_instances.

Class HasNoCredits (h : hprop) :=
  MkHasNoCredits : True.

Lemma HasNoCredits_of_GetCredits: forall h h' cs,
  GetCredits h h' cs ->
  cs = nil ->
  HasNoCredits h.
Proof. intros. exact I. Qed.

(* FUTURE: use Hint Committed? *)
Hint Extern 0 (HasNoCredits ?h) =>
  (eapply HasNoCredits_of_GetCredits;
   [ once (typeclasses eauto) | reflexivity ]) : typeclass_instances.

(**********************************************************)

Lemma GCGC_eq_GC:
  \GC \* \GC = \GC.
Proof.
  unfold heap_is_gc, heap_is_star.
  apply fun_ext_1. intros h.
  apply prop_ext. split.
  - intros (h1 & h2 & (? & [HH1 ?]) & (? & [HH2 ?]) & ?). unpack. split.
    + subst. apply~ heap_affine_union.
    + subst. exists (HH1 \* HH2). unfold heap_is_star. do 2 eexists. eauto.
  - intros (? & [HH ?]). exists h heap_empty. repeat split; eauto.
    + apply heap_affine_empty.
    + exists \[]. unfold heap_is_empty. eauto.
Qed.

Class HasGC (h : hprop) :=
  MkHasGC : h = h \* \GC.

Class HasGC' (h : hprop) :=
  MkHasGC' : HasGC h.

Lemma HasGC_of': forall h,
  HasGC' h ->
  HasGC h.
Proof. eauto. Qed.

Hint Mode HasGC' ! : typeclass_instances.

Instance HasGC'_star_l: forall h1 h2,
  HasGC h1 ->
  HasGC' (h1 \* h2).
Proof.
  introv ->. unfold HasGC', HasGC.
  now rewrite <-!star_assoc, (star_comm _ \GC), (star_assoc \GC), GCGC_eq_GC.
Qed.

Instance HasGC'_star_r: forall h1 h2,
  HasGC h2 ->
  HasGC' (h1 \* h2).
Proof.
  introv ->. unfold HasGC', HasGC.
  now rewrite <-!star_assoc, GCGC_eq_GC.
Qed.

Instance HasGC'_GC:
  HasGC' \GC.
Proof. unfold HasGC', HasGC. now rewrite GCGC_eq_GC. Qed.

Instance HasGC_evar: forall h h',
  IsEvar h ->
  Unify h (\GC \* h') ->
  HasGC h.
Proof.
  introv _ ->. unfold HasGC.
  now rewrite <-star_assoc, (star_comm _ \GC), (star_assoc \GC), GCGC_eq_GC.
Qed.