Require Import CFML.CFLib.
Open Scope Z_scope.

(** Utilities *)

Class IsEvar {A : Type} (x: A) :=
  MkIsEvar : True.

Hint Extern 0 (IsEvar ?x) =>
  (is_evar x; exact I) : typeclass_instances.

Class Unify {A : Type} (x y : A) :=
  MkUnify : x = y.

Instance Unify_refl: forall A (x : A),
  Unify x x.
Proof. reflexivity. Qed.

(* Unifies evar <-> evar, notevar <-> notevar,
   but not evar <-> notevar or notevar <-> evar. *)
Class UnifySameKind {A : Type} (x y : A) :=
  MkUnifySameKind : x = y.

Hint Extern 0 (UnifySameKind ?x ?y) =>
  (tryif is_evar x then
     (tryif is_evar y then reflexivity
      else fail)
   else
     (tryif is_evar y then fail
      else reflexivity)) : typeclass_instances.

(**********************************************************)
(* Hack: it seems we can get into trouble if we do not manually instantiate
   credits expressions of the form "\$ ?c x" into a lambda.

   See https://github.com/coq/coq/issues/6643
 *)

Class CreditsPreprocessEta (c1 c2 : int) :=
  MkCreditsPreprocessEta : c1 = c2.

Hint Extern 0 (CreditsPreprocessEta (?c1 _) ?c2) =>
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

Class Star' (h1 h2 h3 : hprop) :=
  MkStar' : Star h1 h2 h3.

Instance Star_of': forall h1 h2 h3,
  Star' h1 h2 h3 ->
  Star h1 h2 h3.
Proof. eauto. Qed.

Hint Mode Star' ! ! - : typeclass_instances.

Instance Star'_emp_l: forall h, Star' \[] h h.
Proof. intros. apply star_neutral_l. Qed.

Instance Star'_emp_r: forall h, Star' h \[] h.
Proof. intros. apply star_neutral_r. Qed.

Instance Star_default: forall h1 h2, Star h1 h2 (h1 \* h2) | 2.
Proof. reflexivity. Qed.

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
  List.fold_right (fun c h => \$ c \* h) \[] l.

Notation "\$* l" := (heap_is_credits_list l) (at level 40).

Lemma credits_list_nil: \$* nil = \[].
Proof. reflexivity. Qed.

Lemma credits_list_cons x l: \$* (x :: l) = \$ x \* \$* l.
Proof. reflexivity. Qed.

Lemma credits_list_app: forall l1 l2,
  \$* (l1 ++ l2) = \$* l1 \* \$* l2.
Proof.
  induction l1; intros; rew_list.
  - rewrite credits_list_nil. rewrite~ star_neutral_l.
  - rewrite !credits_list_cons, IHl1.
    rewrite~ star_assoc.
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

Instance GetCreditsExpr_evar: forall c1 c2,
  UnifySameKind c1 c2 ->
  GetCreditsExpr (\$ c1) c2 \[].
Proof.
  intros. unfold GetCreditsExpr, UnifySameKind in *. subst.
  now rewrite star_neutral_l.
Qed.

Goal forall H1 H2 H3 a b c, exists H d,
  \$b \* H1 ==> (H2 \* H \* \$a \* H3 \* \$c) \* \$d ->
  \$b \* H1 ==> (H2 \* H \* \$d \* H3 \* \$c) \* \$a ->
  \$ b \* H1 ==> H2 \* H \* (\$ a \* \$ d \* (H3 \* \$ c)).
Proof.
  intros. do 2 eexists. intros HH1 HH2.
  asserts L: (forall c h1 h2 h2',
    GetCreditsExpr h2 c h2' ->
    h1 ==> h2' \* \$ c ->
    h1 ==> h2).
  { intros. unfold GetCreditsExpr in *. now subst. }
  dup.
  { eapply L. typeclasses eauto. apply HH1. }
  dup.
  { eapply (L a). typeclasses eauto. apply HH2. }
  match goal with |- context [ \$ ?x ] =>
    is_evar x; unify x 0 end.
  eapply L. Fail typeclasses eauto.
Abort.
