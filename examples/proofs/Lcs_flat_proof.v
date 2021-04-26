Set Implicit Arguments.
Require Import TLC.LibTactics.
Require Import TLC.LibListSort.
Require Import TLC.LibListZ.
(* Load the CFML library, with time credits. *)
Require Import CFML.CFLibCredits.
Require Pervasives_ml.
Require Array_ml.
Require Import Pervasives_proof.
Require Import ArrayCredits_proof.
(* Load the big-O library. *)
Require Import Dominated.
Require Import UltimatelyGreater.
Require Import Monotonic.
Require Import LibZExtra.
Require Import DominatedNary.
Require Import LimitNary.
Require Import Generic.
(* Load the custom CFML tactics with support for big-Os *)
Require Import CFMLBigO.
(* Load the CF definitions. *)
Require Import Lcs_flat_ml.

Inductive SubSeq {A:Type} : list A -> list A -> Prop :=
 | SubNil (l:list A) : SubSeq nil l
 | SubCons1 (x:A) (l1 l2:list A) (H: SubSeq l1 l2) : SubSeq l1 (x::l2)
 | SubCons2 (x:A) (l1 l2:list A) (H: SubSeq l1 l2) : SubSeq (x::l1) (x::l2).

Parameter subseq_iff: forall A l1 l2 (x : A), SubSeq (x::l1) l2 <-> exists l2' l2'',
  l2 = (l2' & x) ++ l2'' /\ SubSeq l1 l2''. 

Local Ltac my_invert H := inversion H; subst; clear H.

Lemma subseq_cons: forall A l1 l2 (x : A), SubSeq (x::l1) l2 -> SubSeq l1 l2. 
Proof.
  intros. remember (x::l1) as l1'. induction H. 
  - discriminate Heql1'. 
  - subst. assert (x::l1 = x::l1) by reflexivity. apply IHSubSeq in H0. 
  constructor. assumption. 
  - my_invert Heql1'. constructor. assumption. 
Qed.

Lemma subseq_app: forall A l1 l2 (x : A), SubSeq l1 l2 -> SubSeq (l1 & x) (l2 & x). 
Proof.
  intros. induction H. 
  - induction l. 
    + rewrite last_nil. apply SubCons2. apply SubNil. 
    + rewrite last_cons. apply SubCons1. assumption. 
  - rewrite last_cons. apply SubCons1. assumption. 
  - rewrite last_cons. rewrite last_cons. apply SubCons2. assumption. 
Qed.

Lemma subseq_nil: forall A (l : list A), SubSeq l nil -> l = nil. 
Proof.
  intros. my_invert H. reflexivity. 
Qed.

Lemma subseq_app_inv: forall A l1 l2 (x : A), SubSeq (l1 & x) (l2 & x) -> SubSeq l1 l2. 
Proof.
Admitted.
  (* intros A l1. induction l1. intros. constructor. 
  intros l2. induction l2. intros. admit. 
  intros. 
  (* intros. destruct l1. constructor. rewrite last_cons in H. rewrite subseq_iff in H. 
  rewrite subseq_iff. destruct H as [l2' [l2'' [H1 H2]]].  *)
  (* intros. destruct l1. constructor. destruct l2. rewrite last_cons in H. rewrite last_nil in H. 
  my_invert H. my_invert H2. destruct l1. 
  {rewrite last_nil in H1. my_invert H1. } 
  {rewrite last_cons in H1. my_invert H1. }
  rewrite last_cons in H. rewrite last_cons in H. remember (a::l1 & x) as l1'. remember (a::l2 & x) as l2'. induction H. 
  - discriminate. 
  - subst. apply IHSubSeq. reflexivity. 
  - subst.  *)
Qed. *)

Definition Lcs {A: Type} l l1 l2 :=
  SubSeq l l1 /\ SubSeq l l2 /\ 
  (forall l': list A, SubSeq l' l1 /\ SubSeq l' l2 -> length l' <= length l). 

Lemma lcs_nil_nil: forall A (l: list A), Lcs nil nil l. 
Proof.
  intros. unfold Lcs. split. constructor. split. constructor. intros. destruct H as [H _]. 
  apply subseq_nil in H. rewrite H. rewrite length_nil. math. 
Qed.

Lemma lcs_app_eq: forall A (l1 l2 l: list A) (x: A),
  Lcs l l1 l2 -> Lcs (l & x) (l1 & x) (l2 & x). 
Proof.
  unfold Lcs. intros. destruct H as [H1 [H2 H3]]. split. 
  - apply subseq_app. assumption. 
  - split. 
    + apply subseq_app. assumption. 
    + intros. destruct l'. rewrite length_nil. math.
    (* TODO *)
     Admitted. 
(* Qed. *)
Lemma lcs_app_neq: forall A (l1 l2 l l': list A) (x y : A),
  x <> y -> Lcs l (l1&x) l2 -> Lcs l' l1 (l2&x) -> length l' <= length l ->
  Lcs l (l1&x) (l2&y). 
Proof.
  (* TODO *)
Admitted.

Ltac auto_tilde ::= try solve [ auto with maths | false; math ].

Definition ZZle (p1 p2 : Z * Z) :=
  let (x1, y1) := p1 in
  let (x2, y2) := p2 in
  1 <= x1 <= x2 /\ 0 <= y1 <= y2.

(* ATTENTION: INCOMPLETE, WON'T COMPILE, SHOULD BE COMMENTED OUT *)
Lemma lcs_spec:
  specO
    (product_filterType Z_filterType Z_filterType)
    ZZle
  ( fun cost =>
  forall (l1 l2 : list int) p1 p2,
  app lcs [p1 p2]
  PRE (\$(cost (LibListZ.length l1, LibListZ.length l2)) \*
  p1 ~> Array l1 \* p2 ~> Array l2)
  POST (fun p => Hexists (l : list int), p ~> Array l (*\* \[Lcs l l1 l2]*))
  )
  (fun '(n,m) => n * m).
Proof.
  xspecO_refine straight_line. xcf. 
  xpay.  xapp~. intros. xapp~. intros. rewrite <- H. rewrite <- H0. xapp~. 
  assert (0 <= length l1) by (apply length_nonneg). 
  assert (0 <= length l2) by (apply length_nonneg). 
  rewrite <- H in H1. 
  rewrite <- H0 in H2. 
  { math_nia. }
  intros. weaken. 
  xfor_inv (fun (i:int) => 
    Hexists (x' : list (list int)),
    p1 ~> Array l1 \*
    p2 ~> Array l2 \*
    c ~> Array x' \*
    \[length x' = (n+1)*(m+1)]). 
  { math_nia. }
  2: {
    hsimpl. rewrite H1. apply length_make. math_nia. 
  }
  2: {
    intros. xapp~. apply~ int_index_prove. math_nia. 
    intros. xapp~. 
  }
  intros. xpay. xpull. intros. 
  xfor_inv (fun (j:int) => 
    Hexists (x' : list (list int)),
    p1 ~> Array l1 \*
    p2 ~> Array l2 \*
    c ~> Array x' \*
    \[length x' = (n+1)*(m+1)]). 
  { math_nia. }
  2: {
    hsimpl. assumption. 
  }
  2: {
    hsimpl. assumption.
  }
  intros. xpay. xpull. intros. 
  xapp~. { apply~ int_index_prove. }
  intros. xapp~. { apply~ int_index_prove. }
  intros. xret. intros. xif. 
  {
    xapp~. { apply~ int_index_prove. }
    intros. xapp~. 
    { apply~ int_index_prove. math_nia. math_nia. } 
    intros. xret. intros. xapp~. 
    { apply~ int_index_prove. math_nia. math_nia. } 
    xpull. hsimpl_credits. rewrite <- H5. 
    apply length_update. 
  }
  {
    xapp~. { apply~ int_index_prove. math_nia. math_nia. }
    intros. xret. intros. xapp~. 
    { apply~ int_index_prove. math_nia. math_nia. } 
    intros. xret. intros. xif. 
    {
      xapp~. 
      { apply~ int_index_prove. math_nia. math_nia. } 
      intros. xapp~. 
      { apply~ int_index_prove. math_nia. math_nia. } 
      hsimpl_credits. rewrite <- H5. apply length_update. 
    }
    {
      xapp~. 
      { apply~ int_index_prove. math_nia. math_nia. } 
      intros. xapp~. 
      { apply~ int_index_prove. math_nia. math_nia. } 
      hsimpl_credits. rewrite <- H5. apply length_update. 
    }
  }
Admitted.
