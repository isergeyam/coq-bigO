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
Require Import Lcs_ml.

Inductive InL {A:Type} (y:A) : list A -> Prop := 
  | InHead : forall xs:list A, InL y (cons y xs) 
  | InTail : forall (x:A) (xs:list A), InL y xs -> InL y (cons x xs).

Inductive SubSeq {A:Type} : list A -> list A -> Prop :=
 | SubNil : forall l:list A, SubSeq nil l
 | SubCons1 : forall (x:A) (l1 l2:list A), SubSeq l1 l2 -> SubSeq l1 (x::l2)
 | SubCons2 : forall (x:A) (l1 l2:list A), SubSeq l1 l2 -> SubSeq (x::l1) (x::l2).

Definition Lcs {A: Type} l l1 l2 :=
  SubSeq l l1 /\ SubSeq l l2 /\ 
  (forall l': list A, SubSeq l' l1 /\ SubSeq l' l2 -> length l' <= length l). 

Ltac auto_tilde ::= try solve [ auto with maths | false; math ].

Definition ZZle (p1 p2 : Z * Z) :=
  let (x1, y1) := p1 in
  let (x2, y2) := p2 in
  1 <= x1 <= x2 /\ 0 <= y1 <= y2.

Definition hforall (A:Type) (J:A->hprop) : hprop :=
  fun (h:heap) => forall x, J x h.

Notation "'Hforall' x1 .. xn , H" :=
  (hforall (fun x1 => .. (hforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
    format "'[' 'Hforall' '/ ' x1 .. xn , '/ ' H ']'").

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
  xpay.  xapp~. intros. xapp~. intros. xapp~. hsimpl_credits. 
  intros. xapp~. hsimpl_credits. intros. 
  xseq. weaken. 
  xfor_inv (fun (i:int) => 
    Hexists (x0 : list (array (list int)))
    (x1 : list (list (list int))),
    p1 ~> Array l1 \* p2 ~> Array l2 \* c ~> Array x0 \* 
    \[index x0 (n + 1) /\ forall i1 : int, 0 <= i1 <= n -> index x1[i1] (m + 1) /\ 
    (\[] ==> (x0[i1] ~> Array x1[i1]))]).  
  math. intros. 
  {
    xpull. intros. 
    xpay. weaken. 
  xfor_inv (fun (i:int) => 
    Hexists (x0 : list (array (list int)))
    (x1 : list (list (list int))),
    p1 ~> Array l1 \* p2 ~> Array l2 \* c ~> Array x0 \* 
    \[index x0 (n + 1) /\ forall i1 : int, 0 <= i1 <= n -> index x1[i1] (m + 1) /\ 
    (\[] ==> (x0[i1] ~> Array x1[i1]))]).  
    math. intros. {
      xpull. intros. xpay. xapps~. apply~ int_index_prove. 
      xapps~. apply~ int_index_prove. xret. intros. xif. 
      {
        destruct H6 as [H6 H7]. 
        xapps~. apply~ int_index_prove. 
        xapps~. 
        rewrite index_eq_inbound in H6. 
        apply~ int_index_prove. assert (H9 := H7). 
        specialize (H7 (i-1)). 
        destruct H7 as [H7 H8]. math. 
        xapps~. Focus 2. 
        xchange H8. hsimpl. rewrite index_eq_inbound in H7. 
        apply~ int_index_prove. xret. intros. xapp~. 
        rewrite index_eq_inbound in H6. apply~ int_index_prove. 
        intros. xapp~. Focus 2. specialize (H9 i). 
        destruct H9 as [H9 H99]. math. rewrite H11. 
        xchange H99. hsimpl. specialize (H9 i). 
        destruct H9 as [H9 H99]. math. 
        rewrite index_eq_inbound in H9. apply~ int_index_prove. 
        hsimpl. split; auto.  
      }
      {
        destruct H6 as [H6 H7]. 
        xapps~. rewrite index_eq_inbound in H6. apply~ int_index_prove. 
        xapps~. 2: {
          specialize (H7 i). destruct H7 as [H7 H8]. 
          math. xchange H8. hsimpl. 
        }
        {
          specialize (H7 i). destruct H7 as [H7 H8]. 
          math. rewrite index_eq_inbound in H7. 
          apply~ int_index_prove. 
        }
        xret. intros. xapp~. 
        rewrite index_eq_inbound in H6. apply~ int_index_prove. 
        intros. xapp~. 
        2: {rewrite H9. 
          specialize (H7 (i-1)). destruct H7 as [H7 H10]. 
          math. xchange H10. hsimpl. 
        } intros. 
        { specialize (H7 (i-1)). destruct H7 as [H7 H10]. 
          math. rewrite index_eq_inbound in H7. 
          apply~ int_index_prove. 
        } intros. xret. intros. xif. {
          xapp~. 
          rewrite index_eq_inbound in H6. apply~ int_index_prove. 
          intros. xapp~. 2: {
            rewrite H12. 
            specialize (H7 (i-1)). destruct H7 as [_ H7]. 
            math. xchange H7. hsimpl. admit. 
          }
Admitted. 
