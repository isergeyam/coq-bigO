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
  xpay.  xapp~. intros. xapp~. intros. rewrite <- H. rewrite <- H0. xapp~. intros. 
  xapp~. intros. 
  xseq. weaken. 
  xfor_inv (fun (i:int) => 
    Hexists (x0 : list (array (list int)))
    (x1 : list (list (list int))),
    p1 ~> Array l1 \* p2 ~> Array l2 \* c ~> Array x0 \* x0__ ~> Array x \*
    \[index x0 n /\ forall i1 : int, 0 <= i1 <= n -> index x1[i1] m /\ 
    (\[] ==> x0[i1] ~> Array x1[i1])]).  
    3: {
  hsimpl_credits. split. rewrite H2. apply index_make. 
  apply~ int_index_prove. intros. split. remember (make (n+1) x) as x0_. 
  assert (index x0_[i1] m). rewrite Heqx0_. rewrite read_make. 
  rewrite H1. apply index_make. apply~ int_index_prove. apply~ int_index_prove. 
  rewrite Heqx0_ in H4. apply H4. rewrite read_make. rewrite H2. rewrite read_make. 
  hsimpl. admit. apply~ int_index_prove. apply~ int_index_prove. 
    }
  math. intros. 
  {
    xpull. intros. 
    xpay. weaken. 
  xfor_inv (fun (i:int) => 
    Hexists (x0 : list (array (list int)))
    (x1 : list (list (list int))),
    p1 ~> Array l1 \* p2 ~> Array l2 \* c ~> Array x0 \* x0__ ~> Array x \* 
    \[index x0 n /\ forall i1 : int, 0 <= i1 <= n -> index x1[i1] m /\ 
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
            math. xchange H7. hsimpl.
          }
          {
            specialize (H7 (i-1)). destruct H7 as [H7 _]. math. 
            rewrite index_eq_inbound in H7. apply~ int_index_prove. 
          }
          intros. xapp~. 
          rewrite index_eq_inbound in H6. apply~ int_index_prove. 
          intros. xapp~. 2: {
            rewrite H14. hsimpl. 
          }
          {
            specialize (H7 i). destruct H7 as [H7 _]. math. 
            rewrite index_eq_inbound in H7. apply~ int_index_prove. 
          }
          hsimpl. split; auto. 
        }
        xapp~. 
        rewrite index_eq_inbound in H6. apply~ int_index_prove. 
        intros. xapp~. 2: {
          rewrite H12. hsimpl. 
        }
        {
          specialize (H7 i). destruct H7 as [H7 _]. math. 
          rewrite index_eq_inbound in H7. apply~ int_index_prove. 
        }
        intros. xapp~. 
        rewrite index_eq_inbound in H6. apply~ int_index_prove. 
        intros. xapp~. 2: {
          rewrite H12. rewrite H14. hsimpl. 
        }
        {
          specialize (H7 i). destruct H7 as [H7 _]. math. 
          rewrite index_eq_inbound in H7. apply~ int_index_prove. 
        }
        hsimpl. split; auto. 
      }
    } 
    hsimpl. split; auto. destruct H4 as [H4 _]. assumption. 
    apply H4. hsimpl. apply H6. 
    (* match goal with |- cumul _ _ (fun _ => ?x) <= _ => ring_simplify x end.  *)
    reflexivity. 
  }
  reflexivity. 
  (* xpull. hsimpl_credits. split. rewrite H2. apply index_make. 
  apply~ int_index_prove. intros. split. admit. admit. 
  match goal with |- cumul _ _ (fun _ => ?x) <= _ => ring_simplify x end. 
  rewrite H. rewrite H0. 
  sets n1: (length l1). sets m1: (length l2). reflexivity.  *)
  xpull. intros. xapp~. destruct H3 as [H3 H4]. assumption. 
  intros. xapp~. 2: {
    destruct H3 as [H3 H5]. specialize (H5 n). 
    destruct H5. math. rewrite H4. xchange H6. hsimpl. 
  }
  {
    destruct H3 as [H3 H5]. specialize (H5 n). 
    apply H5. math. 
  }
  intros. xapp~. 
  cleanup_cost. 
  { equates 1; swap 1 2.
    { instantiate (1 := (fun '(x, y) => _)). apply fun_ext_1. intros [x y].
      rewrite !cumul_const'. rew_cost. reflexivity. }
    intros [x1 y1] [x2 y2] [H1 H2]. math_nia. }

  apply_nary dominated_sum_distr_nary; swap 1 2.
  dominated.

  apply_nary dominated_sum_distr_nary.
  { apply_nary dominated_sum_distr_nary. 
    { apply dominated_transitive with (fun '(x, y) => 1 * y).
      - (* TODO: improve using some setoid rewrite instances? *)
        apply dominated_eq. intros [? ?]. math.
      - apply_nary dominated_mul_nary; dominated. 
    }
    { apply dominated_transitive with (fun '(x, y) => x * 1).
      - (* TODO: improve using some setoid rewrite instances? *)
        apply dominated_eq. intros [? ?]. math.
      - apply_nary dominated_mul_nary; dominated. 
    }
  }
  { eapply dominated_transitive.
    apply dominated_product_swap.
    apply Product.dominated_big_sum_bound_with.
    { apply filter_universe_alt. intros. rewrite~ <-cumul_nonneg. math_lia. }
    { monotonic. }
    { limit.  }
    simpl. dominated.

    now repeat apply_nary dominated_sum_distr_nary; dominated.
    repeat apply_nary dominated_sum_distr_nary; dominated.
    etransitivity. apply Product.dominated_big_sum_bound_with. 
    intros. apply filter_universe_alt. math_lia. 
    monotonic. limit. dominated. apply_nary dominated_sum_distr_nary; dominated. 
Admitted. 
