Set Implicit Arguments.
Require Import TLC.LibTactics.
Require Import TLC.LibListSort.
Require Import TLC.LibListZ.
Require Import TLC.LibOrder. 
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

Local Ltac auto_tilde ::= try solve [ auto with maths | false; math ].

Local Ltac my_invert H := inversion H; subst; clear H.

Lemma cons_injective: forall {A} x (l1 l2: list A), l1 = l2 -> x :: l1 = x :: l2. 
Proof.
  intros. rewrite H. reflexivity. 
Qed.


Lemma take_plus_one: forall (i : nat) (l: list int), 
  1 <= i <= length l -> take i l = take (i - 1) l & l[i-1]. 
Proof.
  intros. generalize dependent i. induction l. 
  - intros. rewrite length_nil in H. auto_false~. 
  - intros. rewrite take_cons_pos. destruct i. auto_false~. destruct i. 
    rewrite take_zero. rewrite take_zero. rewrite app_nil_l. 
    rewrite read_zero.  reflexivity. rewrite take_cons_pos. 
    rewrite read_cons_case. case_if. auto_false~. rewrite last_cons. 
    apply cons_injective. remember (S (S i) - 1) as i'. 
    remember (to_nat i') as i''. 
    assert (i' = i''). rewrite Heqi''. symmetry. apply to_nat_nonneg. math. 
    rewrite H0. apply IHl. rewrite <- H0. subst. rewrite length_cons in H. math. 
    math. math. 
Qed.

Lemma last_head: forall (l: list int), length l > 0 -> 
  exists l' x, l = l' & x. 
Proof.
  intros. exists (take (length l - 1) l) l[(length l) - 1]. 
  rewrite <- take_full_length at 1. apply take_plus_one. math. 
Qed.

Inductive SubSeq {A:Type} : list A -> list A -> Prop :=
 | SubNil (l:list A) : SubSeq nil l
 | SubCons1 (x:A) (l1 l2:list A) (H: SubSeq l1 l2) : SubSeq l1 (x::l2)
 | SubCons2 (x:A) (l1 l2:list A) (H: SubSeq l1 l2) : SubSeq (x::l1) (x::l2).

Lemma subseq_cons: forall A l1 l2 (x : A), SubSeq (x::l1) l2 -> SubSeq l1 l2. 
Proof.
  intros. remember (x::l1) as l1'. induction H. 
  - discriminate Heql1'. 
  - subst. constructor. apply IHSubSeq. reflexivity. 
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

Lemma subseq_length: forall (l a: list int), SubSeq l a -> length l <= length a. 
Proof.
  intros l. induction l. 
  - intros. rewrite length_nil. math. 
  - intros. my_invert H. 
    * apply subseq_cons in H0. apply IHl in H0. 
      rewrite length_cons. rewrite length_cons. math. 
    * apply IHl in H3. 
      rewrite length_cons. rewrite length_cons. math. 
Qed.

Lemma subseq_cons_l: forall A l1 l2 (x : A),  SubSeq (x :: l1) l2 <-> 
  exists l2' l2'', l2 = l2' & x ++ l2'' /\ SubSeq l1 l2''. 
Proof.
  split. generalize dependent x. generalize dependent l2. 
  {induction l1.  
  - intros l2. induction l2. 
    + intros. my_invert H. 
    + intros. my_invert H. 
      * apply IHl2 in H2. destruct H2 as [l2' [l2'' [H2 H3]]]. 
        exists (a :: l2') l2''. rewrite H2. auto. 
      * exists (@nil A) l2. auto. 
  - intros l2. induction l2. 
    + intros. my_invert H. 
    + intros. my_invert H. 
      * apply IHl2 in H2. destruct H2 as [l2' [l2'' [H2 H3]]]. 
        exists (a0 :: l2') l2''. rewrite H2. auto. 
      * exists (@nil A) l2. auto. 
  }
  {
    intros H. destruct H as [l2' [l2'' [H1 H2]]]. rewrite H1. generalize dependent l2. induction l2'. 
    - intros. rewrite last_nil. apply SubCons2. auto. 
    - intros. admit. 
  }
Admitted.


Lemma subseq_app_r: forall l1 l2 (x y : int), 
  SubSeq (l1 & x) (l2 & y) -> SubSeq l1 l2. 
Proof.
  intros l1. 
  induction l1. 
  - constructor. 
  - intros. rewrite last_cons in H. apply subseq_cons_l in H. 
    destruct H as [l2' [l2'' [H1 H2]]]. rewrite subseq_cons_l. 
    lets H3: subseq_length H2. rewrite length_last in H3. 
    assert (length l2'' > 0) by math. 
    lets H5: last_head l2'' H. destruct H5 as [l' [z H5]]. rewrite H5 in H1. 
    rewrite H5 in H2. apply IHl1 in H2. exists l2' l'. split. 
    assert (l2' & a ++ l' & z = (l2' & a ++ l') & z). rewrite last_app. 
    (* why reflexivity does not work? *)
    admit. 
    rewrite H0 in H1. apply last_eq_last_inv in H1. destruct H1 as [H1 _]. 
    rewrite H1. 
    (* why reflexivity does not work? *)
    admit. auto. 
Admitted.

Definition Lcs {A: Type} l l1 l2 :=
  SubSeq l l1 /\ SubSeq l l2 /\ 
  (forall l': list A, SubSeq l' l1 /\ SubSeq l' l2 -> length l' <= length l). 

Lemma lcs_nil_nil: forall A (l: list A), Lcs nil nil l. 
Proof.
  intros. unfold Lcs. split. constructor. split. constructor. intros. destruct H as [H _]. 
  apply subseq_nil in H. rewrite H. rewrite length_nil. math. 
Qed.

Lemma lcs_symm: forall A (l l1 l2 : list A), Lcs l l1 l2 <-> Lcs l l2 l1. 
Proof.
  intros. split. 
  - unfold Lcs. intros[H1 [H2 H3]]. split. auto. split. auto. 
    intros l' [H4 H5]. specialize (H3 l'). apply H3. split; auto.
  - unfold Lcs. intros[H1 [H2 H3]]. split. auto. split. auto. 
    intros l' [H4 H5]. specialize (H3 l'). apply H3. split; auto. 
Qed.

Lemma lcs_app_eq: forall (l1 l2 l: list int) (x: int),
  Lcs l l1 l2 -> Lcs (l & x) (l1 & x) (l2 & x). 
Proof.
  unfold Lcs. intros. destruct H as [H1 [H2 H3]]. split. 
  apply subseq_app. assumption. split. 
  apply subseq_app. assumption. 
  intros. destruct l'. rewrite length_nil. math. 
  remember (z :: l') as l''. 
  assert (HM: length l'' > 0). rewrite Heql''. rewrite length_cons. math. 
  lets M: last_head l'' HM. destruct M as [ll [y M]]. rewrite M. 
  rewrite length_last. rewrite length_last. destruct H as [Hl1 Hl2]. 
  rewrite M in Hl1. rewrite M in Hl2. 
  apply subseq_app_r in Hl1. apply subseq_app_r in Hl2. 
  assert (Hll: length ll <= length l) by auto. math. 
Qed. 

Lemma lcs_app_neq: forall A (l1 l2 l l': list A) (x y : A),
  x <> y -> Lcs l (l1&x) l2 -> Lcs l' l1 (l2&y) -> length l' <= length l ->
  Lcs l (l1&x) (l2&y). 
Proof.
  (* TODO *)
Admitted.



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
  POST (fun p => Hexists (l : list int), p ~> Array l \* \[Lcs l l1 l2]))
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
    \[length x' = (n+1)*(m+1)] \*
    \[forall i1 i2 : int, 0 <= i1 < i -> 0 <= i2 <= m -> 
        Lcs x'[i1*(m+1) + i2] (take i1 l1 ) (take i2 l2) ] \* 
    \[forall i', i*(m+1) <= i' < (n+1)*(m+1) ->
        x'[i'] = nil ]
    ). 
  { math_nia. }
  2: {
    hsimpl.
    - intros. rewrite H1. rewrite read_make. reflexivity. apply~ int_index_prove. 
    - intros. assert (0 <= i1 < 1 -> i1 = 0) by math_nia. apply H4 in H2. 
      rewrite H2. rewrite take_zero. rewrite H1. rewrite read_make. 
      apply lcs_nil_nil. apply~ int_index_prove. math_nia. 
    - rewrite H1. apply length_make. math_nia. 
  }
  2: {
    intros. xapp~. apply~ int_index_prove. math_nia. 
    intros. xapp~. hsimpl_credits. specialize (H3 n m). 
    rewrite take_ge in H3. rewrite take_ge in H3. 
    assert (((n * (m + 1)%I)%I + m)%I = (((n + 1)%I * (m + 1)%I)%I - 1)%I) by math_nia. 
    rewrite H6 in H3. rewrite H5. apply H3. math_nia. math_nia. math_nia. math_nia. 
  }
  intros. xpay. xpull. intros. 
  xfor_inv (fun (j:int) => 
    Hexists (x' : list (list int)),
    p1 ~> Array l1 \*
    p2 ~> Array l2 \*
    c ~> Array x' \*
    \[length x' = (n+1)*(m+1)] \*
    \[forall i1 i2 : int, 0 <= i1 <= i -> 0 <= i2 <= m -> 
        i1*(m+1) + i2 < i*(m+1) + j -> 
        Lcs x'[i1*(m+1) + i2] (take i1 l1 ) (take i2 l2) ] \*
    \[forall i', i*(m+1) + j <= i' < (n+1)*(m+1) ->
        x'[i'] = nil ]
    ). 
  { math_nia. }
  2: {
    hsimpl. 
    - intros. apply H5. math_nia. 
    - intros. 
      remember (to_nat i1) as i1'. 
      remember (to_nat i) as i'. 
      assert (i1 = i1'). rewrite Heqi1'. symmetry. apply to_nat_nonneg. math. 
      assert (i = i'). rewrite Heqi'. symmetry. apply to_nat_nonneg. math. 
      assert ((i1' <= i')%nat) by math. 
      apply le_lt_eq_dec in H11. 
      destruct H11.
      + assert (i1 < i) by math. clear Heqi1' Heqi' l H9 H10 i' i1'. 
        apply H4; math. 
      + assert (i1 = i) by math. clear Heqi1' Heqi' e H9 H10 i' i1'. 
        rewrite lcs_symm. assert (x0[((i1 * (m + 1)%I)%I + 0)%I] = nil). 
        apply H5. math_nia. asserts_rewrite (i2 = 0). math_nia. 
        rewrite H9. apply lcs_nil_nil. 
    - assumption. 
  }
  2: {
    hsimpl. 
    - intros. apply H9. math_nia. 
    - intros. apply H8; math_nia. 
    - assumption. 
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
    xpull. hsimpl_credits. 
    - intros. 
      remember (((i * (m + 1)) + i0)) as j. 
      remember x11__ as v. 
      assert ((x1[j:=v])[i'] = x1[i']). 
      (* TODO: WHY THE HECK read_update_neq does not work??? *)
      rewrite read_update_case. case_if; auto_false~. 
      apply~ int_index_prove. math_nia. 
      rewrite H16. apply H9. math_nia. 
    - intros. 
      remember (to_nat i1) as i1'. 
      remember (to_nat i) as i'. 
      assert (i1 = i1'). rewrite Heqi1'. symmetry. apply to_nat_nonneg. math. 
      assert (i = i'). rewrite Heqi'. symmetry. apply to_nat_nonneg. math. 
      assert ((i1' <= i')%nat) by math. 
      apply le_lt_eq_dec in H20. 
      destruct H20. 
      + assert (i1 < i) by math. 
        rewrite read_update_case. case_if. 
        assert (((i * (m + 1)%I)%I + i0)%I > ((i1 * (m + 1)%I)%I + i2)%I) by math_nia. 
        auto_false~. apply H8; math_nia. apply int_index_prove; math_nia. 
      + remember (to_nat i2) as i2'. 
        remember (to_nat (i0 + 1)) as i0'. 
        assert (i2 = i2'). rewrite Heqi2'. symmetry. apply to_nat_nonneg. math. 
        assert (i0 + 1 = i0'). rewrite Heqi0'. symmetry. apply to_nat_nonneg. math. 
        assert ((i2' < i0')%nat) by math_nia. 
        apply le_lt_eq_dec in H22. 
        destruct H22. 
        * assert (i2 < i0) by math. 
          rewrite read_update_case. case_if. 
          assert (((i * (m + 1)%I)%I + i0)%I > ((i1 * (m + 1)%I)%I + i2)%I) by math_nia. 
          auto_false~. apply H8; math_nia. apply int_index_prove; math_nia. 
        * assert (i1 = i) by math. assert (i2 = i0) by math. 
          rewrite read_update_case. case_if. rewrite H14. 
          rewrite H22. rewrite H19. rewrite take_plus_one. 
          rewrite <- H19. rewrite H20. rewrite take_plus_one. rewrite <- H20. 
          rewrite H23. rewrite H12. 
          rewrite <- H11. rewrite C. rewrite H10. rewrite <- H10. 
          apply lcs_app_eq. 
          rewrite H13. 
          asserts_rewrite (((((i - 1)%I * (m + 1)%I)%I + i0)%I - 1)%I = (((i - 1)%I * (m + 1)%I)%I + (i0%I - 1)%I)). 
          math. apply H8; math_nia. math_nia. math_nia. apply~ int_index_prove; math_nia. 
    - rewrite <- H7. apply length_update. 
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
      hsimpl_credits.
      {
        intros. 
        rewrite read_update_case. case_if; auto_false~. 
        apply int_index_prove; math_nia. 
      }
      - intros. 
        remember (to_nat i1) as i1'. 
        remember (to_nat i) as i'. 
        assert (i1 = i1'). rewrite Heqi1'. symmetry. apply to_nat_nonneg. math. 
        assert (i = i'). rewrite Heqi'. symmetry. apply to_nat_nonneg. math. 
        assert ((i1' <= i')%nat) by math. 
        apply le_lt_eq_dec in H22. 
        destruct H22. 
        + assert (i1 < i) by math. 
          rewrite read_update_case. case_if. 
          assert (((i * (m + 1)%I)%I + i0)%I > ((i1 * (m + 1)%I)%I + i2)%I) by math_nia. 
          auto_false~. apply H8; math_nia. apply int_index_prove; math_nia. 
        + remember (to_nat i2) as i2'. 
          remember (to_nat (i0 + 1)) as i0'. 
          assert (i2 = i2'). rewrite Heqi2'. symmetry. apply to_nat_nonneg. math. 
          assert (i0 + 1 = i0'). rewrite Heqi0'. symmetry. apply to_nat_nonneg. math. 
          assert ((i2' < i0')%nat) by math_nia. 
          apply le_lt_eq_dec in H24. 
          destruct H24. 
          * assert (i2 < i0) by math. 
            rewrite read_update_case. case_if. 
            assert (((i * (m + 1)%I)%I + i0)%I > ((i1 * (m + 1)%I)%I + i2)%I) by math_nia. 
            auto_false~. apply H8; math_nia. apply int_index_prove; math_nia. 
          * assert (i1 = i) by math. assert (i2 = i0) by math. 
            rewrite read_update_case. case_if. rewrite H16. 
            rewrite H20. rewrite take_plus_one. rewrite <- H20. 
            rewrite H22. rewrite take_plus_one. rewrite <- H22. 
            rewrite H24. rewrite H25. 
            rewrite <- H10. rewrite <- H11. 
            (* rewrite <- H11. rewrite C. rewrite H10. rewrite <- H10.  *)
            rewrite lcs_symm. 
            eapply lcs_app_neq. auto. rewrite H10. 
            rewrite <- H25. rewrite H22. rewrite <- take_plus_one. rewrite lcs_symm. 
            apply H8; math_nia. math_nia. rewrite lcs_symm. rewrite H11. rewrite H21. 
            rewrite <- take_plus_one. rewrite <- H21. apply H8; math_nia. math_nia. 
            asserts_rewrite (((i * (m + 1)%I)%I + (i0%I - 1)%I) = (((i * (m + 1)%I)%I + i0)%I - 1)%I ). math_nia. 
            rewrite <- H12. rewrite <- H14. rewrite <- H13. rewrite <- H15. math. math. math. 
            apply int_index_prove; math_nia. 
      - rewrite <- H7. apply length_update. 
    }
    {
      xapp~. 
      { apply~ int_index_prove. math_nia. math_nia. } 
      intros. xapp~. 
      { apply~ int_index_prove. math_nia. math_nia. } 
      hsimpl_credits. 
      {
        intros. 
        rewrite read_update_case. case_if; auto_false~. 
        apply int_index_prove; math_nia. 
      }
      - intros. 
        remember (to_nat i1) as i1'. 
        remember (to_nat i) as i'. 
        assert (i1 = i1'). rewrite Heqi1'. symmetry. apply to_nat_nonneg. math. 
        assert (i = i'). rewrite Heqi'. symmetry. apply to_nat_nonneg. math. 
        assert ((i1' <= i')%nat) by math. 
        apply le_lt_eq_dec in H22. 
        destruct H22. 
        + assert (i1 < i) by math. 
          rewrite read_update_case. case_if. 
          assert (((i * (m + 1)%I)%I + i0)%I > ((i1 * (m + 1)%I)%I + i2)%I) by math_nia. 
          auto_false~. apply H8; math_nia. apply int_index_prove; math_nia. 
        + remember (to_nat i2) as i2'. 
          remember (to_nat (i0 + 1)) as i0'. 
          assert (i2 = i2'). rewrite Heqi2'. symmetry. apply to_nat_nonneg. math. 
          assert (i0 + 1 = i0'). rewrite Heqi0'. symmetry. apply to_nat_nonneg. math. 
          assert ((i2' < i0')%nat) by math_nia. 
          apply le_lt_eq_dec in H24. 
          destruct H24. 
          * assert (i2 < i0) by math. 
            rewrite read_update_case. case_if. 
            assert (((i * (m + 1)%I)%I + i0)%I > ((i1 * (m + 1)%I)%I + i2)%I) by math_nia. 
            auto_false~. apply H8; math_nia. apply int_index_prove; math_nia. 
          * assert (i1 = i) by math. assert (i2 = i0) by math. 
            rewrite read_update_case. case_if. rewrite H16. 
            rewrite H20. rewrite take_plus_one. rewrite <- H20. 
            rewrite H22. rewrite take_plus_one. rewrite <- H22. 
            rewrite H24. rewrite H25. 
            rewrite <- H10. rewrite <- H11. 
            (* rewrite <- H11. rewrite C. rewrite H10. rewrite <- H10.  *)
            eapply lcs_app_neq. auto. rewrite H11. rewrite H21. rewrite <- take_plus_one. rewrite <- H21. 
            asserts_rewrite ((((i * (m + 1)%I)%I + i0)%I - 1)%I = ((i * (m + 1)%I)%I + (i0%I - 1)%I)). math. 
            apply H8; math.  math. 
            rewrite H10. 
            rewrite <- H25. rewrite H22. rewrite <- take_plus_one. rewrite <- H22. 
            apply H8; math_nia. math. rewrite <- H12. rewrite <- H14. rewrite <- H13. rewrite <- H15. math. math. math. 
            apply int_index_prove; math_nia. 
      - rewrite <- H7. apply length_update. 
    }
  }
  reflexivity. 
  cleanup_cost. 
  { equates 1; swap 1 2.
    { instantiate (1 := (fun '(x, y) => _)). apply fun_ext_1. intros [x y].
      rewrite !cumul_const'. rew_cost. reflexivity. }
    intros [x1 y1] [x2 y2] [H1 H2]. math_nia. }
  apply_nary dominated_sum_distr_nary; swap 1 2.
  dominated. 
  apply_nary dominated_sum_distr_nary.
  apply_nary dominated_sum_distr_nary.
  apply_nary dominated_sum_distr_nary.
  dominated. 
  { apply dominated_transitive with (fun '(x, y) => x * 1).
    - (* TODO: improve using some setoid rewrite instances? *)
      apply dominated_eq. intros [? ?]. math.
    - apply_nary dominated_mul_nary; dominated. 
  }
  { apply dominated_transitive with (fun '(x, y) => 1 * y).
    - (* TODO: improve using some setoid rewrite instances? *)
      apply dominated_eq. intros [? ?]. math.
    - apply_nary dominated_mul_nary; dominated. 
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
    monotonic. limit. dominated. apply_nary dominated_sum_distr_nary; dominated. } 
Qed.
