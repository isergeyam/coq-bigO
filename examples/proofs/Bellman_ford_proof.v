Set Implicit Arguments.
Require Import TLC.LibTactics.
Require Import TLC.LibIntTactics.
(* Load the CFML library, with time credits. *)
Require Import CFML.CFLibCredits.
Require Pervasives_ml.
Require Array_ml.
Require Import Pervasives_proof.
Require Import ArrayCredits_proof.
(* Load the big-O library. *)
Require Import Dominated.
Require Import DominatedNary.
Require Import FilterNary.
Require Import LimitNary.
Require Import UltimatelyGreater.
Require Import Monotonic.
Require Import LibZExtra.
Require Import Generic.
(* Load the custom CFML tactics with support for big-Os *)
Require Import CFMLBigO.
(* Load the CF definitions. *)
Require Import Bellman_ford_ml.

Ltac auto_tilde ::= try solve [ auto with maths | false; math ].

Definition ZZle (p1 p2 : Z * Z) :=
  let (x1, y1) := p1 in
  let (x2, y2) := p2 in
  1 <= x1 <= x2 /\ 0 <= y1 <= y2.

Lemma bellman_ford_spec :
  specO
    (product_filterType Z_filterType Z_filterType)
    ZZle
    (fun cost =>
      forall (inf source : int) t (edges : list (int * int * int)%type) (nb_nodes : int),
        0 <= source < nb_nodes ->
        1 <= nb_nodes ->
        app bellman_ford [inf source t nb_nodes]
        PRE (\$ (cost (nb_nodes, LibListZ.length edges)) \* t ~> Array edges)
        POST (fun (_: array int) => t ~> Array edges))
    (fun '(n,m) => n * m).
Proof.
  xspecO_refine straight_line. xcf.
  xpay.
  xapp~. intros ds Hds. subst ds.
  xapp~. apply index_make. apply~ int_index_prove.
  xseq.

  { xfor_inv (fun (_:int) =>
      Hexists (ds: list int), t ~> Array edges \* d ~> Array ds). math.
    { intros i Hi. xpay.
      xpull. intros ds.
      xapp as edges_nb. intro Hedges_nb.
      weaken. xfor_inv (fun (_:int) =>
        Hexists (ds: list int), t ~> Array edges \* d ~> Array ds). math.
      { intros j Hj. xpull. intros ds'.
        xpay. xapps. apply~ int_index_prove.
        xmatch.
        xapp as d1. admit. (* TODO *) intro Hd1.
        xapp as d2. admit. (* TODO *) intro Hd2.
        xapp. admit. (* TODO *) }
      1,2: now hsimpl.
      { subst edges_nb.
        match goal with |- cumul _ _ (fun _ => ?x) <= _ => ring_simplify x end.
        sets edges_nb: (LibListZ.length edges). reflexivity. }
    }
    { hsimpl. }
  }
  { xpull. intros ds. xret. hsimpl. }
  cleanup_cost.

  { equates 1; swap 1 2.
    { instantiate (1 := (fun '(x, y) => _)). apply fun_ext_1. intros [x y].
      rewrite !cumul_const'. rew_cost. reflexivity. }
    intros [x1 y1] [x2 y2] [H1 H2]. math_nia. }

  apply_nary dominated_sum_distr_nary; swap 1 2.
  dominated.

  apply_nary dominated_sum_distr_nary.
  { apply dominated_transitive with (fun '(x, y) => x * 1).
    - (* TODO: improve using some setoid rewrite instances? *)
      apply dominated_eq. intros [? ?]. math.
    - apply_nary dominated_mul_nary; dominated. }
  { eapply dominated_transitive.
    apply dominated_product_swap.
    apply Product.dominated_big_sum_bound_with.
    { apply filter_universe_alt. intros. rewrite~ <-cumul_nonneg. math_lia. }
    { monotonic. }
    { limit. (* FIXME *) apply limit_sum_cst_r. limit. }
    simpl. dominated.

    now repeat apply_nary dominated_sum_distr_nary; dominated.
    repeat apply_nary dominated_sum_distr_nary; dominated.
    etransitivity. apply Product.dominated_big_sum_bound.
    ultimately_greater. monotonic. dominated.
Admitted.

Lemma bellman_ford_spec_within :
  specO
    (within_filterType (product_filterType Z_filterType Z_filterType)
      (fun '(n,m) => m <= n^2))
    ZZle
    (fun cost =>
      forall (inf source : int) t (edges : list (int * int * int)%type) (nb_nodes : int),
        0 <= source < nb_nodes ->
        1 <= nb_nodes ->
        app bellman_ford [inf source t nb_nodes]
        PRE (\$ (cost (nb_nodes, LibListZ.length edges)) \* t ~> Array edges)
        POST (fun (_: array int) => t ~> Array edges))
    (fun '(n,m) => n ^ 3).
Proof.
  econstructor; try (intros; apply~ bellman_ford_spec).
  eapply dominated_transitive.
  { destruct (cost_dominated bellman_ford_spec) as [c U].
    exists c. applys within_finer U. }
  { exists 1. rewrite withinP.
    rewrite productP. do 2 exists (fun x => 0 <= x).
    splits; try apply ultimately_ge_Z.
    intros n m N M D.
    rewrite Z.abs_eq; [| math_nia].
    rewrite Z.abs_eq; swap 1 2. apply~ Z.pow_nonneg.
    rewrite D. math_nia. }
Qed.

Lemma bellman_ford_spec_derived :
  specZ [cost \in_O (fun n => n^3)] (
    forall (inf source : int) t (edges : list (int * int * int)%type) (nb_nodes : int),
      0 <= source < nb_nodes ->
      1 <= nb_nodes ->
      LibListZ.length edges <= nb_nodes ^ 2 ->
      app bellman_ford [inf source t nb_nodes]
      PRE (\$ (cost nb_nodes) \* t ~> Array edges)
      POST (fun (_: array int) => t ~> Array edges)).
Proof.
  xspecO (fun n =>
    let m := If 0 < n then n^2 else 0 in
    let n' := If 0 < n then n else 1 in
    cost bellman_ford_spec (n', m)).
  { introv Hnodes Hedges. intros; xapply~ (spec bellman_ford_spec).
    hsimpl_credits. (* FIXME *)
    match goal with |- le 0 (?x - ?y) => enough (y <= x) by math end.
    apply (cost_monotonic bellman_ford_spec).
    unfolds ZZle. splits~. cases_if~. cases_if~.
  }
  { eapply monotonic_comp. monotonic.
    intros x1 x2 H. unfold ZZle. splits~.
    - cases_if; cases_if~.
    - cases_if~. apply~ Z.pow_nonneg.
    - cases_if; cases_if~. apply~ Z.pow_le_mono. apply~ Z.pow_nonneg. }
  { eapply dominated_transitive.
    eapply dominated_ultimately_eq.
    { exists 1. intros. cases_if~. reflexivity. }
    eapply dominated_comp_eq.
    apply (cost_dominated bellman_ford_spec).
    2: intro; reflexivity.
    2: intro; reflexivity.
    limit. }
Qed.
