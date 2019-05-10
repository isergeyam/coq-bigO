Require Import ZArith.
Open Scope Z_scope.
Require Import List.
Require Import Template.All.
Import ListNotations MonadNotation.

Inductive expr :=
| EVar : nat -> bool -> expr
| EAdd : expr -> expr -> expr
| EAbstr : Z -> bool -> expr.

Ltac reflect_expr' term sign cont :=
  lazymatch term with
  | tApp (tConst "Coq.ZArith.BinIntDef.Z.add" []) [?x; ?y] =>
    reflect_expr' x sign ltac:(fun e1 =>
    reflect_expr' y sign ltac:(fun e2 =>
    cont (EAdd e1 e2)))
  | tApp (tConst "Coq.ZArith.BinIntDef.Z.sub" []) [?x; ?y] =>
    let sign_op := eval cbv in (negb sign) in
    reflect_expr' x sign ltac:(fun e1 =>
    reflect_expr' y sign_op ltac:(fun e2 =>
    cont (EAdd e1 e2)))
  | tApp (tConst "Coq.ZArith.BinIntDef.Z.opp" []) [?x] =>
    let sign_op := eval cbv in (negb sign) in
    reflect_expr' x sign_op ltac:(fun e1 => cont e1)
  | tRel ?n =>
    cont (EVar n sign)
  | ?x =>
    denote_term x ltac:(fun dx => cont (EAbstr dx sign))
  end.

Ltac reflect_expr term cont :=
  reflect_expr' term true cont.

Goal 5 + 3 + 5 - 2 + 5 = 0.
  match goal with |- ?X = _ =>
    quote_term X ltac:(fun t =>
    reflect_expr t ltac:(fun e => pose e))
  end.
Abort.

Ltac skip_ex t cont :=
  lazymatch t with
  | tApp
      (tInd {| inductive_mind := "Coq.Init.Logic.ex"; inductive_ind := 0 |} [])
      [tInd {| inductive_mind := "Coq.Numbers.BinNums.Z"; inductive_ind := 0 |} [];
       tLambda (nNamed _) _ ?body]
    =>
    skip_ex body cont
  | tApp
      (tInd {| inductive_mind := "Coq.Init.Specif.sigT"; inductive_ind := 0 |} [])
      [tInd {| inductive_mind := "Coq.Numbers.BinNums.Z"; inductive_ind := 0 |} [];
       tLambda (nNamed _) _ ?body]
    =>
    skip_ex body cont
  | tApp
      (tInd {| inductive_mind := "Coq.Init.Specif.sig"; inductive_ind := 0 |} [])
      [tInd {| inductive_mind := "Coq.Numbers.BinNums.Z"; inductive_ind := 0 |} [];
       tLambda (nNamed _) _ ?body]
    =>
    skip_ex body cont
  | _ =>
    cont t
  end.

Ltac quote_under_ex term cont :=
  quote_term term ltac:(fun t => skip_ex t cont).

Ltac reflect_ineqs term cont :=
  lazymatch term with
  | tApp (tInd {| inductive_mind := "Coq.Init.Logic.and"; inductive_ind := 0 |} [])
      [?x; ?y] =>
    reflect_ineqs x ltac:(fun rx =>
    reflect_ineqs y ltac:(fun ry =>
    cont constr:(rx ++ ry)))
  | tApp (tConst "Coq.ZArith.BinInt.Z.le" []) [?x; ?y] =>
    reflect_expr x ltac:(fun e1 =>
    reflect_expr y ltac:(fun e2 =>
    cont constr:([(e1, e2)])))
  | tApp (tConst "Coq.ZArith.BinInt.Z.ge" []) [?x; ?y] =>
    reflect_expr x ltac:(fun e1 =>
    reflect_expr y ltac:(fun e2 =>
    cont constr:([(e2, e1)])))
  | ?z => fail 100 "reflect_ineqs: unrecognized term" z
  end.

Goal 3 + 5 - 2 <= 0.
  match goal with |- ?X =>
    quote_term X ltac:(fun t =>
    reflect_ineqs t ltac:(fun e => pose e))
  end.
Abort.

Fixpoint add_var (l: list (nat * bool)) (n: nat) (b: bool): option (list (nat * bool)) :=
  match l with
  | [] => ret [(n, b)]
  | (n', b') :: l' =>
    if Nat.eqb n n' then (
      if bool_eq b b' then None
      else ret l'
    ) else
      l'' <- add_var l' n b ;;
      ret ((n', b') :: l'')
  end.

Fixpoint merge_vars (l1 l2: list (nat * bool)): option (list (nat * bool)) :=
  match l1 with
  | [] => ret l2
  | (n, b) :: l1' =>
    l2' <- add_var l2 n b ;;
    merge_vars l1' l2'
  end.

Notation "'do' ( x , y ) <- c1 ;; c2" := (@bind _ _ _ _ c1 (fun '(x,y) => c2))
    (at level 100, c1 at next level, right associativity) : monad_scope.

Notation exprnf := (list (nat * bool) * list (Z * bool))%type.

Definition add_nf (e1 e2: exprnf): option exprnf :=
  let '(vars1, cst1) := e1 in
  let '(vars2, cst2) := e2 in
  vars <- merge_vars vars1 vars2 ;;
  ret (vars, cst1 ++ cst2).

Definition neg_nf (e: exprnf): exprnf :=
  let '(vars, cst) := e in
  let vars' := List.map (fun '(n, b) => (n, negb b)) vars in
  let cst' := List.map (fun '(x,b) => (x, negb b)) cst in
  (vars', cst').

Fixpoint nf (e: expr): option exprnf :=
  match e with
  | EAdd e1 e2 =>
    e1nf <- nf e1 ;;
    e2nf <- nf e2 ;;
    add_nf e1nf e2nf
  | EVar n b =>
    ret ([(n, b)], [])
  | EAbstr x b =>
    ret ([], [(x, b)])
  end.

Fixpoint maxvar (e: expr): option nat :=
  match e with
  | EAdd e1 e2 =>
    match maxvar e1 with
    | None => maxvar e2
    | Some n1 =>
      match maxvar e2 with
      | None => ret n1
      | Some n2 => ret (Nat.max n1 n2)
      end
    end
  | EVar n _ => ret n
  | EAbstr _ _ => None
  end.

(* HACK *)
Definition maxvar2 '((e1, e2): expr * expr): option nat :=
  maxvar (EAdd e1 e2).

Fixpoint split_var (var: nat) (l: list (nat * bool)): option (bool * list (nat * bool)) :=
  match l with
  | [] => None
  | (n, b) :: l' =>
    if Nat.eqb var n then
      ret (b, l')
    else
      do (b', l'') <- split_var var l' ;;
      ret (b', (n, b) :: l'')
  end.

Definition classify_ineqs (var: nat) (ineqs: list exprnf):
  list exprnf * list exprnf * list exprnf
:=
  fold_left (fun '(aj, bj, phi) '(vars, cst) =>
    match split_var var vars with
    | Some (true, vars') =>
      (aj, neg_nf (vars', cst) :: bj, phi)
    | Some (false, vars') =>
      ((vars', cst) :: aj, bj, phi)
    | None =>
      (aj, bj, (vars, cst) :: phi)
    end) ineqs ([], [], []).

Inductive var_assign :=
  | maxof : list exprnf -> var_assign
  | minof : list exprnf -> var_assign
  | whatever : var_assign.

Definition step (var: nat) (ineqs: list exprnf): option (var_assign * list exprnf) :=
  let '(aj, bj, phi) := classify_ineqs var ineqs in
  match (aj, bj) with
  | ([], []) => ret (whatever, phi)
  | ([], _) => ret (minof bj, phi)
  | (_, []) => ret (maxof aj, phi)
  | (_, _) =>
    let assign := maxof aj in (* could also be [minof bj] *)
    ineqs' <-
      monad_fold_left (fun ineqs' a =>
        monad_fold_left (fun ineqs' b =>
          ab <- add_nf a (neg_nf b) ;;
          ret (ab :: ineqs')
        ) bj ineqs'
      ) aj phi ;;
    ret (assign, ineqs')
  end.

Fixpoint loop (fuel: nat)
  (var maxvar: nat) (assign: list var_assign) (ineqs: list exprnf) :
  option (list var_assign * list exprnf)
:=
  if Nat.ltb maxvar var then ret (assign, ineqs)
  else (
    do (var_asgn, ineqs') <- step var ineqs ;;
    match fuel with
    | O => None
    | S fuel' => loop fuel' (S var) maxvar (var_asgn :: assign) ineqs'
    end
  ).

Definition reduce_error {A} (f: A -> A -> A) (l : list A) : option A
  := match l with
     | [] => None
     | x :: xs => Some (fold_left f xs x)
     end.

Definition reduce {A} (f: A -> A -> A) (l : list A) (a: A) : A
  := match l with
     | [] => a
     | x :: xs => fold_left f xs x
     end.

Definition compute_exprnf_cst (cst: list (Z * bool)): Z :=
  match cst with
  | [] => 0
  | (e, b) :: cst' =>
    fold_left (fun acc '(e, b) =>
      if (b:bool) then acc + e else acc - e
    ) cst' (if (b:bool) then e else - e)
  end.

Fixpoint compute_assign
  (maxvar assignZlen: nat) (assign: list var_assign) (assignZ: list Z) :
  option (list Z)
:=
  match assign with
  | [] => ret assignZ
  | a :: assign' =>
    let get_value := (fun var =>
      let revidx := (maxvar - var)%nat in
      let idx := (assignZlen - 1 - revidx)%nat in
      nth_error assignZ idx
    ) in
    let compute_exprnf := (fun '(vars, cst) =>
      monad_fold_left (fun acc '(var, b) =>
        var_value <- get_value var ;;
        ret (if (b:bool) then acc + var_value else acc - var_value)
      ) vars (compute_exprnf_cst cst)
    ) in
    match a with
    | whatever => compute_assign maxvar (S assignZlen) assign' (0 :: assignZ)
    | maxof l =>
      lc <- monad_map compute_exprnf l ;;
      a_assign <- reduce_error Z.max lc ;;
      compute_assign maxvar (S assignZlen) assign' (a_assign :: assignZ)
    | minof l =>
      lc <- monad_map compute_exprnf l ;;
      a_assign <- reduce_error Z.min lc ;;
      compute_assign maxvar (S assignZlen) assign' (a_assign :: assignZ)
    end
  end.

Definition main_pre (ineqs: list (expr * expr)): option (nat * list exprnf) :=
  maxvar <- fold_left (fun acc ee =>
    match (maxvar2 ee, acc) with
    | (None, _) => acc
    | (Some m, None) => Some m
    | (Some m, Some m') => Some (Nat.max m m')
    end
  ) ineqs None ;;
  ineqs_nf <- monad_map (fun '(e1, e2) =>
    e1nf <- nf e1 ;;
    e2nf <- nf e2 ;;
    add_nf e1nf (neg_nf e2nf)
  ) ineqs ;;
  ret (maxvar, ineqs_nf).

Definition main (ineqs: list (expr * expr)): option (list Z * list Z) :=
  do (maxvar, ineqs_nf) <- main_pre ineqs ;;
  do (assign, final_ineqs) <- loop 5000 0 maxvar [] ineqs_nf ;;
  assignZ <- compute_assign maxvar O assign [] ;;
  final_ineqs <- monad_map (fun (e: exprnf) =>
    match e with
    | ([], cst) => Some (compute_exprnf_cst cst)
    | _ => None
    end
  ) final_ineqs ;;
  ret (assignZ, final_ineqs).

Declare Reduction elia_red :=
  cbn [add_var merge_vars add_nf neg_nf nf
       maxvar maxvar2
       split_var classify_ineqs step loop
       compute_exprnf_cst compute_assign
       main_pre main
       monad_map monad_fold_left reduce_error reduce fold_left nth_error
       ret bind option_monad
       Nat.max Nat.sub Nat.eqb Nat.ltb Nat.leb
       List.app List.map bool_eq negb
      ].

Fixpoint expr_abstract_terms (e: expr): list Z :=
  match e with
  | EAdd e1 e2 => expr_abstract_terms e1 ++ expr_abstract_terms e2
  | EVar _ _ => []
  | EAbstr x _ => [x]
  end.

Definition ineqs_abstract_terms (ineqs: list (expr * expr)): list Z :=
  fold_left (fun acc '(e1, e2) =>
    acc ++ expr_abstract_terms e1 ++ expr_abstract_terms e2
  ) ineqs [].

Declare Reduction abstract_terms_red :=
  cbn [expr_abstract_terms ineqs_abstract_terms
       List.app fold_left].

Definition ineqs_of_csts (csts: list Z): Prop :=
  let ineqs := List.map (fun (x: Z) => (x <= 0)) csts in
  reduce and ineqs True.

Declare Reduction ineqs_of_csts_red :=
  cbn [ineqs_of_csts List.map reduce fold_left].

Ltac do_ex l :=
  lazymatch l with
  | nil => idtac
  | ?x :: ?xs =>
    do_ex xs;
    exists x
  end.

Require Import Psatz.
Require Import ssreflect.

Ltac abstract_over tms cont :=
  lazymatch tms with
  | [] => cont constr:(@nil Z)
  | ?tm :: ?tms' =>
    let X := fresh "x" in
    set X := tm;
    abstract_over tms' ltac:(fun XS => cont constr:(X :: XS))
  end.

Goal 0 <= 1.
  let tms := constr:([0;1]) in
  abstract_over tms ltac:(fun XS => pose XS).
Abort.

Ltac quote_ineqs cont :=
  match goal with |- ?X =>
    quote_under_ex X ltac:(fun t =>
      reflect_ineqs t ltac:(fun rt =>
        let rt := eval cbn [List.app] in rt in
        cont rt
    ))
  end.

Ltac abstract_over_abstract cont :=
  quote_ineqs ltac:(fun rt =>
    let abstr := eval abstract_terms_red in (ineqs_abstract_terms rt) in
    abstract_over abstr ltac:(fun abstr' =>
    cont abstr'
  )).

Ltac subst_all l :=
  lazymatch l with
  | [] => idtac
  | ?X :: ?XS => subst X; subst_all XS
  end.

Ltac elia_core :=
  abstract_over_abstract ltac:(fun abstr =>
    quote_ineqs ltac:(fun rt =>
      let main_ret := eval elia_red in (main rt) in
      match main_ret with
      | Some (?l, ?final) =>
        let finalP := eval ineqs_of_csts_red in (ineqs_of_csts final) in
        cut finalP; cycle 1;
        [ subst_all abstr; cbn | intro; do_ex l ]
      end
    )).

Ltac elia :=
  elia_core;
  [ first [ lia
          | match goal with |- ?X =>
              fail 100 "Unable to prove reduced system: " X
            end]
  | lia ].

Goal exists a b, 0 <= a /\ a <= 5 /\ b >= 3.
  elia_core. lia. lia.
Qed.

Goal exists a b, 0 <= a /\ a <= b /\ b <= -3.
  elia_core. Fail lia.
Abort.

Arguments Z.add : simpl nomatch.
Arguments Z.sub : simpl nomatch.

Goal
  forall incoming_cost stop_cost ifold_remaining_cost step_cost,
  exists a b c,
  0 <= a /\
  0 <= b /\
  0 <= (a - step_cost) /\
  1 <= c /\
  (1 + (incoming_cost tt + (stop_cost + ifold_remaining_cost tt))) <= c /\
  step_cost <= a /\ (1 + (incoming_cost tt + ifold_remaining_cost tt)) <= b.
Proof.
  intros. elia_core. lia. lia.
Qed.
