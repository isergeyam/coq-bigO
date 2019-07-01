From TLC Require Import LibFun LibTactics LibIntTactics.
Require Import ZArith.

Open Scope Z_scope.

Ltac case_max :=
  match goal with |- context [Z.max ?n ?m] =>
    destruct (Z.max_spec_le n m) as [(_ & ->) | (_ & ->)]
  end.

(*******************************************************************)

Class Add (a b c : Z) :=
  MkAdd : c = a + b.

Class Opp (a b : Z) :=
  MkOpp : b = -a.

Class Sub (a b c : Z) :=
  MkSub : c = a - b.

Instance Add0l a : Add 0 a a.
Proof. reflexivity. Qed.
Instance Add0r a : Add a 0 a.
Proof. unfold Add. now rewrite Z.add_0_r. Qed.
Instance Add_default a b : Add a b (a+b) | 5.
Proof. reflexivity. Qed.

Instance Sub0l a b :
  Opp a b ->
  Sub 0 a b.
Proof. intros ->. reflexivity. Qed.
Instance Sub0r a : Sub a 0 a.
Proof. unfold Sub. now rewrite Z.sub_0_r. Qed.
Instance Sub_default a b : Sub a b (a-b) | 5.
Proof. reflexivity. Qed.

Instance Opp0 : Opp 0 0.
Proof. reflexivity. Qed.
Instance OppOpp a : Opp (-a) a.
Proof. unfold Opp. math. Qed.
Instance Opp_default a : Opp a (-a) | 5.
Proof. reflexivity. Qed.

Instance Sub_opp a b c :
  Add a b c ->
  Sub a (-b) c.
Proof. intros ->. unfold Sub. math. Qed.
Instance Add_opp a b c :
  Sub b a c ->
  Add (-a) b c.
Proof. intros ->. unfold Add. math. Qed.

Class Mul (a b c : Z) :=
  MkMul : c = a * b.

Instance Mul0l a : Mul 0 a 0.
Proof. reflexivity. Qed.
Instance Mul0r a : Mul a 0 0.
Proof. unfold Mul. now rewrite Z.mul_0_r. Qed.
Instance Mul1l a : Mul 1 a a.
Proof. unfold Mul. now rewrite Z.mul_1_l. Qed.
Instance Mul1r a : Mul a 1 a.
Proof. unfold Mul. now rewrite Z.mul_1_r. Qed.
Instance Mulm1l a b :
  Opp a b ->
  Mul (-1) a b.
Proof. intros ->. unfold Mul. math. Qed.
Instance Mulm1r a b :
  Opp a b ->
  Mul a (-1) b.
Proof. intros ->. unfold Mul. math. Qed.
Instance Mul_default a b : Mul a b (a*b) | 5.
Proof. reflexivity. Qed.

Class Le (a b : Z) :=
  MkLe : a <= b.

Instance Le_same a : Le a a.
Proof. unfold Le. reflexivity. Qed.
Instance Le_max_l a b : Le a (Z.max a b).
Proof. unfold Le. math_lia. Qed.
Instance Le_max_r a b : Le b (Z.max a b).
Proof. unfold Le. math_lia. Qed.
Hint Extern 1 (Le _ _) => assumption : typeclass_instances.

Class Max (a b c : Z) :=
  MkMax : c = Z.max a b.

Instance Max_le_l a b : Le a b -> Max a b b.
Proof. unfold Le, Max. math_lia. Qed.
Instance Max_le_r a b : Le b a -> Max a b a.
Proof. unfold Le, Max. math_lia. Qed.
Instance Max_default a b : Max a b (Z.max a b) | 20.
Proof. reflexivity. Qed.

Local Ltac spec :=
  intros;
  repeat match goal with H1 : ?X, H2 : ?X -> ?Y |- _ =>
    specialize (H2 H1)
  end.

Class FactorBy (f: Z) (a b c : Z) :=
  MkFactorBy : a = b * f + c.

Class FactorByLe (f: Z) (a b c : Z) :=
  MkFactorByLe : 0 <= f -> a <= b * f + c.

Instance FactorByLe_FactorBy f a b c :
  FactorBy f a b c ->
  FactorByLe f a b c | 20.
Proof. unfold FactorBy, FactorByLe. math. Qed.

Instance FactorBy_add  f a1 a2 b1 b2 c1 c2 b c :
  FactorBy f a1 b1 c1 ->
  FactorBy f a2 b2 c2 ->
  Add b1 b2 b ->
  Add c1 c2 c ->
  FactorBy f (a1 + a2) b c.
Proof. intros -> -> -> ->. unfold FactorBy. math_nia. Qed.

Instance FactorByLe_add f a1 a2 b1 b2 c1 c2 b c :
  FactorByLe f a1 b1 c1 ->
  FactorByLe f a2 b2 c2 ->
  Add b1 b2 b ->
  Add c1 c2 c ->
  FactorByLe f (a1 + a2) b c.
Proof. intros ? ? -> ->. unfold FactorByLe in *. spec. math_nia. Qed.

Instance FactorBy_sub f a1 a2 b1 b2 c1 c2 b c :
  FactorBy f a1 b1 c1 ->
  FactorBy f a2 b2 c2 ->
  Sub b1 b2 b ->
  Sub c1 c2 c ->
  FactorBy f (a1 - a2) b c.
Proof. intros -> -> -> ->. unfold FactorBy. math_nia. Qed.

Instance FactorByLe_sub f a1 a2 b1 b2 c1 c2 b c :
  FactorByLe f a1 b1 c1 ->
  FactorBy f a2 b2 c2 ->
  Sub b1 b2 b ->
  Sub c1 c2 c ->
  FactorByLe f (a1 - a2) b c.
Proof. intros ? -> -> ->. unfold FactorByLe in *. spec. math_nia. Qed.

Instance FactorBy_opp f a b1 c1 b c :
  FactorBy f a b1 c1 ->
  Opp b1 b ->
  Opp c1 c ->
  FactorBy f (- a) b c.
Proof. intros -> -> ->. unfold FactorBy. math_nia. Qed.

Class MulFactored a1 b1 a2 b2 a3 b3 :=
  MkMulFactored : forall f, a3 * f + b3 = (a1 * f + b1) * (a2 * f + b2).

Instance MulFactored_0l b1 a2 b2 a3 b3 :
  Mul b1 a2 a3 ->
  Mul b1 b2 b3 ->
  MulFactored 0 b1 a2 b2 a3 b3.
Proof using.
  intros ? ?. unfold Mul, MulFactored in *. subst a3 b3. math_nia.
Qed.

Instance MulFactored_0r a1 b1 b2 a3 b3 :
  Mul a1 b2 a3 ->
  Mul b1 b2 b3 ->
  MulFactored a1 b1 0 b2 a3 b3.
Proof using.
  intros ? ?. unfold Mul, MulFactored in *. subst a3 b3. math_nia.
Qed.

Instance FactorBy_mul f a1 a2 b1 b2 c1 c2 b c :
  FactorBy f a1 b1 c1 ->
  FactorBy f a2 b2 c2 ->
  MulFactored b1 c1 b2 c2 b c ->
  FactorBy f (a1 * a2) b c.
Proof.
  intros ? ? HM. unfold FactorBy, MulFactored in *. subst a1 a2.
  rewrite HM. math_nia.
Qed.

Instance FactorBy_self f :
  FactorBy f f 1 0.
Proof. unfold FactorBy. math. Qed.

Instance FactorByLe_max f a1 a2 b1 c1 b2 c2 b c :
  FactorByLe f a1 b1 c1 ->
  FactorByLe f a2 b2 c2 ->
  Max b1 b2 b ->
  Max c1 c2 c ->
  FactorByLe f (Z.max a1 a2) b c.
Proof. unfold FactorByLe, Max in *. spec. math_nia. Qed.

Instance FactorBy_default f a :
  FactorBy f a 0 a | 20.
Proof. unfold FactorBy. math_nia. Qed.

Lemma cancel_factors f : forall e1 e2 a1 b1 a2 b2,
  FactorByLe f e1 a1 b1 ->
  FactorBy f e2 a2 b2 ->
  a1 <= a2 ->
  0 <= f ->
  b1 <= b2 ->
  e1 <= e2.
Proof.
  intros * H ? ? ? ?. unfold FactorBy, FactorByLe in *. spec. math_nia.
Qed.

Ltac cancel f :=
  eapply (@cancel_factors f); [ once (typeclasses eauto) .. | | |]; auto with zarith.

(******************************************************************************)

(* Class PolSPost (a b : Z) := *)
(*   MkPolSPost : a = b. *)

(* Instance PolSPost_add a b a' b' c : *)
(*   PolSPost a a' -> *)
(*   PolSPost b b' -> *)
(*   Add a' b' c -> *)
(*   PolSPost (a + b) c. *)
(* Proof. intros -> -> ->. reflexivity. Qed. *)

(* (* todo: move -cst on the other side of the equation? *) *)

Class Simp (a b : Z) :=
  MkSimp : a = b.

Instance Simp_add a b a' b' c :
  Simp a a' ->
  Simp b b' ->
  Add a' b' c ->
  Simp (a + b) c.
Proof. intros -> -> ->. reflexivity. Qed.

Instance Simp_sub a b a' b' c :
  Simp a a' ->
  Simp b b' ->
  Sub a' b' c ->
  Simp (a - b) c.
Proof. intros -> -> ->. reflexivity. Qed.

Instance Simp_opp a a' b :
  Simp a a' ->
  Opp a' b ->
  Simp (-a) b.
Proof. intros -> ->. reflexivity. Qed.

Instance Simp_mul a b a' b' c :
  Simp a a' ->
  Simp b b' ->
  Mul a' b' c ->
  Simp (a * b) c.
Proof. intros -> -> ->. reflexivity. Qed.

Instance Simp_max a b a' b' c :
  Simp a a' ->
  Simp b b' ->
  Max a' b' c ->
  Simp (Z.max a b) c.
Proof. intros -> -> ->. reflexivity. Qed.

Instance Simp_default a : Simp a a | 40.
Proof. reflexivity. Qed.

Lemma simp_le a b a' b' :
  Simp a a' ->
  Simp b b' ->
  a' <= b' ->
  a <= b.
Proof. intros -> ->. auto. Qed.

Lemma simp_eq a b a' b' :
  Simp a a' ->
  Simp b b' ->
  a' = b' ->
  a = b.
Proof. intros -> ->. auto. Qed.

Ltac simp :=
  first [ eapply simp_le | eapply simp_eq ]; [ once (typeclasses eauto) .. |].
