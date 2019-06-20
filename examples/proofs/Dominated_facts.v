Require Import Dominated UltimatelyGreater.
Require Import TLC.LibTactics.
Require Import Psatz.
Open Scope Z_scope.

Goal forall f,
    dominated Z_filterType (fun n => Z.max 0 (f n)) f.
Proof. intros. dominated. Qed.

Goal
  ~ (forall f, dominated Z_filterType f (fun n => Z.max 0 (f n))).
Proof.
  intros H.
  specializes H (fun n => -n). destruct H as [c [n0 HH]].
  specializes HH (Z.max 1 n0) __. lia. nia.
Qed.
