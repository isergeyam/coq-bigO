Set Implicit Arguments.
Require Import TLC.LibTactics.
Require Import TLC.LibIntTactics.
Require Import TLC.LibListZ.
(* Load the CFML library, with time credits. *)
Require Import CFML.CFLibCredits.
(* Load the big-O library. *)
Require Import Dominated.
Require Import UltimatelyGreater.
Require Import Monotonic.
Require Import elia.
Require Import PolTac.PolTac.
(* Load the custom CFML tactics with support for big-Os *)
Require Import CFMLBigO.
(* Load the examples CF definitions. *)
Require Import Composing_specs_ml.

Notation "'len'" := LibListZ.length.

(* length --------------------------------------------------------------------*)

Lemma length_spec_explicit : forall A (l: list A),
  app length [l]
    PRE (\$ (len l + 1))
    POST (fun y => \[ y = len l ]).
Proof.
  intros. induction l as [| x l].
  { xcf. xpay. xvals. xmatch. xrets~. }
  { xcf. xpay. now rewrite credits_split_eq; hsimpl.
    xvals. xmatch. xapps. rewrite length_cons, !credits_split_eq. hsimpl.
    xrets. now rewrite length_cons. }
Qed.

Class length_spec_constants_pack := {
  length_cost_a : Z;
  length_cost_b : Z;
  length_spec_constants : forall A (l: list A),
    app length [l]
      PRE (\$ (length_cost_a * len l + length_cost_b))
      POST (fun y => \[ y = len l ]);
}.

Instance length_spec_constants_proof : length_spec_constants_pack.
Proof.
  refine {| length_cost_a := 1; length_cost_b := 1; length_spec_constants := _ |}.
  (* cheat a bit, and simply repackage [length_spec_explicit] *)
  intros. xapp_spec length_spec_explicit. hsimpl_credits. math.
Qed.

Lemma length_spec_bigO :
  specZ [costf \in_O (fun n => n)] (forall A (l: list A),
    app length [l]
      PRE (\$ costf (len l))
      POST (fun y => \[ y = len l ])).
Proof.
  (* also cheat a bit, and re-package length_spec_explicit *)
  xspecO (fun n => n + 1). intros; now xapp_spec length_spec_explicit.
  monotonic. dominated.
Qed.

(* length2 -------------------------------------------------------------------*)

Lemma length2_spec_explicit : forall A (l: list A),
  app length2 [l]
    PRE (\$ (2 * len l + 3))
    POST (fun y => \[ y = 2 * len l ]).
Proof.
  intros. xcf. weaken.
  xpay.
  xapps_spec length_spec_explicit.
  xapps_spec length_spec_explicit.
  xrets. math. math.
Qed.

Class length2_spec_constants_pack := {
  length2_cost_a : Z;
  length2_cost_b : Z;
  length2_spec_constants : forall A (l: list A),
    app length2 [l]
      PRE (\$ (length2_cost_a * len l + length2_cost_b))
      POST (fun y => \[ y = 2 * len l ]);
}.

Instance length2_spec_constants_proof : length2_spec_constants_pack.
Proof.
  (* Heavy handed version using defer+elia *)
  begin defer assuming a b.
  refine {| length2_cost_a := a; length2_cost_b := b;
            length2_spec_constants := _ |}.
  intros. xcf. weaken. xpay.
  xapps_spec length_spec_constants.
  xapps_spec length_spec_constants.
  xrets. math.
  (* Ideally (instead of what follows):
     - [generalize (len l) (length_nonneg l); defer.]
     - then have an automated solver *)
  { defer?: (2 * length_cost_a <= a). defer?: (2 * length_cost_b + 1 <= b).
    math_nia. }
  end defer. elia.
Qed.

Lemma length2_spec_bigO :
  specZ [costf \in_O (fun n => n)] (forall A (l: list A),
    app length2 [l]
      PRE (\$ costf (len l))
      POST (fun y => \[ y = 2 * len l ])).
Proof.
  xspecO_refine straight_line. intros.
  xcf. xpay.
  xapps_spec (spec length_spec_bigO). (*hack*) set (ll:=len l). piggybank: *rhs.
  xapps_spec (spec length_spec_bigO). (*hack*) set (ll:=len l). piggybank: *rhs.
  xrets. math.
  cleanup_cost. monotonic. dominated.
Qed.

(* loop ----------------------------------------------------------------------*)

Lemma loop_spec_bigO :
  specZ [costf \in_O (fun n => n^2)] (forall A (l: list A),
    app loop [l]
      PRE (\$ costf (len l))
      POST (fun (_:Z) => \[ True ])).
Proof.
  xspecO_refine recursive. intros costf M D g.
  induction l.
  { xcf. weaken. xpay. xmatch. xrets~. rew_cost.
    rewrite length_nil. defer. }
  { xcf. weaken. xpay. xmatch.
    xapps; =>_. xapps_spec (spec length_spec_bigO). xrets~.
    rewrite length_cons. rew_cost.
    generalize (len l) (length_nonneg l). defer. }
  close_cost.
  exists (fun n => n * cost length_spec_bigO n + n + 1). repeat split.
  math.
  intros.
(*  apply Z.max_case.
  { pols. forwards: cost_monotonic length_spec_bigO z (1+z); math_nia. }
  { pols.
  forwards: cost_nonneg length_spec_bigO z.
  forwards: cost_nonneg length_spec_bigO (1+z). math_nia.*) admit.

  cleanup_cost.
  monotonic. (* ugh *) admit.
  setoid_rewrite Z.pow_2_r. dominated.
  setoid_rewrite <-Z.mul_1_l at 1. apply dominated_mul; dominated.
Admitted.
