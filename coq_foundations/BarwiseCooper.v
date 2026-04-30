(************************************************************************)
(*  Formalization of Barwise & Cooper (1981): Generalized Quantifiers   *)
(*  Category A: Fully Formalizable                                      *)
(*  Key Concept: Monotonicity and Conservativity                        *)
(************************************************************************)

Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.

(* ----------------------------------------------------------------- *)
(* 1. Basic Definitions                                             *)
(* ----------------------------------------------------------------- *)

Module GeneralizedQuantifiers.

  (* ----------------------------------------------------------------- *)
  (* 1. Basic Definitions                                             *)
  (* ----------------------------------------------------------------- *)

  (* ----------------------------------------------------------------- *)
  (* 1. Basic Definitions                                             *)
  (* ----------------------------------------------------------------- *)

  Parameter e : Type.
  Definition E := e -> Prop.
  
  (* A Determiner maps a restriction (noun) to a Generalized Quantifier *)
  Definition Determiner := E -> E -> Prop.

  (* Included (Subset) relation *)
  Definition subset (A B : E) : Prop :=
    forall x, A x -> B x.

  (* ----------------------------------------------------------------- *)
  (* 2. Standard Determiners                                          *)
  (* ----------------------------------------------------------------- *)

  Definition every (A B : E) : Prop :=
    subset A B.

  Definition some (A B : E) : Prop :=
    exists x, A x /\ B x.

  Definition no (A B : E) : Prop :=
    ~ exists x, A x /\ B x.

  (* at_least_two needs equality or distinctness witness *)
  Definition at_least_two (A B : E) : Prop :=
    exists x y, x <> y /\ (A x /\ B x) /\ (A y /\ B y).

  (* ----------------------------------------------------------------- *)
  (* 3. Universal Constraints (Barwise & Cooper 1981)                 *)
  (* ----------------------------------------------------------------- *)

  (* CONSERVATIVITY (The most famous universal) *)
  (* D(A)(B) <-> D(A)(A ∩ B) *)
  Definition Conservative (D : Determiner) : Prop :=
    forall A B, D A B <-> D A (fun x => A x /\ B x).

  (* MONOTONICITY *)
  (* Upward Monotone (Right): If D(A)(B) and B ⊆ B', then D(A)(B') *)
  Definition MonotoneUp (D : Determiner) : Prop :=
    forall A B B', subset B B' -> D A B -> D A B'.

  (* Downward Monotone (Right): If D(A)(B) and B' ⊆ B, then D(A)(B') *)
  Definition MonotoneDown (D : Determiner) : Prop :=
    forall A B B', subset B' B -> D A B -> D A B'.

  (* Persistence (Left Upward): If D(A)(B) and A ⊆ A', then D(A')(B) *)
  Definition Persistent (D : Determiner) : Prop :=
    forall A A' B, subset A A' -> D A B -> D A' B.
    
  (* Anti-Persistence (Left Downward): If D(A)(B) and A' ⊆ A, then D(A')(B) *)
  Definition AntiPersistent (D : Determiner) : Prop :=
    forall A A' B, subset A' A -> D A B -> D A' B.

  (* ----------------------------------------------------------------- *)
  (* 4. The Proofs                                                    *)
  (* ----------------------------------------------------------------- *)

  (* Theorem: 'every' is Conservative *)
  Theorem every_conservative : Conservative every.
  Proof.
    unfold Conservative, every, subset.
    intros A B.
    split; intros H x Hx.
    - split. apply Hx. apply H; assumption.
    - destruct (H x Hx) as [_ HB]. assumption.
  Qed.

  (* Theorem: 'some' is Conservative *)
  Theorem some_conservative : Conservative some.
  Proof.
    unfold Conservative, some.
    intros A B.
    split.
    - intros [x [Ha Hb]]. exists x. split; [assumption | split; assumption].
    - intros [x [Ha [Ha' Hb]]]. exists x. split; assumption.
  Qed.

  (* Theorem: 'every' is Downward Monotone on Left (Anti-Persistent) *)
  Theorem every_antipersistent : AntiPersistent every.
  Proof.
    unfold AntiPersistent, every, subset.
    intros A A' B Hsub Hevery x Ha'.
    apply Hevery.
    apply Hsub.
    assumption.
  Qed.

  (* Theorem: 'every' is Upward Monotone on Right *)
  Theorem every_monotone_up : MonotoneUp every.
  Proof.
    unfold MonotoneUp, every, subset.
    intros A B B' Hsub Hevery x Ha.
    apply Hsub.
    apply Hevery.
    assumption.
  Qed.

  (* Theorem: 'no' is Downward Monotone on Right *)
  Theorem no_monotone_down : MonotoneDown no.
  Proof.
    unfold MonotoneDown, no.
    intros A B B' Hsub Hno [x [Ha Hb']].
    apply Hno.
    exists x.
    split; [assumption | apply Hsub; assumption].
  Qed.
  
  (* Theorem: 'at_least_two' is Upward Monotone on Right *)
  Theorem at_least_two_monotone_up : MonotoneUp at_least_two.
  Proof.
    unfold MonotoneUp, at_least_two.
    intros A B B' Hsub [x [y [Hneq [[Hax Hbx] [Hay Hby]]]]].
    exists x, y.
    repeat split; try assumption.
    - apply Hsub; assumption.
    - apply Hsub; assumption.
  Qed.

End GeneralizedQuantifiers.
