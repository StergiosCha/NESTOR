(************************************************************************)
(*  Set Theoretic Definitions for Champollion Semantics                  *)
(*  Provides the basic set operations used in Champollion.v             *)
(************************************************************************)

Require Import Coq.Sets.Ensembles.

(* 1. Basic Types *)
Definition e := Type.
Definition SetOfEntities := e -> Prop.

(* 2. Set Membership and Operations *)
(* In Ensembles, In is defined as: In U A x means x is in A *)
Definition In_s (P : SetOfEntities) (x : e) : Prop := P x.

Definition intersection (P Q : SetOfEntities) : SetOfEntities :=
  fun x => P x /\ Q x.

Definition union (P Q : SetOfEntities) : SetOfEntities :=
  fun x => P x \/ Q x.

(* 3. Inclusion Relations *)
Definition included (P Q : SetOfEntities) : Prop :=
  forall x, P x -> Q x.

Definition strict_included (P Q : SetOfEntities) : Prop :=
  included P Q /\ exists x, Q x /\ ~ P x.

(* 4. Emptiness *)
Definition Empty_set (P : SetOfEntities) : Prop :=
  forall x, ~ P x.

(* 5. Hint for compatibility *)
(* Make sure 'e' is recognized as a Type *)
Global Arguments In_s P x.
Global Arguments intersection P Q x.
