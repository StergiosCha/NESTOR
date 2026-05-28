(************************************************************************)
(*  PTQ_Theorems.v — Key metatheorems for the PTQ formalization         *)
(************************************************************************)

From Coq Require Import Classical Classical_Prop Nat PeanoNat.
From Coq Require Import FunctionalExtensionality.
Require Import PTQ.
Set Implicit Arguments.

(* 1. every man walks → a man walks (given ∃ a man) *)

Theorem every_to_some_man_walks : forall i,
  (exists z : IndivConcept, man' z i) ->
  interp_S ex_every_man_walks g0 i ->
  interp_S ex_a_man_walks g0 i.
Proof.
  intros i [z Hz] H. simpl in *.
  unfold every_den, a_den in *. exists z. auto.
Qed.

(* 2. every man walks → John walks (given John is a man) *)

Theorem every_man_walks_inst_john : forall i,
  man' (rigid john_e) i ->
  interp_S ex_every_man_walks g0 i ->
  interp_S ex_john_walks g0 i.
Proof.
  intros i Hman H. simpl in *.
  unfold every_den, John_T, PN_to_T in *. auto.
Qed.

(* 3. "the ζ δ" entails "a ζ δ" — definites entail indefinites *)

Theorem the_entails_a : forall (cn : CN_den) (P : IV_den) i,
  the_den cn P i -> a_den cn P i.
Proof.
  intros cn P i [y [Huniq Hp]].
  exists y. split; [apply Huniq; reflexivity | exact Hp].
Qed.

(* 4. Relative clause restriction:
      "a (man such that he walks) talks" → "a man talks" *)

Theorem rel_clause_restricts : forall g i,
  interp_S (E_S4 (E_a (E_such_that (E_CN i_man) 0
                         (E_S4 (E_he 0) (E_IV i_walk))))
                  (E_IV i_talk)) g i ->
  interp_S (E_S4 (E_a (E_CN i_man)) (E_IV i_talk)) g i.
Proof.
  intros g i H. simpl in *.
  unfold a_den in *. destruct H as [x [[Hman _] Htalk]].
  exists x. auto.
Qed.

(* 5. □φ → φ  (T axiom — holds because □ is universal) *)

Theorem nec_T : forall (phi : Prop_s) (i : Index),
  Nec phi i -> phi i.
Proof. intros phi i H. apply H. Qed.

(* 6. □φ → □□φ  (S4 axiom) *)

Theorem nec_4 : forall (phi : Prop_s) (i : Index),
  Nec phi i -> Nec (Nec phi) i.
Proof. unfold Nec. auto. Qed.

(* 7. Extensional collapse biconditional:
      ∀x[man'(x)→walk'(x)] ↔ ∀e[man_ext(e)→walk_ext(e)] *)

Theorem every_man_walks_ext_iff : forall i,
  (forall x : IndivConcept, man' x i -> walk' x i) <->
  (forall e : Entity, man_ext e i -> walk_ext e i).
Proof.
  intro i. split.
  - intros H e Hm. unfold walk_ext, man_ext in *. apply H. exact Hm.
  - intros H x Hman.
    assert (man' (rigid (x i)) i)
      by (apply (man_reduces x _ i); [reflexivity | exact Hman]).
    apply (walk_reduces (rigid (x i)) x i); [reflexivity |].
    apply H. exact H0.
Qed.

(* 8. Temperature puzzle — full countermodel proof.
      "the temperature rises" does NOT entail "ninety rises". *)

Parameter cm_idx : Index.
Parameter cm_concept : IndivConcept.
Axiom cm_unique   : forall x, temperature' x cm_idx <-> x = cm_concept.
Axiom cm_rises    : rise' cm_concept cm_idx.
Axiom cm_rigid_no : ~ rise' (rigid ninety_e) cm_idx.

Theorem temperature_puzzle_proved :
  ~ (forall i,
      interp_S ex_temp_rises g0 i ->
      interp_S ex_ninety_rises g0 i).
Proof.
  intro H. specialize (H cm_idx).
  simpl in H. unfold the_den, Ninety_T, PN_to_T in H.
  apply cm_rigid_no. apply H.
  exists cm_concept. split; [exact cm_unique | exact cm_rises].
Qed.

(* 9. S14 ↔ S4 for simple cases:
      quantifying-in "every man, he₀ walks" = "every man walks" *)

Theorem s14_every_equiv_s4 : forall i,
  interp_S (E_S14 (E_every (E_CN i_man)) 0
                   (E_S4 (E_he 0) (E_IV i_walk))) g0 i <->
  interp_S ex_every_man_walks g0 i.
Proof.
  intros i. simpl.
  unfold every_den, He_n, assign_mod. simpl. reflexivity.
Qed.

(* 10. Assignment modification properties *)

Theorem assign_mod_lookup : forall g n x,
  (assign_mod g n x) n = x.
Proof.
  intros. unfold assign_mod. rewrite Nat.eqb_refl. reflexivity.
Qed.

Theorem assign_mod_other : forall g n m x,
  n <> m -> (assign_mod g n x) m = g m.
Proof.
  intros. unfold assign_mod.
  destruct (Nat.eqb_spec m n); [subst; contradiction | reflexivity].
Qed.

Theorem assign_mod_shadow : forall g n x y,
  assign_mod (assign_mod g n x) n y = assign_mod g n y.
Proof.
  intros. extensionality m. unfold assign_mod.
  destruct (m =? n); reflexivity.
Qed.
