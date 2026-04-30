Require Import Coq.Sets.Ensembles.

Module LinkPlurals.

  Parameter Entity : Type.

  Parameter sum : Entity -> Entity -> Entity.
  
  Parameter part_of : Entity -> Entity -> Prop.
  
  Infix "⊕" := sum (at level 50).
  Infix "≤" := part_of (at level 70).

  Axiom sum_assoc : forall x y z, x ⊕ (y ⊕ z) = (x ⊕ y) ⊕ z.
  Axiom sum_comm  : forall x y, x ⊕ y = y ⊕ x.
  Axiom sum_idem  : forall x, x ⊕ x = x.
  
  Axiom part_of_def : forall x y, x ≤ y <-> x ⊕ y = y.

  Theorem part_of_refl : forall x, x ≤ x.
  Proof.
    intro x. apply part_of_def. apply sum_idem.
  Qed.

  Theorem part_of_trans : forall x y z, x ≤ y -> y ≤ z -> x ≤ z.
  Proof.
    intros x y z Hxy Hyz.
    apply part_of_def in Hxy.
    apply part_of_def in Hyz.
    apply part_of_def.
    rewrite <- Hyz.       
    rewrite sum_assoc.   
    rewrite Hxy.         
    rewrite Hyz.          
    reflexivity.
  Qed.

  Definition Atom (x : Entity) : Prop :=
    forall y, y ≤ x -> y = x.

  Definition Singular (x : Entity) : Prop := Atom x.
  
  Definition Plural (x : Entity) : Prop := ~ Atom x.

  Parameter john mary : Entity.
  Axiom john_atom : Atom john.
  Axiom mary_atom : Atom mary.
  Axiom distinct_jm : john <> mary.

  Definition john_and_mary : Entity := john ⊕ mary.

  Theorem john_in_plural : john ≤ john_and_mary.
  Proof.
    apply part_of_def.
    unfold john_and_mary.
    rewrite sum_assoc.
    rewrite sum_idem.
    reflexivity.
  Qed.

  Theorem jm_is_plural : Plural john_and_mary.
  Proof.
    unfold Plural, Atom, john_and_mary.
    intro H_atom.
    assert (john = john ⊕ mary) as H_eq.
    { apply H_atom. apply john_in_plural. }
    assert (mary ≤ john).
    { apply part_of_def. rewrite sum_comm. symmetry. apply H_eq. }
    apply john_atom in H.
    symmetry in H.
    apply distinct_jm.
    apply H.
  Qed.

  Inductive Star (P : Entity -> Prop) : Entity -> Prop :=
  | star_base : forall x, P x -> Star P x
  | star_sum  : forall x y, Star P x -> Star P y -> Star P (x ⊕ y).

  Parameter Boy : Entity -> Prop.

  Definition PluralBoys := Star Boy.

  Definition Distributive (VP : Entity -> Prop) : Prop :=
    forall x, VP x -> forall y, (Atom y /\ y ≤ x) -> VP y.

  Parameter sleep : Entity -> Prop.
  Axiom sleep_dist : Distributive sleep.

  Theorem dist_inference : 
    sleep john_and_mary -> sleep john.
  Proof.
    intro H_sleep.
    apply sleep_dist with (x := john_and_mary).
    - apply H_sleep.
    - split.
      + apply john_atom.
      + apply john_in_plural.
  Qed.

  Parameter gather : Entity -> Prop.

End LinkPlurals.
