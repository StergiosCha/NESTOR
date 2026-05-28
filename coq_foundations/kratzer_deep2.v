(************************************************************************)
(*  kratzer_deep2.v — Kratzer-Montague equivalence on top of PTQ_deep2  *)
(*                                                                       *)
(*  Imports the deep IL from PTQ_deep2.v and defines Kratzer's modal     *)
(*  operators as SEMANTIC functions on IL denotations. This avoids       *)
(*  extending the IL GADT while still proving all the key theorems.     *)
(*                                                                       *)
(*  The Kratzer operators are shallow (Coq-level), but they operate on  *)
(*  denotations of deep IL expressions via eval_closed.                 *)
(************************************************************************)

Require Import PTQ_deep2.
Require Import List.
Import ListNotations.
Require Import Classical.
Require Import Classical_Prop.

Set Implicit Arguments.

(* ================================================================== *)
(* PART 1: MODAL BASES AND CONVERSATIONAL BACKGROUNDS                  *)
(* ================================================================== *)

(** A proposition in the Kratzer sense: truth at each index **)
Definition Prop_i := Index -> Prop.

(** A modal base is a set of propositions (represented as a list) **)
Definition ModalBase := list Prop_i.

(** A conversational background assigns a modal base to each world **)
Definition ConversationalBackground := World -> ModalBase.

(** Kratzer accessibility: j is accessible from i iff j satisfies
    every proposition in the modal base at world_of(i) **)
Definition kratzer_accessibility (f : ConversationalBackground) :
  Index -> Index -> Prop :=
  fun i j => forall q, In q (f (world_of i)) -> q j.

(* ================================================================== *)
(* PART 2: KRATZER OPERATORS (semantic level)                          *)
(* ================================================================== *)

(** Relativized box: ∀j. R(i,j) → p(j) **)
Definition box_R (R : Index -> Index -> Prop)
  (p : Index -> Prop) (i : Index) : Prop :=
  forall j, R i j -> p j.

(** Kratzer's must: universal quantification over accessible worlds **)
Definition kratzer_must (f : ConversationalBackground)
  (p : Index -> Prop) (i : Index) : Prop :=
  forall j, kratzer_accessibility f i j -> p j.

(** Kratzer's can: existential quantification over accessible worlds **)
Definition kratzer_can (f : ConversationalBackground)
  (p : Index -> Prop) (i : Index) : Prop :=
  exists j, kratzer_accessibility f i j /\ p j.

(* ================================================================== *)
(* PART 3: THE KRATZER-MONTAGUE EQUIVALENCE                            *)
(* ================================================================== *)

(** kratzer_must is definitionally equal to box_R with
    kratzer_accessibility **)
Theorem kratzer_equals_montague :
  forall (φ : ILClosed ty_t) (f : ConversationalBackground)
         (i : Index),
    kratzer_must f (eval_closed φ) i <->
    box_R (kratzer_accessibility f) (eval_closed φ) i.
Proof.
  intros. unfold kratzer_must, box_R. reflexivity.
Qed.

(* ================================================================== *)
(* PART 4: nec_ AS A SPECIAL CASE                                     *)
(* ================================================================== *)

(** deep2's □ (nec_) is the world-relativised box at fixed time **)
Theorem nec_equiv_box_worlds :
  forall (φ : ILClosed ty_t) (i : Index),
    eval_closed (nec_ φ) i <->
    forall w', eval_closed φ (w', time_of i).
Proof.
  intros. unfold eval_closed. simpl. reflexivity.
Qed.

(** Corollary: if the conversational background is trivially
    permissive (empty modal base), kratzer_must implies nec_.
    The converse fails: kratzer_must with empty base ranges over
    all indices, whereas nec_ only ranges over worlds at the
    current time. **)
Theorem kratzer_must_total_implies_nec :
  forall (f : ConversationalBackground) (φ : ILClosed ty_t)
         (i : Index),
    (forall w, f w = nil) ->
    kratzer_must f (eval_closed φ) i ->
    eval_closed (nec_ φ) i.
Proof.
  intros f φ i Hnil H. unfold kratzer_must, kratzer_accessibility,
    eval_closed in *. simpl in *.
  intros w'. apply (H (w', time_of i)). intros q Hq.
  rewrite Hnil in Hq. inversion Hq.
Qed.

(* ================================================================== *)
(* PART 5: DUALITY (requires classical logic)                          *)
(* ================================================================== *)

(** must φ ↔ ¬ can (¬φ) **)
Theorem kratzer_duality :
  forall (φ : ILClosed ty_t) (f : ConversationalBackground)
         (i : Index),
    kratzer_must f (eval_closed φ) i <->
    ~ kratzer_can f (fun j => ~ eval_closed φ j) i.
Proof.
  intros. unfold kratzer_must, kratzer_can, kratzer_accessibility.
  split; intro H.
  - intro Hcan.
    destruct Hcan as [j [Hbase Hnp]].
    apply Hnp. apply H. exact Hbase.
  - intros j Hbase.
    destruct (classic (eval_closed φ j)) as [Hp | Hnp];
      [exact Hp |].
    exfalso. apply H.
    exists j. split; [exact Hbase | exact Hnp].
Qed.

(** Duality via deep2's not_ constructor **)
Theorem kratzer_duality_deep :
  forall (φ : ILClosed ty_t) (f : ConversationalBackground)
         (i : Index),
    kratzer_must f (eval_closed φ) i <->
    ~ kratzer_can f (eval_closed (not_ φ)) i.
Proof.
  intros. unfold kratzer_must, kratzer_can, kratzer_accessibility,
    eval_closed. simpl. split; intro H.
  - intro Hcan.
    destruct Hcan as [j [Hbase Hnp]].
    apply Hnp. apply H. exact Hbase.
  - intros j Hbase.
    destruct (classic (eval (not_ φ) tt j)) as [Hnp | Hnnp].
    + exfalso. apply H.
      exists j. split; [exact Hbase | exact Hnp].
    + simpl in Hnnp.
      destruct (classic (eval φ tt j)) as [Hp | Hn];
        [exact Hp |].
      exfalso. apply Hnnp. exact Hn.
Qed.

(* ================================================================== *)
(* PART 6: AXIOM K AND MONOTONICITY                                    *)
(* ================================================================== *)

(** Axiom K: must(p → q) → must(p) → must(q) **)
Theorem kratzer_axiom_K :
  forall (p q : ILClosed ty_t) (f : ConversationalBackground)
         (i : Index),
    kratzer_must f (fun j => eval_closed p j -> eval_closed q j) i ->
    kratzer_must f (eval_closed p) i ->
    kratzer_must f (eval_closed q) i.
Proof.
  intros. unfold kratzer_must, kratzer_accessibility in *.
  intros j Hbase.
  apply H; [exact Hbase | apply H0; exact Hbase].
Qed.

(** Axiom K via deep2's imp_ constructor **)
Theorem kratzer_axiom_K_deep :
  forall (p q : ILClosed ty_t) (f : ConversationalBackground)
         (i : Index),
    kratzer_must f (eval_closed (imp_ p q)) i ->
    kratzer_must f (eval_closed p) i ->
    kratzer_must f (eval_closed q) i.
Proof.
  intros. unfold kratzer_must, kratzer_accessibility, eval_closed in *.
  simpl in *.
  intros j Hbase.
  apply H; [exact Hbase | apply H0; exact Hbase].
Qed.

(** Monotonicity: if p entails q, then must(p) entails must(q) **)
Theorem kratzer_monotonic :
  forall (p q : ILClosed ty_t) (f : ConversationalBackground)
         (i : Index),
    (forall j, eval_closed p j -> eval_closed q j) ->
    kratzer_must f (eval_closed p) i ->
    kratzer_must f (eval_closed q) i.
Proof.
  intros. unfold kratzer_must, kratzer_accessibility in *.
  intros j Hbase.
  apply H. apply H0. exact Hbase.
Qed.

(* ================================================================== *)
(* PART 7: S5 AXIOMS FOR nec_ (via deep2's □)                         *)
(* ================================================================== *)

(** T axiom: □φ → φ  (already in deep2 as nec_T in theorems file,
    but we re-prove it here for completeness) **)
Theorem nec_T :
  forall (φ : ILClosed ty_t) (i : Index),
    eval_closed (nec_ φ) i -> eval_closed φ i.
Proof.
  intros φ [w t] H. unfold eval_closed in *. simpl in *. apply H.
Qed.

(** 4 axiom: □φ → □□φ **)
Theorem nec_4 :
  forall (φ : ILClosed ty_t) (i : Index),
    eval_closed (nec_ φ) i -> eval_closed (nec_ (nec_ φ)) i.
Proof.
  intros φ i H. unfold eval_closed in *. simpl in *. intros w' w''. apply H.
Qed.

(** 5 axiom: ¬□φ → □¬□φ  (or equivalently ◇φ → □◇φ) **)
Theorem nec_5 :
  forall (φ : ILClosed ty_t) (i : Index),
    ~ eval_closed (nec_ φ) i ->
    eval_closed (nec_ (not_ (nec_ φ))) i.
Proof.
  intros φ i Hnnec. unfold eval_closed in *. simpl in *.
  intros w' Hnec. apply Hnnec. exact Hnec.
Qed.

(* ================================================================== *)
(* PART 8: EXAMPLES WITH DEEP IL EXPRESSIONS                          *)
(* ================================================================== *)

(** "Every man must walk" under conversational background f:
    kratzer_must f (eval_closed il_every_man_walks_c) **)
Theorem every_man_kratzer_must_walk :
  forall (f : ConversationalBackground) (i : Index),
    kratzer_must f (eval_closed il_every_man_walks_c) i ->
    forall j, kratzer_accessibility f i j ->
      forall x, man_den x j -> walk_den x j.
Proof.
  intros f i Hmust j Hacc x Hman.
  unfold kratzer_must in Hmust.
  specialize (Hmust j Hacc).
  unfold eval_closed in Hmust. simpl in Hmust.
  apply Hmust. exact Hman.
Qed.

(** "Bill must walk" under f **)
Theorem bill_kratzer_must_walk :
  forall (f : ConversationalBackground) (i : Index),
    kratzer_must f (eval_closed il_bill_walks_c) i ->
    forall j, kratzer_accessibility f i j ->
      walk_den (fun _ => bill_e) j.
Proof.
  intros f i Hmust j Hacc.
  unfold kratzer_must in Hmust.
  specialize (Hmust j Hacc).
  unfold eval_closed, il_bill_walks_c in Hmust. simpl in Hmust.
  exact Hmust.
Qed.
