(**  Champollion‑style choice–function operators on top of
     the set‑theoretic fragment in Set_theoretic_Defs
     ===================================================== *)

Require Import Set_theoretic_Defs.

Set Implicit Arguments.

(* ------------------------------------------------------------- *)
(* 1 · Choice functions and well‑formedness                       *)
(* ------------------------------------------------------------- *)

Definition choiceF : Type := (e -> Prop) -> e.

Definition CF (f : choiceF) : Prop :=
  forall (N : e -> Prop), (exists x, N x) -> N (f N).

(* ------------------------------------------------------------- *)
(* 2 · A tiny universe of indices for CR                          *)
(* ------------------------------------------------------------- *)

Inductive idx : Type := i1 | i2 | i3.

Parameter g : idx -> choiceF.

(* ------------------------------------------------------------- *)
(* 3 · Choice‑Raising  CR  (Champollion 45)                       *)
(* ------------------------------------------------------------- *)

Definition CR (i : idx) (N : e -> Prop) (P : e -> Prop) : Prop :=
  P (g i N).
Notation "⟦ N ⟧ᶜ i" := (CR i N) (at level 40).

(* ------------------------------------------------------------- *)
(* 4 · Intersective ‘and’ (INT)                                   *)
(* ------------------------------------------------------------- *)

Definition INT (Q R : (e -> Prop) -> Prop) (X : e -> Prop) : Prop :=
  Q X /\ R X.

Notation "Q ∧̂ R" := (INT Q R) (at level 40).

(* ------------------------------------------------------------- *)
(* 5 · MIN – reused verbatim                                      *)
(* ------------------------------------------------------------- *)

Definition MIN (Q : (e->Prop)->Prop) : (e->Prop)->Prop :=
  fun P => Q P /\ forall P', strict_included P' P -> ~Q P'.

(* ------------------------------------------------------------- *)
(* 6 · Choice‑Closure CC (∃f CF f ∧ A f P)                        *)
(*     Inductive to enable structural proofs                      *)
(* ------------------------------------------------------------- *)

Inductive CC (A : choiceF -> (e->Prop)->Prop) : (e->Prop)->Prop :=
| cc_intro : forall f P, CF f -> A f P -> CC A P.

(* convenience destruct lemma *)
Lemma CC_destruct :
  forall A P, CC A P -> exists f, CF f /\ A f P.
Proof. intros A P [f P' Hcf Ha]; exists f; auto. Qed.

(* ------------------------------------------------------------- *)
(* 7 · Example predicates                                          *)
(* ------------------------------------------------------------- *)

Parameter man woman : e -> Prop.
Parameter date      : e -> Prop.

Definition Man   := fun x => man x.
Definition Woman := fun x => woman x.

(* ER as in user code *)
Definition ER (P Q : e -> Prop) : Prop := exists x, In_s (intersection P Q) x.

(* ------------------------------------------------------------- *)
(* 8 · Build the NP  MIN (⟦Man⟧ ∧̂ ⟦Woman⟧)                        *)
(* ------------------------------------------------------------- *)

Definition NP_pair : (e->Prop)->Prop :=
  MIN ((CR i1 Man) ∧̂ (CR i2 Woman)).

(* ------------------------------------------------------------- *)
(* 9 · Evaluate the user’s term                                   *)
(* ------------------------------------------------------------- *)

Definition a (P : (e->Prop)->Prop) (Q : (e->Prop)->Prop) : Prop :=
  exists X, P X /\ Q X.

Definition dated (P : e -> Prop) : Prop := exists z, date z.

Eval cbv beta delta [a MIN CR INT NP_pair Man Woman dated] in
    (a NP_pair dated).

(* ------------------------------------------------------------- *)
(* 10 · PDIST & have_a_beer example                               *)
(* ------------------------------------------------------------- *)

Parameter beer : e -> Prop.
Parameter have : e -> e -> Prop.

Definition have_a_beer (x : e) : Prop :=
  exists y, beer y /\ have x y.

Definition PDIST (P' P : e -> Prop) : Prop :=
  ~Empty_set P /\ included P P'.

Eval cbv beta delta [a MIN CR INT NP_pair Man Woman PDIST have_a_beer] in
    (a NP_pair (PDIST have_a_beer)).
