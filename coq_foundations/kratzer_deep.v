(************************************************************************)
(*  kratzer_deep.v — Kratzer-Montague equivalence in the deep embedding  *)
(*                                                                       *)
(*  Self-contained. Defines a minimal deep IL for the modal fragment,    *)
(*  extends it with Kratzer's operators, and proves the equivalence.     *)
(*                                                                       *)
(*  Uses the convoy pattern for eval with @-prefixed constructor         *)
(*  patterns so all indices are explicit in the match.                   *)
(************************************************************************)

Require Import List.
Import ListNotations.
Require Import Classical.
Require Import Classical_Prop.

Set Implicit Arguments.

(* ================================================================== *)
(* PART 0: SEMANTIC DOMAINS                                            *)
(* ================================================================== *)

Parameter Entity : Type.
Parameter World  : Type.
Parameter Index  : Type.
Parameter world_of : Index -> World.

Definition t := Index -> Prop.

Definition ModalBase := list t.
Definition ConversationalBackground := World -> ModalBase.

Definition kratzer_accessibility (f : ConversationalBackground) :
  Index -> Index -> Prop :=
  fun i j => forall q, In q (f (world_of i)) -> q j.

(* ================================================================== *)
(* PART 1: IL TYPES AND DENOTATION DOMAINS                            *)
(* ================================================================== *)

Inductive ILType : Type :=
  | ty_e : ILType
  | ty_t : ILType
  | ty_arrow : ILType -> ILType -> ILType
  | ty_s : ILType -> ILType.

Fixpoint Den (τ : ILType) : Type :=
  match τ with
  | ty_e         => Entity
  | ty_t         => Prop
  | ty_arrow a b => Den a -> Den b
  | ty_s a       => Index -> Den a
  end.

(* ================================================================== *)
(* PART 2: IL EXPRESSIONS                                              *)
(* ================================================================== *)

Definition Ctx := list ILType.

Inductive IL : Ctx -> ILType -> Type :=
  | var_z : forall Γ τ, IL (τ :: Γ) τ
  | var_s : forall Γ τ σ, IL Γ τ -> IL (σ :: Γ) τ
  | lam : forall Γ σ τ, IL (σ :: Γ) τ -> IL Γ (ty_arrow σ τ)
  | app : forall Γ σ τ, IL Γ (ty_arrow σ τ) -> IL Γ σ -> IL Γ τ
  | not_ : forall Γ, IL Γ ty_t -> IL Γ ty_t
  | and_ : forall Γ, IL Γ ty_t -> IL Γ ty_t -> IL Γ ty_t
  | or_  : forall Γ, IL Γ ty_t -> IL Γ ty_t -> IL Γ ty_t
  | imp_ : forall Γ, IL Γ ty_t -> IL Γ ty_t -> IL Γ ty_t
  | forall_ : forall Γ σ, IL (σ :: Γ) ty_t -> IL Γ ty_t
  | exists_ : forall Γ σ, IL (σ :: Γ) ty_t -> IL Γ ty_t
  | up   : forall Γ τ, IL Γ τ -> IL Γ (ty_s τ)
  | down : forall Γ τ, IL Γ (ty_s τ) -> IL Γ τ
  | nec_ : forall Γ, IL Γ ty_t -> IL Γ ty_t
  | box_R_ : forall Γ,
      (Index -> Index -> Prop) -> IL Γ ty_t -> IL Γ ty_t
  | kratzer_must_ : forall Γ,
      ConversationalBackground -> IL Γ ty_t -> IL Γ ty_t
  | kratzer_can_ : forall Γ,
      ConversationalBackground -> IL Γ ty_t -> IL Γ ty_t
  .

(* ================================================================== *)
(* PART 3: ENVIRONMENTS                                                *)
(* ================================================================== *)

Fixpoint Env (Γ : Ctx) : Type :=
  match Γ with
  | nil     => unit
  | τ :: Γ' => (Den τ * Env Γ')%type
  end.

Definition env_head {τ Γ} (env : Env (τ :: Γ)) : Den τ := fst env.
Definition env_tail {τ Γ} (env : Env (τ :: Γ)) : Env Γ := snd env.
Definition env_cons {τ Γ} (v : Den τ) (env : Env Γ) : Env (τ :: Γ) := (v, env).

(* ================================================================== *)
(* PART 4: INTERPRETATION                                              *)
(*                                                                      *)
(* Convoy pattern: match returns Env Γ' -> Index -> Den τ' so that     *)
(* env and i get properly typed in each branch. @ in patterns makes    *)
(* all constructor arguments explicit.                                  *)
(* ================================================================== *)

Fixpoint eval {Γ τ} (e : IL Γ τ) : Env Γ -> Index -> Den τ :=
  match e in IL Γ' τ' return Env Γ' -> Index -> Den τ' with

  | @var_z Γ' τ'            => fun env _ =>
      env_head env

  | @var_s Γ' τ' σ' e'      => fun env i =>
      eval e' (env_tail env) i

  | @lam Γ' σ' τ' body      => fun env i =>
      fun (v : Den σ') => eval body (env_cons v env) i

  | @app Γ' σ' τ' f arg     => fun env i =>
      (eval f env i) (eval arg env i)

  | @not_ Γ' φ              => fun env i =>
      ~ (eval φ env i)

  | @and_ Γ' φ ψ            => fun env i =>
      eval φ env i /\ eval ψ env i

  | @or_ Γ' φ ψ             => fun env i =>
      eval φ env i \/ eval ψ env i

  | @imp_ Γ' φ ψ            => fun env i =>
      eval φ env i -> eval ψ env i

  | @forall_ Γ' σ' body     => fun env i =>
      forall (v : Den σ'), eval body (env_cons v env) i

  | @exists_ Γ' σ' body     => fun env i =>
      exists (v : Den σ'), eval body (env_cons v env) i

  | @up Γ' τ' α             => fun env _ =>
      fun i' => eval α env i'

  | @down Γ' τ' α           => fun env i =>
      (eval α env i) i

  | @nec_ Γ' φ              => fun env _ =>
      forall i', eval φ env i'

  | @box_R_ Γ' R φ          => fun env i =>
      forall j, R i j -> eval φ env j

  | @kratzer_must_ Γ' f φ   => fun env i =>
      forall j,
        (forall q, In q (f (world_of i)) -> q j) ->
        eval φ env j

  | @kratzer_can_ Γ' f φ    => fun env i =>
      exists j,
        (forall q, In q (f (world_of i)) -> q j) /\
        eval φ env j
  end.

(* ================================================================== *)
(* PART 5: CLOSED EXPRESSIONS                                          *)
(* ================================================================== *)

Definition ILClosed := IL nil.

Definition eval_closed {τ} (e : ILClosed τ) (i : Index) : Den τ :=
  eval e tt i.

(* ================================================================== *)
(* PART 6: THE KRATZER-MONTAGUE EQUIVALENCE                            *)
(* ================================================================== *)

Theorem deep_kratzer_equals_montague :
  forall Γ (φ : IL Γ ty_t) (f : ConversationalBackground)
         (env : Env Γ) (i : Index),
    eval (kratzer_must_ f φ) env i <->
    eval (box_R_ (kratzer_accessibility f) φ) env i.
Proof.
  intros.
  simpl.
  unfold kratzer_accessibility.
  reflexivity.
Qed.

(* ================================================================== *)
(* PART 7: S5 IS NOT DEFINITIONALLY A SPECIAL CASE                    *)
(* ================================================================== *)

Theorem nec_equiv_box_total :
  forall Γ (φ : IL Γ ty_t) (env : Env Γ) (i : Index),
    eval (nec_ φ) env i <->
    eval (box_R_ (fun _ _ => True) φ) env i.
Proof.
  intros. simpl. split.
  - intros H j _. apply H.
  - intros H j. apply H. exact I.
Qed.

(* ================================================================== *)
(* PART 8: DUALITY (still requires classical logic)                    *)
(* ================================================================== *)

Theorem deep_kratzer_duality :
  forall Γ (φ : IL Γ ty_t) (f : ConversationalBackground)
         (env : Env Γ) (i : Index),
    eval (kratzer_must_ f φ) env i <->
    ~ eval (kratzer_can_ f (not_ φ)) env i.
Proof.
  intros. simpl. split; intro H.
  - intro Hcan.
    destruct Hcan as [j [Hbase Hnp]].
    apply Hnp. apply H. exact Hbase.
  - intros j Hbase.
    destruct (classic (eval φ env j)) as [Hp | Hnp];
      [exact Hp |].
    exfalso. apply H.
    exists j. split; [exact Hbase | exact Hnp].
Qed.

(* ================================================================== *)
(* PART 9: AXIOM K AND MONOTONICITY                                    *)
(* ================================================================== *)

Theorem deep_kratzer_axiom_K :
  forall Γ (p q : IL Γ ty_t) (f : ConversationalBackground)
         (env : Env Γ) (i : Index),
    eval (kratzer_must_ f (imp_ p q)) env i ->
    eval (kratzer_must_ f p) env i ->
    eval (kratzer_must_ f q) env i.
Proof.
  intros. simpl in *.
  intros j Hbase.
  apply H; [exact Hbase | apply H0; exact Hbase].
Qed.

Theorem deep_kratzer_monotonic :
  forall Γ (p q : IL Γ ty_t) (f : ConversationalBackground)
         (env : Env Γ) (i : Index),
    (forall j, eval p env j -> eval q env j) ->
    eval (kratzer_must_ f p) env i ->
    eval (kratzer_must_ f q) env i.
Proof.
  intros. simpl in *.
  intros j Hbase.
  apply H. apply H0. exact Hbase.
Qed.

(* ================================================================== *)
(* PART 10: INTENSION/EXTENSION IDENTITY                               *)
(* ================================================================== *)

Theorem up_down_identity :
  forall Γ τ (e : IL Γ τ) (env : Env Γ) (i : Index),
    eval (down (up e)) env i = eval e env i.
Proof.
  intros. simpl. reflexivity.
Qed.
