(************************************************************************)
(*  Montague-style semantics with abstract counting quantifiers         *)
(*  – extensional, intensional, and world-time fragments                *)
(*  – no list / NoDup definitions                                       *)
(************************************************************************)

From Coq Require Import Lia.
Set Implicit Arguments.

Module MontagueFragment.

(* ------------------------------------------------------------- *)
(* 0.  Generic counting interface                                *)
(* ------------------------------------------------------------- *)
Section AbstractCounting.
  Variable Entity : Type.
  Variable size   : (Entity -> Prop) -> nat.
  Axiom size_ext :
    forall A B : Entity -> Prop,
      (forall x, A x <-> B x) -> size A = size B.
  Axiom size_subset :
    forall A B : Entity -> Prop,
      (forall x, A x -> B x) -> size A <= size B.

  Definition G_some      N P := 1 <= size (fun x => N x /\ P x).
  Definition G_exactly_n n N P := size (fun x => N x /\ P x) = n.
  Definition G_at_least_n n N P := n <= size (fun x => N x /\ P x).
  Definition G_most      N P :=
    size (fun x => N x /\  P x) >
    size (fun x => N x /\ ~ P x).
End AbstractCounting.

(* ------------------------------------------------------------- *)
(* 1.  EXTENSIONAL fragment                                      *)
(* ------------------------------------------------------------- *)
Module MontagueExtensional.
  Parameter Entity : Type.
  Parameter size   : (Entity -> Prop) -> nat.
  Axiom size_ext    : forall A B, (forall x, A x <-> B x) -> size A = size B.
  Axiom size_subset : forall A B, (forall x, A x -> B x) -> size A <= size B.

  Definition g_some        := @G_some      Entity size.
  Definition g_exactly  n  := @G_exactly_n Entity size n.
  Definition g_at_least n  := @G_at_least_n Entity size n.
  Definition g_most        := @G_most      Entity size.

  Parameter john mary : Entity.
  Parameter Man Woman Dog : Entity -> Prop.
  Parameter loves       : Entity -> Entity -> Prop.

  Inductive NP :=
  | np_prop  : Entity -> NP
  | np_quant : ((Entity->Prop)->(Entity->Prop)->Prop) -> (Entity->Prop) -> NP.

  Inductive S := s_atom : Prop -> S.

  Definition interp_NP (n:NP) : (Entity->Prop)->Prop :=
    match n with
    | np_prop  e   => fun P => P e
    | np_quant q N => fun P => q N P
    end.

  Definition sentence (subj:NP) (vp:Entity->Prop) : S :=
    s_atom (interp_NP subj vp).

  (* classic logical determiners *)
Definition every (N P : Entity -> Prop) : Prop :=
  forall x : Entity, N x -> P x.

Definition some  (N P : Entity -> Prop) : Prop :=
  exists x : Entity, N x /\ P x.

Definition no    (N P : Entity -> Prop) : Prop :=
  ~ some N P.

  Definition loves_mary x := loves x mary.

  Definition most_dogs_love_mary : S :=
    sentence (np_quant g_most Dog) loves_mary.

  Definition at_least_two_women_love_mary : S :=
    sentence (np_quant (g_at_least 2) Woman) loves_mary.
End MontagueExtensional.

(* ------------------------------------------------------------- *)
(* 2.  INTENSIONAL fragment  (kept unchanged)                     *)
(* ------------------------------------------------------------- *)
Module MontagueIntensional.
  Parameter Entity : Type.
  Parameter World  : Type.
  Definition I (A:Type) := World -> A.  Definition t := I Prop.

  Parameter john mary : Entity.
  Parameter Man Woman Unicorn : Entity -> I Prop.
  Parameter loves : Entity -> Entity -> I Prop.
  Parameter seek  : (Entity -> I Prop) -> Entity -> I Prop.

(* inside Module MontagueIntensional *)

Definition every (N P : Entity -> I Prop) : t :=
  fun w => forall x : Entity, N x w -> P x w.

Definition some  (N P : Entity -> I Prop) : t :=
  fun w => exists x : Entity, N x w /\ P x w.

Definition no    (N P : Entity -> I Prop) : t :=
  fun w => ~ some N P w.

  Definition john_seeks_a_unicorn : t := seek Unicorn john.
End MontagueIntensional.

(* ------------------------------------------------------------- *)
(* 3.  WORLD-TIME + modality fragment (kept unchanged)            *)
(* ------------------------------------------------------------- *)
Module MontagueWorldTime.
  Parameter Entity World Time : Type.
  Definition Index := (World*Time)%type.
  Definition world_of i := @fst World Time i.
  Definition time_of  i := @snd World Time i.
  Definition I (A:Type) := Index -> A.  Definition t := I Prop.

  Parameter john mary : Entity. Parameter Dog : Entity -> I Prop.
  Parameter loves : Entity -> Entity -> I Prop.

  Parameter R : World -> World -> Prop.  Axiom R_refl : forall w, R w w.
(* inside MontagueWorldTime *)

Definition every (N P : Entity -> I Prop) : t :=
  fun i => forall x : Entity, N x i -> P x i.

Definition some  (N P : Entity -> I Prop) : t :=
  fun i => exists x : Entity, N x i /\ P x i.

Definition no    (N P : Entity -> I Prop) : t :=
  fun i => ~ some N P i.

  Definition box φ : t := fun i => forall w', R (world_of i) w' -> φ (w', time_of i).
End MontagueWorldTime.

End MontagueFragment.
