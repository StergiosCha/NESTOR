(********************************************************************)
(*  dowty_roles.v  —  Dowty proto-roles + events on top of          *)
(*  MontagueFragment.MontagueExtensional                            *)
(********************************************************************)

From Coq Require Import Classical Decidable.
Require Import MontagueFragment.

(* Import the extensional fragment *)
Import MontagueFragment.MontagueExtensional.

(* ---------- Events & thematic relations ------------------------ *)
Parameter Event : Type.
Parameter AGENT   : Entity -> Event -> Prop.
Parameter PATIENT : Entity -> Event -> Prop.

(* Lexical root "open" ------------------------------------------- *)
Parameter open_ev : Event -> Prop.
Definition verb_open (x y : Entity) : Prop :=
  exists e, open_ev e /\ AGENT x e /\ PATIENT y e.

(* ---------- Dowty proto-features -------------------------------- *)
Parameter volitional sentient cause_change movement changed_state
         : Entity -> Event -> Prop.

Definition ProtoAgent_feats  x e :=
  volitional x e \/ sentient x e \/ cause_change x e \/ movement x e.

Definition ProtoPatient_feats x e :=
  changed_state x e \/ movement x e \/ (cause_change x e -> False).

(* Option 2: Axiomatic approach *)
Parameter score : (Entity -> Event -> Prop) -> Entity -> Event -> nat.

(* Axioms constraining the score function *)
Axiom score_true : forall F x e, F x e -> score F x e = 1.
Axiom score_false : forall F x e, ~ F x e -> score F x e = 0.
Axiom score_range : forall F x e, score F x e <= 1.

Axiom ASP :
  forall e x y,
    score ProtoAgent_feats x e > score ProtoAgent_feats y e ->
    AGENT x e /\ PATIENT y e.

(* ---------- Worked example -------------------------------------- *)
Section Example.
  Variables john door : Entity.  
  Variable e0 : Event.
  
  Hypothesis Hroot  : open_ev e0.
  Hypothesis Hroles : AGENT john e0 /\ PATIENT door e0.
  
  Definition john_opened_door : Prop := verb_open john door.
  
  Lemma sentence_true : john_opened_door.
  Proof. 
    unfold john_opened_door, verb_open. 
    exists e0.
    exact (conj Hroot Hroles).
  Qed.
End Example.
