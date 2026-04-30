(************************************************************************)
(*  Aspect.v — Progressive & Perfect for the Dowty-Tense layer          *)
(************************************************************************)
From Coq Require Import Classical Lia.
Require Import MontagueFragment.

(* Import the extensional fragment *)
Import MontagueFragment.MontagueExtensional.

(* Import definitions from previous modules *)
Parameter Event : Type.
Parameter AGENT PATIENT : Entity -> Event -> Prop.
Parameter open_ev : Event -> Prop.

Parameter Time : Type.
Parameter lt   : Time -> Time -> Prop.
Axiom lt_trans : forall t1 t2 t3, lt t1 t2 -> lt t2 t3 -> lt t1 t3.
Axiom lt_irrefl: forall t, ~ lt t t.
Axiom lt_total : forall t1 t2, t1 <> t2 -> lt t1 t2 \/ lt t2 t1.

Parameter time_of : Event -> Time.

Parameter World : Type.
Definition Index := (World * Time)%type.
Definition world_of (ι : Index) := fst ι.
Definition speech_time (ι : Index) := snd ι.

Definition I (A : Type) := Index -> A.
Definition t := I Prop.

(* -------------------------------------------------------------- *)
(* 1.  Event mereology & culmination                              *)
(* -------------------------------------------------------------- *)
Parameter subevent   : Event -> Event -> Prop.  (* e₁ ⊑ e₂ *)
Axiom subevent_refl  : forall e, subevent e e.
Axiom subevent_trans : forall e1 e2 e3,
    subevent e1 e2 -> subevent e2 e3 -> subevent e1 e3.

(* Culmination relation                                           *)
Parameter culminates : Event -> Event -> Prop.  (* e_pre  ⇝  e_culminated *)
Parameter result_state : Event -> Prop.
Axiom culminates_sub : forall e1 e2, culminates e1 e2 -> subevent e1 e2.

(* -------------------------------------------------------------- *)
(* 2.  Aspect operators                                           *)
(* -------------------------------------------------------------- *)
Definition PROG (VP : Entity -> Event -> Prop) (x : Entity) : t :=
  fun ι =>
    exists e_prog e_full,
        VP x e_full
    /\  subevent e_prog e_full
    /\  ~ culminates e_prog e_full        (* still in progress *)
    /\  time_of e_prog = speech_time ι.

Definition PERF (VP : Entity -> Event -> Prop) (x : Entity) : t :=
  fun ι =>
    exists e, VP x e
          /\ result_state e               (* culminated event *)
          /\ lt (time_of e) (speech_time ι).

(* -------------------------------------------------------------- *)
(* 3.  Example: "John is opening the door."                       *)
(* -------------------------------------------------------------- *)
Section ProgressiveExample.
  Variables john door : Entity.
  Variable e_prog e_full : Event.
  Variable w0 : World.
  Variable S  : Time.
  
  Hypothesis Event_full : open_ev e_full /\ AGENT john e_full /\ PATIENT door e_full.
  Hypothesis Prog_part : subevent e_prog e_full /\ ~ culminates e_prog e_full /\ time_of e_prog = S.
  
  Definition VP_open (x y : Entity) (e:Event) : Prop :=
    open_ev e /\ AGENT x e /\ PATIENT y e.
  
  Definition sent :=
    PROG (fun x e => VP_open x door e) john.
  
  Lemma prog_sentence_true : sent (w0 , S).
  Proof.
    unfold sent, PROG.
    destruct Event_full as [Hopen [Hag Hpat]].
    destruct Prog_part as [Hsub [Hnotculm Htime]].
    exists e_prog, e_full.
    split.
    - unfold VP_open. exact (conj Hopen (conj Hag Hpat)).
    - split; [exact Hsub | split; [exact Hnotculm | simpl; exact Htime]].
  Qed.
End ProgressiveExample.

