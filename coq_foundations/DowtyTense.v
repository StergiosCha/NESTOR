(************************************************************************)
(*  DowtyTense.v                                                        *)
(*  ───────────────────────────────────────────────────────────────────  *)
(*  Adds a time line and tense semantics to DowtyLexical.               *)
(************************************************************************)
From Coq Require Import Lia Classical.
Require Import MontagueFragment.

(* Import both the extensional fragment and the lexical module *)
Import MontagueFragment.MontagueExtensional.

(* Assume DowtyLexical definitions are available *)
Parameter Event : Type.
Parameter AGENT PATIENT : Entity -> Event -> Prop.
Parameter open_ev : Event -> Prop.
Parameter volitional sentient cause_change movement changed_state
         : Entity -> Event -> Prop.

Definition verb_open (x y : Entity) : Prop :=
  exists e, open_ev e /\ AGENT x e /\ PATIENT y e.

(* -------------------------------------------------------------- *)
(* 1.  A linear Time type                                         *)
(* -------------------------------------------------------------- *)
Parameter Time : Type.
Parameter lt   : Time -> Time -> Prop.         (* strict order *)
Axiom lt_trans : forall t1 t2 t3, lt t1 t2 -> lt t2 t3 -> lt t1 t3.
Axiom lt_irrefl: forall t, ~ lt t t.
Axiom lt_total : forall t1 t2, t1 <> t2 -> lt t1 t2 \/ lt t2 t1.

(* -------------------------------------------------------------- *)
(* 2.  Events carry a time stamp                                  *)
(* -------------------------------------------------------------- *)
Parameter time_of : Event -> Time.

(* -------------------------------------------------------------- *)
(* 3.  Semantic types with an evaluation index                    *)
(*     index ι = (world , speaking-time ts)                       *)
(* -------------------------------------------------------------- *)
Parameter World : Type.
Definition Index := (World * Time)%type.
Definition world_of (ι : Index) := fst ι.
Definition speech_time (ι : Index) := snd ι.

(* intensional lift with access to index *)
Definition I (A : Type) := Index -> A.
Definition t := I Prop.

(* For simplicity we assume the event semantics itself is still   *
*  extensional.  Tense will relate index-time to event-time.       *)

(* -------------------------------------------------------------- *)
(* 4.  Tense operators, à la Dowty                                *)
(*     • PST φ : event time < speech time                         *)
(*     • PRS φ : event time = speech time                         *)
(*     • FUT φ : speech time < event time                         *)
(* -------------------------------------------------------------- *)

(* Fixed: The VP should be a relation between Entity and Event *)
Definition PST (VP : Entity -> Event -> Prop) (x : Entity) : t :=
  fun ι =>
    exists e, VP x e /\
      lt (time_of e) (speech_time ι).

Definition PRS (VP : Entity -> Event -> Prop) (x : Entity) : t :=
  fun ι =>
    exists e, VP x e /\
      time_of e = speech_time ι.

Definition FUT (VP : Entity -> Event -> Prop) (x : Entity) : t :=
  fun ι =>
    exists e, VP x e /\
      lt (speech_time ι) (time_of e).

(* -------------------------------------------------------------- *)
(* 5.  Example: "John opened the door" in the PAST                *)
(* -------------------------------------------------------------- *)
Section Example.
  Variables john door : Entity.
  Variable e0 : Event.
  Variable t0 : Time.
  Variable w0 : World.
  
  Hypothesis Hopen   : open_ev e0.
  Hypothesis Hroles  : AGENT john e0 /\ PATIENT door e0.
  (* Assume the event happened at time t0                         *)
  Hypothesis Hevent_time : time_of e0 = t0.
  
  (* Build a VP relation that includes the specific event         *)
  Definition VP_open_door (x : Entity) (e : Event) : Prop := 
    verb_open x door /\ e = e0.
  
  (* The intensional sentence                                     *)
  Definition sent (ι : Index) : Prop :=
    PST VP_open_door john ι.
  
  (* It is true in index (w0 , S) provided S is after t0           *)
  Lemma sentence_true_past :
    forall S, lt t0 S -> sent (w0 , S).
  Proof.
    intros S Hlt. 
    unfold sent, PST, VP_open_door.
    exists e0. 
    simpl. 
    rewrite Hevent_time.
    split.
    - split.
      + unfold verb_open. 
        exists e0.
        exact (conj Hopen Hroles).
      + reflexivity.
    - exact Hlt.
  Qed.
End Example.
