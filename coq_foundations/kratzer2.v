(************************************************************************)
(*  Clean Formalization of Kratzer's Modal System                        *)
(*  NO ADMITS - only provable theorems                                   *)
(************************************************************************)

From Coq Require Import List Classical_Prop FunctionalExtensionality.
Require Import MontagueFragment.
Set Implicit Arguments.

Module KratzerClean.

Import MontagueFragment.MontagueWorldTime.

(* ------------------------------------------------------------- *)
(* 1. KRATZER'S BASIC SYSTEM                                    *)
(* ------------------------------------------------------------- *)

(* Modal bases: finite lists of propositions *)
Definition ModalBase := list t.

(* Conversational backgrounds: map worlds to modal bases *)
Definition ConversationalBackground := World -> ModalBase.

(* Logical consequence from finite modal base *)
Definition follows_from (base : ModalBase) (p : t) : Prop :=
  forall i, (forall q, In q base -> q i) -> p i.

(* Compatibility with finite modal base *)
Definition compatible_with (base : ModalBase) (p : t) : Prop :=
  exists i, (forall q, In q base -> q i) /\ p i.

(* Kratzer's modal operators *)
Definition kratzer_must (f : ConversationalBackground) (p : t) : t :=
  fun i => follows_from (f (world_of i)) p.

Definition kratzer_can (f : ConversationalBackground) (p : t) : t :=
  fun i => compatible_with (f (world_of i)) p.

(* ------------------------------------------------------------- *)
(* 2. CONNECTION TO MONTAGUE MODALS                             *)
(* ------------------------------------------------------------- *)

(* Kratzer's conversational backgrounds generate accessibility relations *)
Definition kratzer_accessibility (f : ConversationalBackground) : Index -> Index -> Prop :=
  fun i j => forall q, In q (f (world_of i)) -> q j.

(* ------------------------------------------------------------- *)
(* 3. PROVABLE THEOREMS                                         *)
(* ------------------------------------------------------------- *)

(* The fundamental equivalence *)
Theorem kratzer_equals_montague :
  forall f p i,
    kratzer_must f p i <-> 
    (forall j, kratzer_accessibility f i j -> p j).
Proof.
  intros f p i.
  unfold kratzer_must, follows_from, kratzer_accessibility.
  reflexivity.
Qed.

(* Duality between must and can *)
Theorem kratzer_duality :
  forall f p i,
    kratzer_must f p i <-> ~ kratzer_can f (fun j => ~ p j) i.
Proof.
  intros f p i.
  unfold kratzer_must, kratzer_can, follows_from, compatible_with.
  split; intro H.
  - intro Hcan. 
    destruct Hcan as [j [Hbase Hnp]].
    specialize (H j Hbase).
    contradiction.
  - intros j Hbase.
    destruct (classic (p j)) as [Hp | Hnp]; [exact Hp |].
    exfalso. apply H.
    exists j. split; [exact Hbase | exact Hnp].
Qed.

(* Kratzer modals validate modal logic axiom K *)
Theorem kratzer_axiom_K :
  forall f p q i,
    kratzer_must f (fun j => p j -> q j) i ->
    kratzer_must f p i ->
    kratzer_must f q i.
Proof.
  intros f p q i H1 H2.
  unfold kratzer_must, follows_from in *.
  intros j Hbase.
  apply H1; [exact Hbase | apply H2; exact Hbase].
Qed.

(* Monotonicity *)
Theorem kratzer_monotonic :
  forall f p q i,
    (forall j, p j -> q j) ->
    kratzer_must f p i ->
    kratzer_must f q i.
Proof.
  intros f p q i Hpq H.
  unfold kratzer_must, follows_from in *.
  intros j Hbase.
  apply Hpq, H, Hbase.
Qed.

(* Empty modal base *)
Theorem empty_base_characterization :
  forall p i,
    kratzer_must (fun _ => nil) p i ->
    forall j, p j.
Proof.
  intros p i H j.
  unfold kratzer_must, follows_from in H.
  apply H.
  intros q Hq.
  inversion Hq.
Qed.

(* ------------------------------------------------------------- *)
(* 4. EXAMPLES                                                  *)
(* ------------------------------------------------------------- *)

(* Example propositions *)
Parameter murder_is_crime theft_is_crime : t.
Parameter learn_ancestors children_obey : t.

(* Example conversational backgrounds *)
Definition legal_background : ConversationalBackground :=
  fun w => murder_is_crime :: theft_is_crime :: nil.

Definition tribal_background : ConversationalBackground :=
  fun w => learn_ancestors :: children_obey :: nil.

(* Example modal statements *)
Definition murder_must_be_crime : t :=
  kratzer_must legal_background murder_is_crime.

Definition children_must_learn : t :=
  kratzer_must tribal_background learn_ancestors.

(* ------------------------------------------------------------- *)
(* 5. KRATZER'S CONJUNCTION AMBIGUITY                           *)
(* ------------------------------------------------------------- *)

Parameter striding flying : t.

(* Two different ways to encode "Te Miti recommends striding and flying" *)

(* Reading 1: Single conjunctive recommendation *)
Definition conjunctive_recommendation : ModalBase := 
  (fun i => striding i /\ flying i) :: nil.

(* Reading 2: Two separate recommendations *)
Definition separate_recommendations : ModalBase := 
  striding :: flying :: nil.

(* These are genuinely different modal bases *)
Theorem readings_are_different :
  conjunctive_recommendation <> separate_recommendations.
Proof.
  unfold conjunctive_recommendation, separate_recommendations.
  intro H.
  inversion H.
Qed.

(* ------------------------------------------------------------- *)
(* 6. FIXING KRATZER'S INCONSISTENCY PROBLEM                    *)
(* ------------------------------------------------------------- *)

(* Simple consistency check *)
Definition consistent (base : ModalBase) : Prop :=
  exists i, forall p, In p base -> p i.

(* Maximal consistent subsets *)
Definition maximal_consistent_subset (base sub : ModalBase) : Prop :=
  incl sub base /\ 
  consistent sub /\
  forall sup, incl sub sup -> incl sup base -> consistent sup -> incl sup sub.

(* Fixed Kratzer operators that handle inconsistency *)
Definition kratzer_must_fixed (f : ConversationalBackground) (p : t) : t :=
  fun i => 
    let base := f (world_of i) in
    (consistent base -> follows_from base p) /\
    (~ consistent base -> forall sub, maximal_consistent_subset base sub -> follows_from sub p).

(* ------------------------------------------------------------- *)
(* 7. ADDITIONAL MISSING THEOREMS                               *)
(* ------------------------------------------------------------- *)

(* Necessitation rule *)
Theorem kratzer_necessitation :
  forall f p,
    (forall i, p i) ->
    forall i, kratzer_must f p i.
Proof.
  intros f p Hp i.
  unfold kratzer_must, follows_from.
  intros j Hbase.
  apply Hp.
Qed.

(* Distribution over implication *)
Theorem kratzer_distribution :
  forall f p q i,
    kratzer_must f (fun j => p j -> q j) i ->
    (kratzer_must f p i -> kratzer_must f q i).
Proof.
  intros f p q i H Hp.
  apply kratzer_axiom_K with p; assumption.
Qed.

(* Conjunction introduction *)
Theorem kratzer_conjunction_intro :
  forall f p q i,
    kratzer_must f p i ->
    kratzer_must f q i ->
    kratzer_must f (fun j => p j /\ q j) i.
Proof.
  intros f p q i Hp Hq.
  unfold kratzer_must, follows_from in *.
  intros j Hbase.
  split; [apply Hp | apply Hq]; exact Hbase.
Qed.

(* Can distributes over disjunction *)
Theorem kratzer_can_disjunction :
  forall f p q i,
    kratzer_can f (fun j => p j \/ q j) i ->
    kratzer_can f p i \/ kratzer_can f q i.
Proof.
  intros f p q i H.
  unfold kratzer_can, compatible_with in *.
  destruct H as [j [Hbase Hdisj]].
  destruct Hdisj as [Hp | Hq].
  - left. exists j. split; assumption.
  - right. exists j. split; assumption.
Qed.

(* ------------------------------------------------------------- *)
(* 8. ORDERING SOURCES (Kratzer's Later Work)                   *)
(* ------------------------------------------------------------- *)

(* Ordering sources for comparative modality *)
Definition OrderingSource := World -> ModalBase.

(* Comparative necessity using ordering sources *)
Definition better_worlds (g : OrderingSource) (i j : Index) : Prop :=
  forall p, In p (g (world_of i)) -> p j.

Definition kratzer_better (f : ConversationalBackground) (g : OrderingSource) (p : t) : t :=
  fun i =>
    forall j, kratzer_accessibility f i j ->
    forall k, kratzer_accessibility f i k ->
    better_worlds g i j -> better_worlds g i k ->
    (forall q, In q (g (world_of i)) -> q j -> q k -> p j -> p k) ->
    p j.

(* ------------------------------------------------------------- *)
(* 9. WHAT KRATZER PROMISES vs. WHAT SHE DELIVERS               *)
(* ------------------------------------------------------------- *)

(* KRATZER PROMISES (Abstract, page 1): "I make an attempt to avoid most 
   of the consequences of this paradox for the meaning definitions of 'must' and 'can'"
   
   KRATZER DELIVERS: Definitions 7-8 with consistent subset approach
   
   FORMALIZATION REVEALS: Her solution requires:
   - Decidable consistency checking (not provided)
   - Subset enumeration algorithms (not provided) 
   - Complex quantification over subsets (informally specified)
   
   We can formalize the basic idea but not the full computational procedure *)

(* KRATZER PROMISES (page 2): To capture "whatever is common to the meaning" 
   of modal words across different uses
   
   KRATZER DELIVERS: The "relative modal phrase" analysis showing all modals
   have the structure "must/can in view of X"
   
   FORMALIZATION CONFIRMS: This insight is correct and formalizable *)

(* KRATZER PROMISES (page 5): "Let us try to find out what this connection is" 
   between different uses of 'must'
   
   KRATZER DELIVERS: Conversational backgrounds as the unifying concept
   
   FORMALIZATION REVEALS: This reduces to parameterized accessibility relations
   - not a new discovery but a useful interface *)

(* KRATZER PROMISES (Section 2): To solve the "ex falso quodlibet" problem
   
   KRATZER CLAIMS TO DELIVER: Improved definitions that handle inconsistency
   
   FORMALIZATION REVEALS: 
   - The logical idea is sound 
   - But requires substantial computational machinery she doesn't provide
   - Her examples work but the general algorithm is missing *)

(* KRATZER PROMISES (page 16): To distinguish "striding and flying" readings
   
   KRATZER DELIVERS: Identification of the ambiguity and informal explanation
   
   FORMALIZATION CONFIRMS: The distinction exists (separate_recommendations ≠ conjunctive_recommendation)
   but she doesn't provide formal rules for disambiguation *)

(* KRATZER DOES NOT PROMISE BUT SHOULD HAVE: 
   - Connection to existing modal logic (we proved kratzer_equals_montague)
   - Computational procedures for her definitions
   - Formal treatment of English-to-logic translation
   - Systematic handling of context-dependence *)

(* SUMMARY: Kratzer delivers on her core insight (conversational backgrounds)
   but doesn't deliver the computational and formal details needed for 
   implementation. The formalization shows her ideas are sound but incomplete. *)

(* ------------------------------------------------------------- *)
(* 10. WHAT WE FIXED AND ADDED                                  *)
(* ------------------------------------------------------------- *)

(* FIXED:
   - Added actual consistency definition
   - Provided kratzer_must_fixed that handles inconsistent bases
   - Added missing theorems (necessitation, distribution, conjunction)
   - Added ordering sources from her later work
   
   STILL MISSING (fundamental gaps):
   - Algorithm to compute maximal_consistent_subset
   - Decidability assumptions for real implementation
   - Context resolution (how to pick conversational background)
   - Natural language parsing into modal logic *)

End KratzerClean.
