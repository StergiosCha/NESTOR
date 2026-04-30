(* ====================================================================
   CASE STUDY: Why File Change Semantics Cannot Be Fully Formalized in Coq
   
   Based on: Heim, Irene (1983). "File Change Semantics and the 
   Familiarity Theory of Definiteness"
   
   This file demonstrates the fundamental barriers to mechanizing 
   File Change Semantics (FCS) in a constructive type theory like Coq.
   ==================================================================== *)

Require Import Coq.Lists.List.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical.
Import ListNotations.

(* ==================================================================== 
   PART 1: THE THEORY AS PRESENTED IN THE LITERATURE
   ==================================================================== *)

(* In File Change Semantics, Heim proposes:
   
   1. A FILE is a partial function from indices to individuals
   2. An INFORMATION STATE is a set of files
   3. Sentences denote CONTEXT CHANGE POTENTIALS (CCPs)
   4. A CCP is a function: InfoState -> InfoState
   
   Key insight: Indefinites introduce NEW file cards (discourse referents)
   that remain accessible for anaphoric reference.
*)

(* ==================================================================== 
   ATTEMPT 1: Direct Encoding (Fails)
   ==================================================================== *)

Section DirectEncoding.

(* Universe of individuals *)
Variable Entity : Type.

(* Indices for discourse referents *)
Variable Index : Type.

(* A file: partial function from indices to entities *)
Definition File1 := Index -> option Entity.

(* Information state: SET of files 
   PROBLEM 1: In Coq, we cannot have arbitrary sets
   We need to either:
   - Use Type (but then it's not a set, it's a type)
   - Use Ensemble (but then we need classical logic)
   - Use lists (but then we lose set semantics)
*)

(* Try with Ensemble *)
Definition InfoState1 := Ensemble File1.

(* Context Change Potential *)
Definition CCP1 := InfoState1 -> InfoState1.

(* PROBLEM 2: How do we construct Ensembles computationally?
   
   In classical semantics, we can say:
   
   [[∃x.P(x)]] = λI. {f ∈ I | ∃d ∈ D. f[x:=d] satisfies P}
   
   But in Coq:
   - We cannot iterate over all elements of an Ensemble
   - We cannot construct an Ensemble by comprehension without LEM
   - The set comprehension is not decidable
*)

(* Example: Try to define the semantics of existential quantifier *)
Definition exists_ccp (x : Index) (P : File1 -> Prop) : CCP1 :=
  fun (I : InfoState1) =>
    (* We want: {f' | ∃f ∈ I. ∃d:Entity. f' = f[x:=d] ∧ P(f')} *)
    (* But we CANNOT write this constructively! *)
    
    (* This doesn't work: *)
    fun (f' : File1) => 
      exists (f : File1) (d : Entity),
        In _ I f /\ 
        (forall i, i = x -> f' i = Some d) /\
        (forall i, i <> x -> f' i = f i) /\
        P f'.

(* The above "definition" is ill-typed because:
   - Ensemble expects a predicate, but we're trying to compute
   - The existential quantifier hides the choice of f and d
   - There's no decision procedure for membership in I
*)

End DirectEncoding.

(* ==================================================================== 
   PROBLEM 2: THE RANDOM RESET OPERATOR
   ==================================================================== *)

Section RandomResetProblem.

Variable Entity : Type.
Variable Index : Type.
Definition File2 := Index -> option Entity.
Definition InfoState2 := Ensemble File2.

(* In FCS, [[∃x.φ]] uses a "random reset" operator:
   
   f[x] = any assignment that differs from f at most on x
   
   PROBLEM: "Any assignment" is inherently non-deterministic
   
   In classical logic: we can say "there exists some assignment"
   In constructive logic: we need to CONSTRUCT the assignment
   
   But which one? The choice is arbitrary!
*)

(* We could try to encode non-determinism with a relation *)
Definition random_reset (x : Index) : File2 -> File2 -> Prop :=
  fun f f' =>
    (exists d : Entity, f' x = Some d) /\
    (forall i, i <> x -> f' i = f i).

(* But now our semantics is not a FUNCTION anymore,
   it's a RELATION. This changes the entire framework! *)

Definition CCP_relational := InfoState2 -> InfoState2 -> Prop.

(* And we lose compositionality:
   
   If [[φ]] : I -> I' and [[ψ]] : I' -> I''
   then [[φ ; ψ]] should be: I -> I''
   
   But with relations:
   If [[φ]] : I -> I1 and [[φ]] : I -> I2 (multiple outputs)
   How do we compose?
*)

End RandomResetProblem.

(* ==================================================================== 
   PROBLEM 3: GLOBAL EFFECTS OF LOCAL QUANTIFIERS
   ==================================================================== *)

Section GlobalEffectsProblem.

Variable Entity : Type.
Variable Index : Type.
Definition File3 := Index -> option Entity.

(* Classic donkey sentence:
   "Every farmer who owns a donkey beats it"
   
   Structure: ∀x. (farmer(x) ∧ ∃y. donkey(y) ∧ owns(x,y)) → beats(x,y)
   
   The existential ∃y is syntactically in the antecedent,
   but the variable y must be accessible in the consequent!
   
   PROBLEM: In typed lambda calculus, this is impossible!
   
   The standard treatment:
   λx. (farmer(x) ∧ ∃y. donkey(y) ∧ owns(x,y)) has type Entity -> Prop
   
   The variable y is bound inside this expression and cannot escape.
*)

(* FCS solves this by making quantifiers modify the GLOBAL file
   But this breaks compositionality in a typed setting! *)

(* Attempt to type the sentence: *)
Variable farmer : Entity -> Prop.
Variable donkey : Entity -> Prop.
Variable owns : Entity -> Entity -> Prop.
Variable beats : Entity -> Entity -> Prop.

(* Standard (impossible) attempt: *)
Definition donkey_sentence_impossible : Prop :=
  forall x : Entity,
    farmer x ->
    (exists y : Entity, donkey y /\ owns x y) ->
    (* Now we want to say: beats x y 
       But y is not in scope! *)
    exists y : Entity, beats x y. (* This is too weak! *)

(* FCS solution: quantifiers are file operations
   But to type this, we need dependent types where the TYPE
   depends on the RUNTIME VALUE of the file! *)

End GlobalEffectsProblem.

(* ==================================================================== 
   PROBLEM 4: PRESUPPOSITION ACCOMMODATION IS NON-MONOTONIC
   ==================================================================== *)

Section PresuppositionProblem.

Variable Entity : Type.
Variable Index : Type.
Definition File4 := Index -> option Entity.
Definition InfoState4 := Ensemble File4.

(* Definites presuppose familiarity:
   "The king of France" presupposes there's a king of France in the file
   
   If the presupposition FAILS, FCS proposes ACCOMMODATION:
   - Add a new file card for the king of France
   - Then evaluate the sentence
   
   PROBLEM: This is non-monotonic reasoning!
   
   Accommodation depends on:
   1. Whether the referent is already present (requires global search)
   2. Whether adding it would be consistent (requires global check)
   3. Pragmatic factors (what's most plausible)
   
   In Coq, we cannot:
   - Search an arbitrary Ensemble
   - Make decisions based on failure
   - Incorporate pragmatic reasoning
*)

(* Attempted encoding: *)
Definition accommodate (i : Index) (I : InfoState4) : InfoState4 :=
  (* If i is not defined in any file in I, add it *)
  (* But we cannot check this constructively! *)
  
  (* Classical encoding (doesn't compute): *)
  fun f => 
    In _ I f \/  (* f was already there, OR *)
    (exists f' d, In _ I f' /\  (* there's some f' in I *)
                  f' i = None /\  (* where i is undefined *)
                  f i = Some d /\  (* and f defines i *)
                  (forall j, j <> i -> f j = f' j)).  (* same elsewhere *)

(* This is not computable because:
   1. We can't decide "In _ I f'" for arbitrary Ensembles
   2. We can't find the witness f'
   3. We can't decide whether to accommodate
*)

End PresuppositionProblem.

(* ==================================================================== 
   PROBLEM 5: UPDATE SEMANTICS VS. DENOTATIONAL SEMANTICS
   ==================================================================== *)

Section UpdateVsDenotational.

(* FCS conflates two distinct notions:
   
   1. SEMANTIC VALUE: what a sentence means
   2. UPDATE EFFECT: how a sentence changes context
   
   In Coq, we need to keep these separate!
   
   Consider: "It is raining and it is not raining"
   
   Classical semantics: this is contradictory, denotes FALSE
   FCS: this is an update that produces the EMPTY info state
   
   But in Coq:
   - False is a proposition (type Prop)
   - Empty info state is a value (type InfoState)
   These are DIFFERENT TYPES and cannot be conflated!
*)

Variable Entity : Type.
Variable Index : Type.
Definition File5 := Index -> option Entity.
Definition InfoState5 := Ensemble File5.

(* If we want to handle both, we need TWO semantic functions: *)
Definition static_semantics : Type := Prop.  (* classical meaning *)
Definition dynamic_semantics : Type := InfoState5 -> InfoState5.  (* update *)

(* But FCS wants these to be the SAME function!
   This is a type error in Coq. *)

(* Moreover, even if we pick dynamic_semantics,
   we lose the connection to truth conditions:
   
   When is a sentence TRUE in FCS?
   Answer: When the output info state is non-empty
   
   But this means: Truth depends on the input context!
   
   Example:
   Input: I = {f1, f2}  (two files)
   Sentence: "x is a cat" (test that x is a cat)
   Output: {f ∈ I | f(x) is a cat}
   
   Is the sentence true?
   - If both f1(x) and f2(x) are cats: Yes (output non-empty)
   - If only f1(x) is a cat: Yes (output non-empty)
   - If neither is a cat: No (output empty)
   
   So truth is CONTEXT-DEPENDENT, which contradicts classical semantics!
*)

End UpdateVsDenotational.

(* ==================================================================== 
   PROBLEM 6: PARTIALITY AND DEFINEDNESS
   ==================================================================== *)

Section PartialityProblem.

Variable Entity : Type.
Variable Index : Type.
Definition File6 := Index -> option Entity.

(* Files are PARTIAL functions: not all indices are defined
   
   Question: What happens when we try to access an undefined index?
   
   FCS answer: Presupposition failure -> empty output
   
   But in Coq, we need to handle option types explicitly:
*)

Definition access_file (f : File6) (i : Index) : option Entity :=
  f i.

(* Every operation must case-split on Some/None *)
Definition file_satisfies (f : File6) (i : Index) (P : Entity -> Prop) : Prop :=
  match f i with
  | Some e => P e
  | None => False  (* Presupposition failure *)
  end.

(* This means EVERY semantic rule must explicitly handle failure!
   
   Compare to FCS informal definition:
   "[[the x]] is defined iff x is in the domain"
   
   In Coq, we must make this explicit everywhere:
*)

Variable smart : Entity -> Prop.

Definition the_x_is_smart (i : Index) : File6 -> Prop :=
  fun f =>
    match f i with
    | Some e => smart e
    | None => False  (* undefined *)
    end.

(* But FCS wants to propagate undefinedness IMPLICITLY.
   This is like exception handling, which Coq doesn't have! *)

End PartialityProblem.

(* ==================================================================== 
   PART 2: WHAT CAN BE SALVAGED?
   ==================================================================== *)

Section PartialFormalization.

(* We CAN formalize fragments of FCS by making compromises: *)

Variable Entity : Type.

(* Use natural numbers for indices *)
(* We use nat directly as the index type *)

(* Use LISTS instead of sets *)
Definition File7 := nat -> option Entity.
Definition InfoState7 := list File7.

(* Now we can write decidable operations! *)
Fixpoint filter_files (P : File7 -> bool) (I : InfoState7) : InfoState7 :=
  match I with
  | [] => []
  | f :: fs => if P f then f :: filter_files P fs else filter_files P fs
  end.

(* But we've lost:
   1. Set semantics (duplicates, order matters)
   2. Infinite domains (lists are finite)
   3. Non-determinism (we must pick specific outputs)
   4. The connection to the informal theory
*)

(* We can formalize simple test operations: *)
(* Definition test (P : File7 -> Prop) : InfoState7 -> InfoState7 :=
  filter (fun f => if excluded_middle_informative (P f) then true else false).
  (* Requires decidability! *)
*)

(* But for existentials, we're stuck:
   We cannot enumerate all possible entities to extend the file with *)

End PartialFormalization.

(* ==================================================================== 
   CONCLUSION: WHY FCS CANNOT BE FULLY FORMALIZED
   ==================================================================== *)

(* The fundamental barriers:

1. NON-CONSTRUCTIVE SET THEORY
   - FCS uses arbitrary sets and set comprehension
   - Coq requires constructive definitions
   - No workaround without losing computational content

2. NON-DETERMINISM
   - Random reset operator is inherently non-deterministic  
   - Coq functions must be deterministic
   - Encoding as relations destroys compositionality

3. IMPREDICATIVITY
   - Info states contain sets of files
   - Files contain info states (for attitude verbs)
   - This creates impredicative definitions that Coq rejects

4. PARTIALITY AND FAILURE
   - Undefined file cards cause presupposition failure
   - FCS handles this implicitly (like exceptions)
   - Coq requires explicit error handling everywhere

5. TYPE CONFUSION
   - FCS conflates propositions and state transformations
   - These are different types in Coq
   - Cannot be unified without losing static typing

6. GLOBAL SIDE EFFECTS
   - Quantifiers modify global file structure
   - Breaks lexical scoping and compositionality
   - No type-safe encoding in simply-typed settings

7. PRAGMATIC ACCOMMODATION
   - Accommodation requires pragmatic reasoning
   - This is outside the scope of formal semantics
   - Cannot be mechanized without AI-complete reasoning

LESSON: FCS is "formal" in the sense of using mathematical notation,
but NOT formal in the sense of being mechanizable. The gap between
these two notions of "formal" is exactly what this formalization
attempt reveals.

Alternative: We could formalize a DIFFERENT theory that captures
similar intuitions but is mechanizable. This would be scientific
progress! But it would not be "formalizing FCS" - it would be
proposing a new theory.
*)

(* ==================================================================== 
   APPENDIX: WHAT A MECHANIZABLE THEORY WOULD NEED
   ==================================================================== *)

(* A mechanizable dynamic semantics would require:

1. DECIDABLE TYPES
   - Replace sets with decidable data structures (lists, maps)
   - Ensure all operations are computable

2. EXPLICIT CHOICE
   - Replace non-determinism with explicit choice functions
   - Or use monadic encoding of non-determinism

3. EXPLICIT CONTEXT THREADING
   - Make context an explicit parameter everywhere
   - Use state monad or similar structure

4. EXPLICIT ERROR HANDLING
   - Use option/either types for partiality
   - Propagate errors explicitly through computations

5. STRATIFIED TYPES
   - Avoid impredicative definitions
   - Use universe levels correctly

6. SEPARATE SEMANTIC LEVELS
   - Static semantics (truth conditions)
   - Dynamic semantics (updates)
   - Pragmatics (accommodation)
   Keep these as separate functions!

Such a theory EXISTS: yIt's called "Update Semantics with Structured Contexts"
and has been successfully formalized. But it's NOT File Change Semantics -
it's a different theory inspired by similar problems.
*)
