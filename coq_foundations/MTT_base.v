(************************************************************************)
(*  MTT From Scratch - Building Modern Type Theory for Language          *)
(*  Step-by-step construction with explanations                          *)
(************************************************************************)

(* -------------------------------------------------------------- *)
(* STEP 1: WHY DO WE NEED TYPES FOR NATURAL LANGUAGE?            *)
(* -------------------------------------------------------------- *)

(** Traditional formal semantics uses set theory:
    - "Human" is a set: {john, mary, bob, ...}
    - "walks" is a function: Human -> {true, false}
    - "Every human walks" means: for all x in Human, walks(x) = true
    
    Problems with set-theoretic approach:
    1. No distinction between different kinds of objects
    2. Cannot handle complex phenomena like polysemy ("book" = physical object + information)
    3. No natural way to represent context-dependent meaning
    4. Cannot capture fine-grained semantic distinctions
    
    Solution: Use TYPES instead of sets
    - Types can carry more information than sets
    - Types can be dependent (vary based on other values)
    - Types naturally support subtyping and inheritance
**)

(* -------------------------------------------------------------- *)
(* STEP 2: BASIC TYPE UNIVERSE FOR COMMON NOUNS                  *)
(* -------------------------------------------------------------- *)

(** In MTT, common nouns are TYPES, not sets **)
Definition CN := Type.

(** Some basic common noun types **)
Parameter Human Animal Object : CN.
Parameter Man Woman : CN.

(** Why types instead of sets?
    - Types can be refined and restricted
    - Types support natural subtyping relationships
    - Types can be parameterized and dependent
    - Types integrate with proof theory (proof-relevant semantics)
**)

(* -------------------------------------------------------------- *)  
(* STEP 3: INDIVIDUALS AS ELEMENTS OF TYPES                      *)
(* -------------------------------------------------------------- *)

(** Individuals are elements of common noun types **)
Parameter john mary : Human.
Parameter bob : Man.
Parameter alice : Woman.

(** This immediately gives us type safety:
    - john : Human means john is classified as human
    - Can't accidentally apply human-specific predicates to non-humans
    - Type checker ensures semantic well-formedness
**)

(* -------------------------------------------------------------- *)
(* STEP 4: SUBTYPING RELATIONSHIPS                               *)
(* -------------------------------------------------------------- *)

(** Natural language has subtype relationships:
    "Man is a kind of Human"
    "Human is a kind of Animal"  
    "Animal is a kind of Object"
**)

Axiom mh : Man -> Human.
Axiom wh : Woman -> Human.
Axiom ha : Human -> Animal.
Axiom ao : Animal -> Object.

(** Coercions make subtyping automatic **)
Coercion mh : Man >-> Human.
Coercion wh : Woman >-> Human.
Coercion ha : Human >-> Animal.
Coercion ao : Animal >-> Object.

(** Now bob : Man automatically counts as Human, Animal, Object **)
Check bob : Human.  (* Works via coercion *)
Check bob : Animal. (* Works via coercion chain *)

(* -------------------------------------------------------------- *)
(* STEP 5: PREDICATES AND PROPERTIES                             *)
(* -------------------------------------------------------------- *)

(** Predicates are functions from types to propositions **)
Parameter walks sleeps talks : Human -> Prop.
Parameter heavy red : Object -> Prop.

(** Type safety in action **)
Check walks john.    (* ✓ john : Human *)
Check walks bob.     (* ✓ bob : Man -> Human via coercion *)
(* Check walks 5.    (* ✗ 5 is not Human - type error! *) *)

(** Properties can be restricted to appropriate types **)
Parameter pregnant : Woman -> Prop.  (* Only makes sense for women *)

(* -------------------------------------------------------------- *)
(* STEP 6: QUANTIFIERS                                           *)
(* -------------------------------------------------------------- *)

(** Quantifiers operate over types, not sets **)
Definition some (A : CN) (P : A -> Prop) : Prop := 
  exists x : A, P x.

Definition all (A : CN) (P : A -> Prop) : Prop := 
  forall x : A, P x.

(** Examples **)
Definition some_human_walks := some Human walks.
Definition all_humans_sleep := all Human sleeps.

(** Type-restricted quantification is natural **)
Definition some_woman_pregnant := some Woman pregnant.

(* -------------------------------------------------------------- *)
(* STEP 7: WHY SUBTYPING MATTERS FOR QUANTIFIERS                 *)
(* -------------------------------------------------------------- *)

(** Subtyping allows natural inferences **)
Theorem men_are_humans : 
  all Man walks -> some Human walks.
Proof.
  intro H.
  exists bob.  (* bob : Man, coerces to Human *)
  apply H.
Qed.

(** This captures the intuition that:
    "All men walk" implies "Some humans walk"
**)

(* -------------------------------------------------------------- *)
(* STEP 8: ADJECTIVES AS TYPE CONSTRUCTORS                       *)
(* -------------------------------------------------------------- *)

(** Problem: How do we handle "tall human"?
    
    Option 1 (bad): Make "tall" a predicate tall : Human -> Prop
    Then "tall human" isn't a type, just humans that satisfy tall
    
    Option 2 (good): Make "tall human" a new type!
    This is a SUBTYPE of Human containing only tall humans
**)

(** Adjectives as type constructors **)
Definition Adjective := forall A : CN, A -> Prop.

Parameter tall short  light : Adjective.

(** Adjective-noun composition creates subtypes **)
Definition modified_noun (adj : Adjective) (N : CN) : CN :=
  { x : N | adj N x }.

(** Now we can create new types compositionally **)
Definition TallHuman : CN := modified_noun tall Human.
Definition LightObject : CN := modified_noun light Object.

(** Automatic subtyping via sigma projection **)
Definition tall_human_to_human : TallHuman -> Human := 
  fun x => proj1_sig x.
Coercion tall_human_to_human : TallHuman >-> Human.

(* -------------------------------------------------------------- *)
(* STEP 9: WHY THIS APPROACH IS POWERFUL                         *)
(* -------------------------------------------------------------- *)

(** 1. Compositionality: Can build complex types **)
Definition TallLightHuman : CN := 
  modified_noun light  (modified_noun tall Human).

(** 2. Type safety: Only tall humans in TallHuman type **)
Parameter mike : TallHuman.
Check tall Human mike.  (* True by construction! *)

(** 3. Natural subsumption: Tall humans are humans **)
Check walks mike.  (* mike : TallHuman -> Human, so walks applies *)

(** 4. Quantification over subtypes **)
Definition some_tall_human_walks := some TallHuman walks.
Definition all_tall_humans_sleep := all TallHuman sleeps.

(* -------------------------------------------------------------- *)
(* STEP 10: MULTIPLE INHERITANCE AND COMPLEX TYPES              *)
(* -------------------------------------------------------------- *)

(** Types can inherit from multiple sources **)
Parameter Surgeon Teacher : CN.
Axiom sh : Surgeon -> Human.
Axiom th : Teacher -> Human.
Coercion sh : Surgeon >-> Human.
Coercion th : Teacher >-> Human.

(** Can have surgeon-teachers **)
Definition SurgeonTeacher : CN := 
  { x : Human | exists (s : Surgeon) (t : Teacher), 
                sh s = x /\ th t = x }.

(** Properties flow along inheritance chains **)
Theorem surgeons_walk : 
  all Human walks -> all Surgeon walks.
Proof.
cbv.   intro H.
 firstorder.   (* s : Surgeon -> Human via coercion *)
Qed.

(* -------------------------------------------------------------- *)
(* STEP 11: WHERE WE GO FROM HERE                                *)
(* -------------------------------------------------------------- *)

(** This foundation enables:
    
    1. Dot types: Book = Physical • Information
    2. Event types: Complex events with participants  
    3. Context-dependent types: Meaning that varies with context
    4. Polydefinites: Types that mark prominence
    5. Degree semantics: Gradable adjectives with standards
    6. Dependent types: Types that depend on values
    7. Proof-relevant semantics: Meaning includes proof obligations
    
    Next steps:
    - Add dependent types for context
    - Build event structure  
    - Add dynamic semantics
    - Implement specific linguistic phenomena
**)

(* -------------------------------------------------------------- *)
(* SUMMARY: WHY MTT FOR LANGUAGE?                                *)
(* -------------------------------------------------------------- *)

(** MTT provides:
    ✓ Type safety for semantic composition
    ✓ Natural subtyping for taxonomic relationships  
    ✓ Compositional adjective semantics
    ✓ Proof-relevant meaning representations
    ✓ Foundation for complex linguistic phenomena
    ✓ Integration with computational implementations
    
    This is just the beginning! The real power comes when we add:
    - Dependent types for context-sensitivity
    - Inductive types for complex structures  
    - Module system for organizing theories
    - Proof tactics for automated reasoning
**)
