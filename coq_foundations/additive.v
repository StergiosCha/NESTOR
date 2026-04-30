(************************************************************************)
(*  Alternative Semantics and Greek Additive Operators                   *)
(*  Formalizing Rooth's Alternative Semantics + Greek ke/too             *)
(************************************************************************)

From Coq Require Import List Classical_Prop FunctionalExtensionality.
From Coq Require Import Bool Decidable.
Set Implicit Arguments.

Module AlternativeSemantics.

(* ------------------------------------------------------------- *)
(* 1. ROOTH'S ALTERNATIVE SEMANTICS (1985, 1992)               *)
(* ------------------------------------------------------------- *)

(* Basic semantic types *)
Parameter Entity : Type.
Parameter World : Type.
Definition Proposition : Type := World -> Prop.

(* Semantic values *)
Inductive SemanticValue : Type :=
  | EntityValue : Entity -> SemanticValue
  | PropValue : Proposition -> SemanticValue.

(* Focus marking *)
Definition FocusMarked : Type := bool.

(* Alternative sets - the core of alternative semantics *)
Definition AlternativeSet (A : Type) : Type := list A.

(* Ordinary semantic value *)
Definition ord (s : SemanticValue) : SemanticValue := s.

(* Focus semantic value - set of alternatives *)
Definition alt (s : SemanticValue) (focused : FocusMarked) : AlternativeSet SemanticValue :=
  match focused with
  | true => cons s nil  (* Simplified - should be proper alternative set *)
  | false => cons s nil
  end.

(* Alternative generation for entities *)
Definition entity_alternatives (e : Entity) : AlternativeSet Entity :=
  cons e nil.  (* In practice: all entities of same type *)

(* Alternative generation for propositions *)
Definition prop_alternatives (p : Proposition) (focus_var : Entity) : AlternativeSet Proposition :=
  cons p nil.  (* In practice: substitute alternatives for focus_var in p *)

(* Pointwise application of alternatives *)
Definition pointwise_alt {A B : Type} 
  (f_alts : AlternativeSet (A -> B)) 
  (x_alts : AlternativeSet A) : AlternativeSet B :=
  flat_map (fun f => map f x_alts) f_alts.

(* ------------------------------------------------------------- *)
(* 2. FOCUS OPERATORS IN ALTERNATIVE SEMANTICS                  *)
(* ------------------------------------------------------------- *)

(* The squiggle operator - focus interpretation *)
Definition focus_interp (C : AlternativeSet Proposition) (p : Proposition) : Prop :=
  In p C.

(* Generic focus-associating operator *)
Record FocusOperator := {
  operator_meaning : AlternativeSet Proposition -> Proposition -> Proposition;
  focus_sensitivity : forall C p, focus_interp C p -> 
    operator_meaning C p <> operator_meaning (cons p nil) p
}.

(* ------------------------------------------------------------- *)
(* 3. EXCLUSIVE OPERATORS (only/mono)                           *)
(* ------------------------------------------------------------- *)

(* English 'only' *)
Definition only_semantics (C : AlternativeSet Proposition) (p : Proposition) : Proposition :=
  fun w => 
    (* p is true and all other alternatives in C are false *)
    p w /\ forall q, In q C -> q <> p -> ~ q w.

(* Greek 'mono' with sisterhood constraint *)
Definition mono_semantics (C : AlternativeSet Proposition) (p : Proposition) 
  (sisterhood_satisfied : bool) : Proposition :=
  fun w =>
    match sisterhood_satisfied with
    | true => only_semantics C p w
    | false => False  (* Association fails *)
    end.

(* ------------------------------------------------------------- *)
(* 4. ADDITIVE OPERATORS (too/also/ke)                          *)
(* ------------------------------------------------------------- *)

(* English 'too'/'also' *)
Definition too_semantics (C : AlternativeSet Proposition) (p : Proposition) : Proposition :=
  fun w =>
    (* p is true AND some alternative in C is also true *)
    p w /\ 
    (exists q, In q C /\ q <> p /\ q w).

(* Greek additive 'ke' *)
Definition ke_additive_semantics (C : AlternativeSet Proposition) (p : Proposition)
  (sisterhood_satisfied : bool) : Proposition :=
  fun w =>
    match sisterhood_satisfied with
    | true => too_semantics C p w
    | false => False  (* Association fails *)
    end.

(* ------------------------------------------------------------- *)
(* 5. DISTRIBUTIVE 'KE' (Conjunction)                           *)
(* ------------------------------------------------------------- *)

(* Sum types for collective/distributive distinction *)
Parameter SumEntity : Type.
Parameter atom : SumEntity -> Entity -> Prop.
Parameter sum : Entity -> Entity -> SumEntity.

(* Distributive operator *)
Definition DIST (P : Entity -> Proposition) (sum_e : SumEntity) : Proposition :=
  fun w => forall x, atom sum_e x -> P x w.

(* Collective predicate application *)
Definition COLL (P : SumEntity -> Proposition) (sum_e : SumEntity) : Proposition :=
  fun w => P sum_e w.

(* Regular conjunction 'ke' (ambiguous between collective/distributive) *)
Definition ke_conjunction (e1 e2 : Entity) (P : Entity -> Proposition) : Proposition :=
  fun w =>
    let sum_e := sum e1 e2 in
    (* Can be either collective or distributive *)
    (exists P_sum, COLL P_sum sum_e w) \/ DIST P sum_e w.

(* Double 'ke...ke' (only distributive) *)
Definition ke_double (e1 e2 : Entity) (P : Entity -> Proposition) : Proposition :=
  fun w => DIST P (sum e1 e2) w.

(* ------------------------------------------------------------- *)
(* 6. THE HISTORICAL DEVELOPMENT                                *)
(* ------------------------------------------------------------- *)

(* CSM&S's hypothesis: distributive ke misapplied to singulars *)
Definition singular_entity (e : Entity) : Prop :=
  forall sum_e, ~ atom sum_e e \/ (forall x, atom sum_e x -> x = e).

(* When distributive ke applied to singular, alternatives emerge *)
Definition distributive_to_additive (e : Entity) (P : Entity -> Proposition) : Prop :=
  singular_entity e ->
  (* Cannot apply DIST meaningfully *)
  ~ (exists sum_e, atom sum_e e /\ exists y, atom sum_e y /\ y <> e) ->
  (* So alternatives are introduced instead *)
  exists C w, ke_additive_semantics C (P e) true w.

(* ------------------------------------------------------------- *)
(* 7. SYNTACTIC CONSTRAINTS                                     *)
(* ------------------------------------------------------------- *)

(* Abstract syntactic positions *)
Inductive SyntacticPosition : Type :=
  | SpecTP | SpecvP | VPAdj | vPAdj | TPAdj.

(* Sisterhood relation *)
Definition sister (pos1 pos2 : SyntacticPosition) : Prop :=
  match pos1 with
  | VPAdj => match pos2 with SpecvP => True | _ => False end
  | vPAdj => match pos2 with SpecTP => True | _ => False end
  | _ => False
  end.

(* Greek focus association constraint *)
Definition greek_association (op_pos assoc_pos : SyntacticPosition) : Prop :=
  sister op_pos assoc_pos.

(* Movement possibilities *)
Definition can_move (item : SyntacticPosition) : Prop :=
  match item with
  | VPAdj => True   (* mono can move *)
  | vPAdj => False  (* ke cannot move *)
  | _ => False
  end.

(* ------------------------------------------------------------- *)
(* 8. CORE THEOREMS                                             *)
(* ------------------------------------------------------------- *)

(* Alternative semantics provides proper focus sensitivity *)



(* Movement asymmetry between mono and ke *)
Theorem mono_ke_movement_asymmetry :
  can_move VPAdj /\ ~ can_move vPAdj.
Proof.
  split.
  - unfold can_move. auto.
  - unfold can_move. auto.
Qed.

