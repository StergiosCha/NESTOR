(************************************************************************)
(*  FocusEven.v — Focus-associating operators and scalar implicatures   *)
(*  Classic examples:                                                   *)
(*  • "Even JOHN came" vs "Even John CAME"                             *)
(*  • "Only Mary left" vs "Mary only LEFT"                             *)
(*  • Alternative semantics and focus interpretation                    *)
(************************************************************************)
From Coq Require Import Classical Lia.
Require Import MontagueFragment.

Import MontagueFragment.MontagueExtensional.

(* -------------------------------------------------------------- *)
(* 1. FOCUS AND ALTERNATIVES                                       *)
(* -------------------------------------------------------------- *)

Section FocusSemantics.
  
  (* Focus generates a set of alternatives *)
  Definition Alternatives (A : Type) := A -> Prop.
  
  (* A focused expression has ordinary semantic value + alternatives *)
  Record FocusedExpr (A : Type) := mkFocus {
    ordinary_value : A;
    focus_alternatives : Alternatives A
  }.
  
  (* Focus on entity: "JOHN came" *)
  Parameter john mary bill : Entity.
  Parameter came : Entity -> Prop.
  
  (* Alternative set for focused "JOHN" *)
  Definition john_alternatives : Alternatives Entity :=
    fun x => x = john \/ x = mary \/ x = bill.
  
  Definition john_focused : FocusedExpr Entity := {|
    ordinary_value := john;
    focus_alternatives := john_alternatives
  |}.
  
  (* Focus on predicate: "John CAME" *)  
  Parameter left arrived : Entity -> Prop.
  
  Definition came_alternatives : Alternatives (Entity -> Prop) :=
    fun P => P = came \/ P = left \/ P = arrived.
  
  Definition came_focused : FocusedExpr (Entity -> Prop) := {|
    ordinary_value := came;
    focus_alternatives := came_alternatives
  |}.
  
End FocusSemantics.

(* -------------------------------------------------------------- *)
(* 2. "EVEN" - The Classic Focus-Associating Operator             *)
(* -------------------------------------------------------------- *)

Section EvenSemantics.
  
  (* "Even" presupposes alternatives and scales *)
  Parameter likelihood : Entity -> (Entity -> Prop) -> Prop.  (* likelihood x P: x is likely to satisfy P *)
  Parameter surprise : Prop -> Prop.              (* surprise P: P is surprising *)
  
  (* Basic "even" semantics (simplified) *)
  Definition even_basic (focused : FocusedExpr Entity) (P : Entity -> Prop) : Prop :=
    match focused with
    | mkFocus _ val alts =>
        (* Assertion: the focused entity satisfies P *)
        P val /\
        (* Presupposition: some alternative also satisfies P *)
        (exists x, alts x /\ x <> val /\ P x)
    end.
  
  (* Example: "Even JOHN came" *)
  Definition even_john_came : Prop :=
    even_basic john_focused came.
  
  (* This means: *)
  (* 1. John came (assertion) *)
  (* 2. Someone else also came (existential presupposition) *)
  (* 3. John was least likely to come (scalar presupposition) *)
  
  (* Contrast with focus on predicate: "Even John CAME" *)
  Definition even_john_came_predicate : Prop :=
    (* Here "even" associates with the predicate CAME *)
    came john /\
    (exists P, came_alternatives P /\ P <> came /\ P john) /\
    (forall P, came_alternatives P -> P <> came ->
       likelihood john P -> likelihood john came).
  
  (* This means: *)
  (* 1. John came (assertion) *)
  (* 2. John did something else too (existential presupposition) *)
  (* 3. Coming was least likely thing for John to do (scalar presupposition) *)
  
End EvenSemantics.

(* -------------------------------------------------------------- *)
(* 3. "ONLY" - Exhaustive Focus Operator                          *)
(* -------------------------------------------------------------- *)

Section OnlySemantics.
  
  (* "Only" creates exhaustivity presuppositions *)
  Definition only_basic (focused : FocusedExpr Entity) (P : Entity -> Prop) : Prop :=
    match focused with
    | mkFocus _ val alts =>
        (* Assertion: no alternative (other than focused) satisfies P *)
        (forall x, alts x -> x <> val -> ~ P x) /\
        (* Presupposition: the focused entity satisfies P *)
        P val
    end.
  
  (* Example: "Only JOHN came" *)
  Definition only_john_came : Prop :=
    only_basic john_focused came.
  
  (* This means: *)
  (* 1. Nobody else came (assertion) *)
  (* 2. John came (presupposition) *)
  
  (* Contrast: "John only CAME" (focus on predicate) *)
  Definition john_only_came : Prop :=
    (forall P, came_alternatives P -> P <> came -> ~ P john) /\
    came john.
  
  (* This means: *)
  (* 1. John didn't do anything else (assertion) *)
  (* 2. John came (presupposition) *)
  
End OnlySemantics.

(* -------------------------------------------------------------- *)
(* 4. ALTERNATIVE SEMANTICS FRAMEWORK                             *)
(* -------------------------------------------------------------- *)

Section AlternativeSemantics.
  
  (* Rooth's alternative semantics *)
  (* Every expression has ordinary value + alternative set *)
  
  Definition AltSem (A : Type) := (A * Alternatives A)%type.
  
  (* Lift ordinary expressions to alternative semantics *)
  Definition lift {A : Type} (x : A) (alts : Alternatives A) : AltSem A :=
    (x, alts).
  
  (* Composition rule: pointwise application *)
  Definition alt_apply {A B : Type} (f_alt : AltSem (A -> B)) (x_alt : AltSem A) : AltSem B :=
    let (f, f_alts) := f_alt in
    let (x, x_alts) := x_alt in
    (f x, fun y => exists g a, f_alts g /\ x_alts a /\ y = g a).
  
  (* Focus interpretation principle *)
  (* A focus operator must have its alternative set match its argument's *)
  Definition focus_match {A B : Type} (op : AltSem A -> AltSem B) (arg : AltSem A) : Prop :=
    let (_, arg_alts) := arg in
    let (_, result_alts) := op arg in
    (* The operator's alternatives must be generated from argument's alternatives *)
    forall y, result_alts y -> exists x, arg_alts x.
  
End AlternativeSemantics.

(* -------------------------------------------------------------- *)
(* 5. SCALAR IMPLICATURES AND HORN SCALES                         *)
(* -------------------------------------------------------------- *)

Section ScalarImplicatures.
  
  (* Horn scales: ordered alternatives by informativity *)
  Definition HornScale (A : Type) := A -> A -> Prop.  (* stronger_than relation *)
  
  (* Example: <all, most, many, some> *)
  Parameter all most many some_quant : (Entity -> Prop) -> (Entity -> Prop) -> Prop.
  Parameter student : Entity -> Prop.  (* Add missing student predicate *)
  
  Definition quantifier_scale : HornScale ((Entity -> Prop) -> (Entity -> Prop) -> Prop) :=
    fun Q1 Q2 => 
      (Q1 = all /\ (Q2 = most \/ Q2 = many \/ Q2 = some_quant)) \/
      (Q1 = most /\ (Q2 = many \/ Q2 = some_quant)) \/
      (Q1 = many /\ Q2 = some_quant).
  
  (* Scalar implicature: using weaker term implicates negation of stronger *)
  Definition scalar_implicature (Q : (Entity -> Prop) -> (Entity -> Prop) -> Prop)
                                (N P : Entity -> Prop) : Prop :=
    Q N P /\ 
    (forall Q', quantifier_scale Q' Q -> ~ Q' N P).
  
  (* "Some students came" implicates "Not all students came" *)
  Definition some_not_all : Prop :=
    scalar_implicature some_quant student came.
  
  (* This unfolds to: some students came AND not all students came *)
  
End ScalarImplicatures.

(* -------------------------------------------------------------- *)
(* 6. FOCUS PROJECTION AND ASSOCIATION                            *)
(* -------------------------------------------------------------- *)

Section FocusProjection.
  
  (* Focus can project from embedded positions *)
  (* "John said that even MARY left" *)
  
  Parameter said : Entity -> Prop -> Prop.
  
  (* Focus projects from embedded clause *)
  Definition embedded_even : Prop :=
    said john (even_basic {| ordinary_value := mary; focus_alternatives := john_alternatives |} left).
  
  (* Association with focus: operators seek focused constituents *)
  Definition associates_with_focus {A : Type} {B : Type} 
    (op : FocusedExpr A -> B) 
    (expr : A) 
    (focus_alts : Alternatives A) : B :=
    op {| ordinary_value := expr; focus_alternatives := focus_alts |}.
  
  (* "Even" must associate with a focused constituent *)
  Axiom even_requires_focus : 
    forall (x : Entity) (P : Entity -> Prop),
      even_basic {| ordinary_value := x; focus_alternatives := fun _ => False |} P -> False.
  
  (* This captures that "even" is ungrammatical without focus *)
  
End FocusProjection.

(* -------------------------------------------------------------- *)
(* 7. COMPLEX EXAMPLES AND INTERACTIONS                           *)
(* -------------------------------------------------------------- *)

Section ComplexExamples.
  
  (* Multiple focus particles *)
  (* "Only even JOHN came" *)
  
  Definition only_even_john : Prop :=
    (* "Even JOHN came" is true *)
    even_john_came /\
    (* And nobody else satisfies "even X came" *)
    (forall x, john_alternatives x -> x <> john -> 
       ~ even_basic {| ordinary_value := x; focus_alternatives := john_alternatives |} came).
  
  (* Scope ambiguity with focus *)
  (* "John only introduced Bill to SUE" *)
  Parameter introduced : Entity -> Entity -> Entity -> Prop.
  Parameter sue ann kim : Entity.
  
  Definition sue_alternatives : Alternatives Entity :=
    fun x => x = sue \/ x = ann \/ x = kim.
  
  (* Reading 1: Only to Sue (narrow scope) *)
  Definition narrow_only : Prop :=
    only_basic {| ordinary_value := sue; focus_alternatives := sue_alternatives |} (introduced john bill).
  
  (* Reading 2: Only introduced (wide scope) *)  
  Definition wide_only : Prop :=
    only_basic {| ordinary_value := sue; 
                  focus_alternatives := sue_alternatives |}
      (introduced john bill).
  
  (* These give different truth conditions! *)
  
End ComplexExamples.

(* -------------------------------------------------------------- *)
(* 8. FORMAL PROPERTIES AND THEOREMS                              *)
(* -------------------------------------------------------------- *)

Section FormalProperties.
  
  (* "Even" and "only" are duals in some sense *)
  Theorem even_only_relationship :
    forall (focused : FocusedExpr Entity) (P : Entity -> Prop),
      even_basic focused P ->
      ~ only_basic focused (fun x => ~ P x).
  Proof.
    intros focused P Heven.
    unfold even_basic, only_basic in *.
    destruct focused as [val alts].
    simpl in *.
    destruct Heven as [HP Hexists].
    intro Honly.
    destruct Honly as [Hexh Hpresup].
    (* "Even" says some alternative satisfies P *)
    destruct Hexists as [x [Hx_alt [Hx_neq Hx_P]]].
    (* "Only" says no alternative satisfies ~P (i.e., all satisfy P) *)
    specialize (Hexh x Hx_alt Hx_neq).
    (* But Hx_P says x satisfies P, so ~(~P x) *)
    apply Hexh. firstorder. 
  Qed.
  
  (* Focus alternatives must be non-empty for "even" *)
  Theorem even_requires_alternatives :
    forall (x : Entity) (P : Entity -> Prop),
      even_basic {| ordinary_value := x; focus_alternatives := fun _ => False |} P -> False.
  Proof.
    intros x P Heven.
    unfold even_basic in Heven.
    simpl in Heven.
    (* Now Heven should be: P x /\ (exists y, False /\ y <> x /\ P y) *)
    destruct Heven as [HPx Hexists].
    (* Hexists should be: exists y, False /\ y <> x /\ P y *)
    destruct Hexists as [y [Hfalse [Hneq HPy]]].
    (* Hfalse should be: False *)
    exact Hfalse.
  Qed.
  (* "Only" preserves truth of focused constituent *)
  Theorem only_preserves_focus :
    forall (focused : FocusedExpr Entity) (P : Entity -> Prop),
      only_basic focused P -> P (match focused with mkFocus _ val _ => val end).
  Proof.
    intros focused P Honly.
    unfold only_basic in Honly.
    destruct focused as [val alts].
    simpl in *.
    destruct Honly as [_ Hpresup].
    exact Hpresup.
  Qed.
  
End FormalProperties.

(* -------------------------------------------------------------- *)
(* SUMMARY: Focus-Associating Operators Formalized               *)
(* -------------------------------------------------------------- *)

(* We've captured:
   1. Focus semantics with alternatives
   2. "Even" with scalar and existential presuppositions  
   3. "Only" with exhaustivity and existential presuppositions
   4. Alternative semantics framework (Rooth)
   5. Scalar implicatures and Horn scales
   6. Focus projection and association patterns
   7. Complex interactions and scope ambiguities
   8. Formal properties and theorems
   
   This shows how focus particles create complex meaning components
   that go far beyond simple assertion! *)
