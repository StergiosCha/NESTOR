(************************************************************************)
(*  PresuppositionProjection.v — Modeling presupposition projection     *)
(*  Classic examples:                                                   *)
(*  • "The King of France is bald" presupposes France has a king       *)
(*  • "John stopped smoking" presupposes John used to smoke            *)
(*  • Projection through negation, conditionals, quantifiers           *)
(************************************************************************)
From Coq Require Import Classical Lia.
Require Import MontagueFragment.

Import MontagueFragment.MontagueExtensional.

(* -------------------------------------------------------------- *)
(* Basic presupposition infrastructure                             *)
(* -------------------------------------------------------------- *)

(* A proposition with presuppositions *)
Record PresupProp := mkPresup {
  assertion : Prop;           (* What is asserted *)
  presupposition : Prop       (* What is presupposed *)
}.

(* Truth conditions: assertion is true AND presupposition is satisfied *)
Definition presup_true (p : PresupProp) : Prop :=
  presupposition p /\ assertion p.

(* Presupposition failure: presupposition fails *)
Definition presup_failure (p : PresupProp) : Prop :=
  ~ presupposition p.

(* Truth value gaps: neither true nor false when presupposition fails *)
Definition truth_value_gap (p : PresupProp) : Prop :=
  presup_failure p.

(* -------------------------------------------------------------- *)
(* Classic examples of presuppositional expressions               *)
(* -------------------------------------------------------------- *)

Section BasicPresuppositions.
  
  (* Definite descriptions: "The King of France" *)
  Parameter france : Entity.
  Parameter king_of : Entity -> Entity -> Prop.  (* king_of x y: x is king of y *)
  Parameter bald : Entity -> Prop.
  
  (* Existence and uniqueness for definite descriptions *)
  Definition exists_unique (P : Entity -> Prop) : Prop :=
    exists x, P x /\ forall y, P y -> x = y.
  
  (* "The King of France is bald" *)
  Definition king_of_france_is_bald : PresupProp := mkPresup
    (* Assertion: the (unique) king of France is bald *)
    (exists x, king_of x france /\ bald x)
    (* Presupposition: France has a unique king *)
    (exists_unique (fun x => king_of x france)).
  
  (* Factive verbs: "John knows that P" presupposes P *)
  Parameter john : Entity.
  Parameter mary : Entity.
  Parameter knows : Entity -> Prop -> Prop.
  Parameter left : Entity -> Prop.
  
  (* "John knows that Mary left" *)
  Definition john_knows_mary_left : PresupProp := mkPresup
    (* Assertion: John knows Mary left *)
    (knows john (left mary))
    (* Presupposition: Mary left *)
    (left mary).
  
  (* Change of state verbs: "John stopped smoking" *)
  Parameter smokes : Entity -> Prop.
  Parameter stopped_smoking : Entity -> Prop.
  
  (* "John stopped smoking" *)
  Definition john_stopped_smoking : PresupProp := mkPresup
    (* Assertion: John stopped smoking *)
    (stopped_smoking john)
    (* Presupposition: John used to smoke *)
    (smokes john).
  
End BasicPresuppositions.

(* -------------------------------------------------------------- *)
(* Negation and presupposition projection                         *)
(* -------------------------------------------------------------- *)

Section NegationProjection.
  
  (* Key insight: Negation preserves presuppositions! *)
  (* "The King of France is NOT bald" still presupposes France has a king *)
  
  Definition presup_negation (p : PresupProp) : PresupProp := mkPresup
    (* Assertion: negated assertion *)
    (~ assertion p)
    (* Presupposition: SAME presupposition *)
    (presupposition p).
  
  (* Projection theorem for negation *)
  Theorem negation_preserves_presupposition :
    forall p : PresupProp,
      presupposition (presup_negation p) = presupposition p.
  Proof.
    intro p. unfold presup_negation. simpl. reflexivity.
  Qed.
  
  (* Example: "The King of France is NOT bald" *)
  Definition king_not_bald := presup_negation king_of_france_is_bald.
  
  (* Both positive and negative forms have same presupposition *)
  Lemma same_presupposition_under_negation :
    presupposition king_of_france_is_bald = presupposition king_not_bald.
  Proof.
    unfold king_not_bald. 
    unfold presup_negation. 
    simpl. 
    reflexivity.
  Qed.
  
End NegationProjection.

(* -------------------------------------------------------------- *)
(* Conditional presupposition projection                          *)
(* -------------------------------------------------------------- *)

Section ConditionalProjection.
  
  (* Complex projection behavior in conditionals *)
  (* "If P then Q" where Q has presupposition R *)
  
  Definition presup_conditional (P : Prop) (Q : PresupProp) : PresupProp := mkPresup
    (* Assertion: P → assertion(Q) *)
    (P -> assertion Q)
    (* Presupposition: P → presupposition(Q) *)  
    (P -> presupposition Q).
  
  (* Example: "If John is married, then his wife is pregnant" *)
  Parameter married : Entity -> Prop.
  Parameter wife_of : Entity -> Entity.
  Parameter pregnant : Entity -> Prop.
  
  (* "John's wife is pregnant" presupposes John has a wife *)
  Definition johns_wife_pregnant : PresupProp := mkPresup
    (pregnant (wife_of john))
    (married john).  (* Simplified: being married implies having a wife *)
  
  (* "If John is rich, then his wife is pregnant" *)
  Parameter rich : Entity -> Prop.
  Definition conditional_wife_pregnant := 
    presup_conditional (rich john) johns_wife_pregnant.
  
  (* The presupposition becomes: "If John is rich, then John is married" *)
  Lemma conditional_presupposition :
    presupposition conditional_wife_pregnant = (rich john -> married john).
  Proof.
    unfold conditional_wife_pregnant, presup_conditional. 
    simpl. reflexivity.
  Qed.
  
End ConditionalProjection.

(* -------------------------------------------------------------- *)
(* Universal quantification and presupposition                    *)
(* -------------------------------------------------------------- *)

Section UniversalProjection.
  
  (* "All of John's children are asleep" *)
  (* Presupposes: John has children *)
  
  Parameter child_of : Entity -> Entity -> Prop.
  Parameter asleep : Entity -> Prop.
  
  Definition all_johns_children_asleep : PresupProp := mkPresup
    (* Assertion: all of John's children are asleep *)
    (forall x, child_of x john -> asleep x)
    (* Presupposition: John has children *)
    (exists x, child_of x john).
  
  (* Universal quantification over presuppositional statements *)
  (* "Every professor knows that logic is hard" *)
  Parameter professor : Entity -> Prop.
  Parameter logic_hard : Prop.
  
  (* Individual statement: "x knows that logic is hard" *)
  Definition knows_logic_hard (x : Entity) : PresupProp := mkPresup
    (knows x logic_hard)
    logic_hard.
  
  (* Universal quantification *)
  Definition every_prof_knows_logic : PresupProp := mkPresup
    (* Assertion: every professor knows logic is hard *)
    (forall x, professor x -> knows x logic_hard)
    (* Presupposition: logic is hard (projects universally) *)
    logic_hard.
  
  (* Projection theorem: universal presupposition *)
  Theorem universal_presupposition_projection :
    forall (P : Entity -> Prop) (Q : Entity -> PresupProp),
      (* If every individual in domain has same presupposition *)
      (forall x, P x -> presupposition (Q x) = presupposition (Q john)) ->
      (* Then universal statement has that presupposition *)
      presupposition (mkPresup 
        (forall x, P x -> assertion (Q x))
        (presupposition (Q john))) = presupposition (Q john).
  Proof.
    intros P Q H. simpl. reflexivity.
  Qed.
  
End UniversalProjection.

(* -------------------------------------------------------------- *)
(* Presupposition accommodation and context                      *)
(* -------------------------------------------------------------- *)

Section Accommodation.
  
  (* Context: set of propositions taken as given *)
  Definition Context := Prop -> Prop.
  
  (* A proposition is in the context *)
  Definition in_context (ctx : Context) (p : Prop) : Prop := ctx p.
  
  (* Context entails a proposition *)
  Definition context_entails (ctx : Context) (p : Prop) : Prop :=
    (forall q, in_context ctx q -> q) -> p.
  
  (* Presupposition satisfaction relative to context *)
  Definition presup_satisfied_in_context (ctx : Context) (p : PresupProp) : Prop :=
    context_entails ctx (presupposition p).
  
  (* Accommodation: adding presupposition to context *)
  Definition accommodate (ctx : Context) (presup : Prop) : Context :=
    fun p => in_context ctx p \/ p = presup.
  
  (* Felicity condition: utterance is felicitous if presuppositions are satisfied *)
  Definition felicitous (ctx : Context) (p : PresupProp) : Prop :=
    presup_satisfied_in_context ctx p.
  
  (* Global accommodation theorem *)
  Theorem global_accommodation :
    forall (ctx : Context) (p : PresupProp),
      felicitous (accommodate ctx (presupposition p)) p.
  Proof.
    intros ctx p.
    unfold felicitous, presup_satisfied_in_context, context_entails.
    intro H.
    apply H.
    unfold accommodate, in_context.
    right. reflexivity.
  Qed.
  
End Accommodation.

(* -------------------------------------------------------------- *)
(* Projection patterns and filtering                             *)
(* -------------------------------------------------------------- *)

Section ProjectionPatterns.
  
  (* Holes: contexts that let all presuppositions through *)
  (* Plugs: contexts that block all presuppositions *)  
  (* Filters: contexts that let some presuppositions through *)
  
  (* Holes: negation, questions *)
  Definition hole_context (P : PresupProp) : PresupProp :=
    presup_negation P.  (* Negation is a hole *)
  
  (* Plugs: modal contexts like "believe" *)
  Parameter believes : Entity -> Prop -> Prop.
  
  Definition plug_context (x : Entity) (P : PresupProp) : PresupProp := mkPresup
    (* Assertion: x believes assertion(P) *)
    (believes x (assertion P))
    (* Presupposition: NONE (plugged) *)
    True.
  
  (* Filters: conditionals with complex projection *)
  Definition filter_context (cond : Prop) (P : PresupProp) : PresupProp :=
    presup_conditional cond P.
  
  (* Classification theorem *)
  Definition is_hole (f : PresupProp -> PresupProp) : Prop :=
    forall P, presupposition (f P) = presupposition P.
  
  Definition is_plug (f : PresupProp -> PresupProp) : Prop :=
    forall P, presupposition (f P) = True.
  
  Theorem negation_is_hole : is_hole presup_negation.
  Proof.
    unfold is_hole. intro P. apply negation_preserves_presupposition.
  Qed.
  
  Theorem belief_is_plug : forall x, is_plug (plug_context x).
  Proof.
    unfold is_plug, plug_context. intros x P. simpl. reflexivity.
  Qed.
  
End ProjectionPatterns.

(* -------------------------------------------------------------- *)
(* The Projection Problem: Recursive composition                 *)
(* -------------------------------------------------------------- *)

Section ProjectionProblem.
  
  (* Complex sentences with nested presupposition triggers *)
  (* "If the King of France is bald, then John knows that Mary left" *)
  
  Definition complex_conditional := 
    presup_conditional 
      (assertion king_of_france_is_bald)
      john_knows_mary_left.
  
  (* The presupposition becomes: *)
  (* "If the King of France is bald, then Mary left" *)
  (* BUT we also need: "France has a king" *)
  (* This shows the complexity of projection! *)
  
  Lemma complex_presupposition :
    presupposition complex_conditional = 
      (assertion king_of_france_is_bald -> left mary).
  Proof.
    unfold complex_conditional, presup_conditional. simpl. reflexivity.
  Qed.
  
  (* But this misses the definite description presupposition! *)
  (* Real projection needs to collect ALL presuppositions *)
  
  (* Better approach: collect all presuppositions *)
  Definition collect_presuppositions (p1 p2 : PresupProp) : Prop :=
    presupposition p1 /\ presupposition p2.
  
  (* Full complex sentence with all presuppositions *)
  Definition complex_conditional_full : PresupProp := mkPresup
    (assertion king_of_france_is_bald -> assertion john_knows_mary_left)
    (presupposition king_of_france_is_bald /\ 
     (assertion king_of_france_is_bald -> presupposition john_knows_mary_left)).
  
End ProjectionProblem.

(* -------------------------------------------------------------- *)
(* Summary: The Projection Calculus                              *)
(* -------------------------------------------------------------- *)

(* We've formalized:
   1. Basic presuppositional expressions
   2. Projection through negation (holes) 
   3. Projection through conditionals (filters)
   4. Projection through quantification
   5. Context and accommodation
   6. Holes vs plugs vs filters
   7. The compositional projection problem
   
   This provides a foundation for modeling how presuppositions 
   behave in complex linguistic environments! *)
