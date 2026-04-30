 Require Import Set_theoretic_Defs.

Definition ER:= fun P:(e->Prop)=>  fun Q:(e->Prop)=> exists x: e,In_s  (intersection P  Q) x.
Set Implicit Arguments. 
Definition INT:= fun P:(e->Prop)->Prop=>  fun Q:(e->Prop)->Prop=> fun X:(e->Prop)=>  P(X) /\ Q (X).

Definition and:=INT.
Parameter man woman: e->Prop.
Definition Man:= fun x:e=> man x.
Definition Woman:= fun x:e=>  woman x.

(**some type checking**)
Check ER man.
Check INT (ER woman).
Check ER woman. 
Check and(ER man)(ER woman).

Definition MIN:= fun Q: (e->Prop)->Prop=> fun P: (e->Prop)=> In Q P/\ forall P':e->Prop, (strict_included P' P)->not(In Q P').
Definition a:= fun P: (e->Prop)->Prop=> fun Q:(e->Prop)->Prop=> exists X, P X /\ Q X.
Parameter date: (e->Prop)->Prop.
Definition dated:= fun P:e->Prop=>  date P.

(**some type checking and evaluaton**)
Check (a(MIN((and(ER Man)(ER Woman))))dated).
Eval cbv in  (a(MIN((and(ER Man)(ER Woman))))dated).
Check dated.


Definition PDIST:= fun (P' P:e->Prop)=>not (Empty_set P)/\ included P P'.
Parameter beer: e->Prop. 
Definition Beer:= fun x=>  beer x.
Parameter have: e->e->Prop. 
Definition  have_a_beer:= fun x:e=>exists y:e, beer(y) /\ have(x)(y). (**introduced some non-compositionality, can be done compositionally easily though**)


Check  (a(MIN((and(ER Man)(ER Woman))))(PDIST(have_a_beer))).
Eval cbv in  (a(MIN((and(ER Man)(ER Woman))))(PDIST(have_a_beer))).
(**Choice closure seems  doable but not as straightforward as the other definitions, needs probably an inductive type**)
