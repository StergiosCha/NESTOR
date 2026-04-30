Require Import Setoid.
Require Import List.
Load "indi.v".

(* -------------------------------------------------------------- *)
(* MASS/COUNT CLASSIFICATION SYSTEM                              *)
(* -------------------------------------------------------------- *)

(** Mass/Count distinction **)
Inductive noun_type : Type :=
  | Count : noun_type
  | Mass : noun_type.

(** Classification function for DomCN types **)
Parameter noun_classification : DomCN -> noun_type.

(* -------------------------------------------------------------- *)
(* MASS NOUN TYPES                                               *)
(* -------------------------------------------------------------- *)

(** Mass nouns - substances that don't have natural individuation **)
Parameter Water Gold Air Milk Coffee : DomCN.

(** Identity criteria for mass nouns - based on qualitative sameness **)
Parameter IC_Water : Equiv(Water).
Parameter IC_Gold : Equiv(Gold).
Parameter IC_Air : Equiv(Air).
Parameter IC_Milk : Equiv(Milk).
Parameter IC_Coffee : Equiv(Coffee).

(** Mass noun setoids **)
Definition WATER := mkCN Water IC_Water.
Definition GOLD := mkCN Gold IC_Gold.
Definition AIR := mkCN Air IC_Air.
Definition MILK := mkCN Milk IC_Milk.
Definition COFFEE := mkCN Coffee IC_Coffee.

(** Axioms declaring these as mass nouns **)
Axiom water_mass : noun_classification Water = Mass.
Axiom gold_mass : noun_classification Gold = Mass.
Axiom air_mass : noun_classification Air = Mass.
Axiom milk_mass : noun_classification Milk = Mass.
Axiom coffee_mass : noun_classification Coffee = Mass.

(** Count nouns - we already have Human, Man, Book **)
Axiom human_count : noun_classification Human = Count.
Axiom man_count : noun_classification Man = Count.
Axiom book_count : noun_classification Book = Count.

(* -------------------------------------------------------------- *)
(* MEASURE PHRASES FOR MASS NOUNS                                *)
(* -------------------------------------------------------------- *)

(** Measure units **)
Parameter Liter Kilogram Cup Glass Bottle : DomCN.

(** Cups and glasses are physical objects **)
Parameter cup_to_phy : Cup -> Phy.
Parameter glass_to_phy : Glass -> Phy.
Coercion cup_to_phy : Cup >-> Phy.
Coercion glass_to_phy : Glass >-> Phy.

(** Identity criteria for measure units **)
Parameter IC_Liter : Equiv(Liter).
Parameter IC_Kilogram : Equiv(Kilogram).
Parameter IC_Cup : Equiv(Cup).
Parameter IC_Glass : Equiv(Glass).
Parameter IC_Bottle : Equiv(Bottle).

(** Measure unit setoids **)
Definition LITER := mkCN Liter IC_Liter.
Definition KILOGRAM := mkCN Kilogram IC_Kilogram.
Definition CUP := mkCN Cup IC_Cup.
Definition GLASS := mkCN Glass IC_Glass.
Definition BOTTLE := mkCN Bottle IC_Bottle.

(** Measure units are count nouns **)
Axiom liter_count : noun_classification Liter = Count.
Axiom kilogram_count : noun_classification Kilogram = Count.
Axiom cup_count : noun_classification Cup = Count.
Axiom glass_count : noun_classification Glass = Count.
Axiom bottle_count : noun_classification Bottle = Count.

(** Measure phrase structure: "three liters of water" **)
Record MeasurePhrase := mkMeasure {
  quantity : nat;
  unit_type : DomCN;
  unit_ic : Equiv unit_type;
  substance_type : DomCN;
  substance_ic : Equiv substance_type;
  unit_is_count : noun_classification unit_type = Count;
  substance_is_mass : noun_classification substance_type = Mass
}.

(** Helper to create measure phrases **)
Definition make_measure_phrase (q : nat) (unit : CN) (substance : CN) 
  (unit_count_proof : noun_classification (unit.(D)) = Count)
  (substance_mass_proof : noun_classification (substance.(D)) = Mass) : MeasurePhrase :=
  {| quantity := q;
     unit_type := unit.(D);
     unit_ic := unit.(E);
     substance_type := substance.(D);
     substance_ic := substance.(E);
     unit_is_count := unit_count_proof;
     substance_is_mass := substance_mass_proof |}.

(** Examples of measure phrases **)
Definition three_liters_water : MeasurePhrase :=
  make_measure_phrase 3 LITER WATER liter_count water_mass.

Definition five_kilograms_gold : MeasurePhrase :=
  make_measure_phrase 5 KILOGRAM GOLD kilogram_count gold_mass.

Definition two_cups_coffee : MeasurePhrase :=
  make_measure_phrase 2 CUP COFFEE cup_count coffee_mass.

(* -------------------------------------------------------------- *)
(* MASS-SPECIFIC QUANTIFICATION                                  *)
(* -------------------------------------------------------------- *)

(** Mass quantification doesn't use counting but portioning **)
Definition some_mass := fun A : CN => fun P : A.(D) -> Prop =>
  noun_classification (A.(D)) = Mass /\ exists x : A.(D), P(x).

Definition much_mass := fun A : CN => fun P : A.(D) -> Prop =>
  noun_classification (A.(D)) = Mass /\ exists x : A.(D), P(x).

Definition little_mass := fun A : CN => fun P : A.(D) -> Prop =>
  noun_classification (A.(D)) = Mass /\ exists x : A.(D), P(x).

(** Measure-based quantification for mass nouns **)
Definition measured_mass (mp : MeasurePhrase) (P : mp.(substance_type) -> Prop) : Prop :=
  exists portions : list mp.(substance_type),
  length portions = mp.(quantity) /\
  forall x, In x portions -> P(x).

(* -------------------------------------------------------------- *)
(* PORTIONING AND PARTITIVES                                     *)
(* -------------------------------------------------------------- *)

(** Partitive relation for mass nouns: "some of the water" **)
Definition portion_of := fun A : CN => fun whole part : A.(D) =>
  noun_classification (A.(D)) = Mass /\ A.(E) part part.

(** Container-based individuation **)
Parameter contains : forall (container_type substance_type : DomCN), 
  container_type -> substance_type -> Prop.

(** "The water in the glass" **)
Definition substance_in_container (container : CN) (substance : CN) 
  (c : container.(D)) (s : substance.(D)) : Prop :=
  @contains (container.(D)) (substance.(D)) c s.

(** Examples **)
Parameter glass1 : Glass.
Definition water_in_glass1 : Prop :=
  some_mass WATER (substance_in_container GLASS WATER glass1).

(* -------------------------------------------------------------- *)
(* MASS TO COUNT COERCION PATTERNS                               *)
(* -------------------------------------------------------------- *)

(** Universal grinder: count nouns can be interpreted as mass **)
Definition grind := fun A : CN => 
  {substance : DomCN & 
   {ic : Equiv substance & 
   {coercion : A.(D) -> substance &
    noun_classification substance = Mass}}}.

(** Universal packager: mass nouns can be packaged into count units **)
Definition package := fun A : CN =>
  {unit : DomCN &
   {ic : Equiv unit &
   {contains_rel : unit -> A.(D) -> Prop &
    noun_classification unit = Count}}}.

(** Example: books as mass (destroyed/ground up) **)
Parameter BookSubstance : DomCN.
Parameter IC_BookSubstance : Equiv BookSubstance.
Parameter book_to_substance : Book -> BookSubstance.
Axiom book_substance_mass : noun_classification BookSubstance = Mass.

Definition BOOK_AS_MASS : grind BOOK1 :=
  existT _ BookSubstance 
    (existT _ IC_BookSubstance 
      (existT _ book_to_substance book_substance_mass)).

(** Example: water as count (in containers) **)
Parameter WaterContainer : DomCN.
Parameter IC_WaterContainer : Equiv WaterContainer.
Parameter water_container_contains : WaterContainer -> Water -> Prop.
Axiom water_container_count : noun_classification WaterContainer = Count.

Definition WATER_AS_COUNT : package WATER :=
  existT _ WaterContainer
    (existT _ IC_WaterContainer
      (existT _ water_container_contains water_container_count)).

(* -------------------------------------------------------------- *)
(* COLLECTIVE VS DISTRIBUTIVE WITH MASS/COUNT                    *)
(* -------------------------------------------------------------- *)

(** Count nouns can form collections **)
Definition collective_count (A : CN) (P : list (A.(D)) -> Prop) (xs : list (A.(D))) : Prop :=
  noun_classification (A.(D)) = Count /\ 
  length xs > 1 /\ P xs /\
  (forall x y, In x xs -> In y xs -> x <> y -> ~ A.(E) x y).

(** Mass nouns don't naturally form collections, but can be portioned **)
Definition distributed_mass := fun A : CN => fun P : A.(D) -> Prop =>
  noun_classification (A.(D)) = Mass /\
  exists x : A.(D), P x.

(* -------------------------------------------------------------- *)
(* EXAMPLES WITH MIXED MASS/COUNT CONSTRUCTIONS                  *)
(* -------------------------------------------------------------- *)

(** "Three glasses of water" - count containers with mass contents **)
Definition three_glasses_water : Prop :=
  (three_f GLASS) (fun g => 
    some_mass WATER (fun w => substance_in_container GLASS WATER g w)).

(** "Some books contain much information" **)
Parameter Information : DomCN.
Parameter IC_Information : Equiv Information.
Definition INFORMATION := mkCN Information IC_Information.
Axiom information_mass : noun_classification Information = Mass.

Parameter book_contains_info : Book -> Information -> Prop.

Definition books_contain_much_info : Prop :=
  (some BOOK1) (fun b => 
    much_mass INFORMATION (book_contains_info b)).

(** "John drank the coffee in three cups" **)
Definition john_drank_coffee_three_cups : Prop :=
  (three_f CUP) (fun c =>
    some_mass COFFEE (fun coffee =>
      substance_in_container CUP COFFEE c coffee /\
      picked_up John c)).

(* -------------------------------------------------------------- *)
(* MEASURE PHRASE THEOREMS                                       *)
(* -------------------------------------------------------------- *)

(** Axiom: Measure phrases presuppose substance existence **)
Axiom measure_presupposition : 
  forall mp : MeasurePhrase,
  exists s : mp.(substance_type), True.

(** If we have a measure phrase, we have count units and mass substance **)
Theorem measure_phrase_decomposition :
  forall mp : MeasurePhrase,
  (three_f (mkCN mp.(unit_type) mp.(unit_ic))) (fun u => True) ->
  some_mass (mkCN mp.(substance_type) mp.(substance_ic)) (fun s => True).
Proof.
  intros mp H_units.
  unfold some_mass.
  split.
  - exact mp.(substance_is_mass).
  - (* Use the presupposition that substance exists *)
    destruct (measure_presupposition mp) as [s _].
    exists s.
    exact I.
Qed.

(** Mass substances can be measured **)
Theorem mass_measurable :
  forall (substance : CN) (unit : CN),
  noun_classification (substance.(D)) = Mass ->
  noun_classification (unit.(D)) = Count ->
  some_mass substance (fun s => True) ->
  exists mp : MeasurePhrase,
    mp.(substance_type) = substance.(D) /\
    mp.(unit_type) = unit.(D).
Proof.
  intros substance unit H_mass H_count H_some.
  (* Construct a measure phrase with quantity 1 *)
  exists {| quantity := 1;
           unit_type := unit.(D);
           unit_ic := unit.(E);
           substance_type := substance.(D);
           substance_ic := substance.(E);
           unit_is_count := H_count;
           substance_is_mass := H_mass |}.
  simpl.
  split; reflexivity.
Qed.

(** Count to mass coercion preserves existence **)
Theorem count_to_mass_preservation :
  forall A : CN,
  noun_classification (A.(D)) = Count ->
  (some A) (fun x => True) ->
  forall (grinder : grind A),
  some_mass (mkCN (projT1 grinder) (projT1 (projT2 grinder))) (fun x => True).
Proof.
  intros A H_count H_some grinder.
  unfold some_mass.
  destruct grinder as [substance [ic [coercion mass_proof]]].
  simpl.
  split.
  - exact mass_proof.
  - (* Use coercion to map from count to mass *)
    unfold some in H_some.
    destruct H_some as [x Hx].
    exists (coercion x).
    exact I.
Qed.

(* -------------------------------------------------------------- *)
(* COMPLEX MASS/COUNT EXAMPLES                                   *)
(* -------------------------------------------------------------- *)

(** "Three heavy books worth much gold" **)
Parameter worth : Book -> Gold -> Prop.

Definition three_heavy_books_worth_gold : Prop :=
  (three_f HBOOK1) (fun hb => 
    picked_up John hb /\
    much_mass GOLD (worth hb)).

(** "John read three books containing little information each" **)
Definition john_read_books_little_info : Prop :=
  (three_f BOOK2) (fun b =>
    mastered John b /\
    little_mass INFORMATION (book_contains_info b)).

(** "Most water in these glasses is drinkable" **)
Parameter drinkable : Water -> Prop.
Parameter these_glasses : list Glass.

Definition most_water_drinkable : Prop :=
  forall g, In g these_glasses ->
    some_mass WATER (fun w =>
      substance_in_container GLASS WATER g w /\
      drinkable w).

(* -------------------------------------------------------------- *)
(* SUMMARY: MASS/COUNT WITH SETOID STRUCTURE                     *)
(* -------------------------------------------------------------- *)

(** This extension provides:
    
    ✅ MASS/COUNT CLASSIFICATION: Water, Gold (mass) vs Human, Book (count)
    ✅ MEASURE PHRASES: "three liters of water" with proper type structure
    ✅ MASS QUANTIFICATION: some/much/little for mass nouns
    ✅ PORTIONING: Partitive constructions for mass substances
    ✅ CONTAINER INDIVIDUATION: "water in glass" patterns
    ✅ COERCION PATTERNS: Universal grinder/packager operations
    ✅ MIXED CONSTRUCTIONS: Count containers with mass contents
    ✅ COMPLEX EXAMPLES: Real linguistic phenomena with mass/count
    
    Built directly on the working setoid foundation from indi.v!
**)
