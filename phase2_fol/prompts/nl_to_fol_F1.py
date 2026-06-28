"""F1 prompt template: NL -> FOL with translation conventions (canonical tier).

Placeholders: {premise}, {hypothesis}, {condition_block}.
"""

TEMPLATE = """Translate the following premise and hypothesis into first-order logic formulas.

Premise: {premise}
Hypothesis: {hypothesis}

{condition_block}Use Prover9 syntax:
- Universal: all x (P(x) -> Q(x))
- Existential: exists x (P(x) & Q(x))
- Implication: ->
- Conjunction: &
- Disjunction: |
- Negation: -
- Biconditional: <->
- Equality: =
- Variables: x, y, z, u, v, w (lowercase)
- Constants: lowercase (john, mary, socrates)
- Predicates: lowercase (cat, run, read)

=== TRANSLATION CONVENTIONS ===

1. "All/Every A are/is B"       -> all x (A(x) -> B(x))
2. "Some/A few A are B"         -> exists x (A(x) & B(x))
3. "No A is B"                  -> all x (A(x) -> -B(x))
4. "A is B" (proper name)       -> B(a)  where a is a constant
5. Bare plurals / generics      -> treat as universal: all x (A(x) -> B(x))
6. Definite "the A"             -> exists x (A(x) & all y (A(y) -> y = x) & ...)
7. Transitive verbs             -> 2-place predicates: read(x, y)
8. Adjectives                   -> 1-place predicates: tall(x), red(x)
9. Relative clauses             -> conjoin: all x ((man(x) & run(x)) -> ...)
10. "If A then B"               -> translate A as premise, B as separate formula
11. Negation "does not", "isn't" -> use -

=== NON-STANDARD QUANTIFIERS ===

FOL cannot directly express proportional quantifiers like "most", "few",
"many". These need approximation strategies. Use the following rules:

12. "Most A are B"
    Approximate as: more than half, which FOL cannot count.
    Strategy: treat as universal with an exception clause:
    all x (A(x) -> B(x))
    This is an OVER-APPROXIMATION (stronger than "most"). It may cause
    false entailments but is the safest for Prover9.
    Alternative: exists x (A(x) & B(x))
    This is an UNDER-APPROXIMATION (weaker). It may miss entailments.
    Pick one strategy and be consistent across all items.

13. "Few A are B"
    "Few" implies "some but not many". Approximate as:
    exists x (A(x) & B(x)) & -all x (A(x) -> B(x))
    This says: at least one A is B, but not every A is B.

14. "Many A are B"
    Similar to "most". Approximate as:
    exists x (A(x) & B(x))
    This is weak but safe. Cannot express "many" precisely in FOL.

15. "At least two A are B"
    Use distinctness:
    exists x exists y (A(x) & A(y) & B(x) & B(y) & -(x = y))

16. "At most one A is B"
    all x all y ((A(x) & B(x) & A(y) & B(y)) -> x = y)

17. "Exactly one A is B"
    exists x (A(x) & B(x) & all y ((A(y) & B(y)) -> y = x))

18. "Both A and B"
    Treat "both" as universal over a known pair:
    all x ((x = a | x = b) -> P(x))
    where a, b are the two entities in context.

=== PASSIVES AND COMPARATIVES ===

19. Passives: same predicate, swap argument order.
    "The book was read by John"  -> read(john, book1)
    Same as "John read the book". Do not create a separate passive predicate.

20. Comparatives: use a 2-place relation.
    "John is taller than Mary"   -> taller(john, mary)
    "A is bigger than B"         -> bigger(a, b)
    For the comparative adjective, create a 2-place predicate (taller, bigger,
    older, etc.). Do NOT try to model degrees.

21. Superlatives: combine comparative with universal.
    "John is the tallest man"
    -> man(john) & all x ((man(x) & -(x = john)) -> taller(john, x))

=== TEMPORAL EXPRESSIONS ===

22. FOL has no built-in time. For simple tense, ignore it:
    "John ran"    -> run(john)     (same as "John runs")
    "John will run" -> run(john)

    For items where tense matters (FraCaS Section 7), add a time argument:
    "John ran"       -> exists t (run(john, t) & past(t))
    "John is running" -> exists t (run(john, t) & present(t))
    Only use this when the entailment depends on tense. Otherwise ignore tense.

=== CONSISTENCY RULES ===

- Use ONE predicate name per concept across all premises and hypothesis.
  GOOD: man(x) in premise, man(x) in hypothesis
  BAD:  man(x) in premise, male(x) in hypothesis
- Predicate arity must be consistent: if love(x,y) in one formula, always love(x,y).
- Constants for named entities: john, mary, bill (not j, m, b).
- Multi-premise items: all premises share the same vocabulary.
- Adjective + noun: use conjunction, not a compound predicate.
  GOOD: tall(x) & man(x)
  BAD:  tall_man(x)

=== EXAMPLES ===

Example 1 (entailment, universal to existential):
  Premise: "All cats are animals"
  Hypothesis: "Some cats are animals"
  Premises:
  all x (cat(x) -> animal(x))
  Hypothesis:
  exists x (cat(x) & animal(x))

Example 2 (contradiction):
  Premise: "No dog is a cat"
  Hypothesis: "Some dog is a cat"
  Premises:
  all x (dog(x) -> -cat(x))
  Hypothesis:
  exists x (dog(x) & cat(x))

Example 3 (multi-premise chain):
  Premises: "Every European is a person. Every Italian is a European. John is Italian."
  Hypothesis: "John is a person"
  Premises:
  all x (european(x) -> person(x))
  all x (italian(x) -> european(x))
  italian(john)
  Hypothesis:
  person(john)

Example 4 (at least two):
  Premise: "At least two students passed the exam"
  Hypothesis: "Some student passed the exam"
  Premises:
  exists x exists y (student(x) & student(y) & passed(x) & passed(y) & -(x = y))
  Hypothesis:
  exists x (student(x) & passed(x))

Example 5 (comparative):
  Premise: "John is taller than Mary. Mary is taller than Bill."
  Hypothesis: "John is taller than Bill"
  Premises:
  taller(john, mary)
  taller(mary, bill)
  all x all y all z ((taller(x, y) & taller(y, z)) -> taller(x, z))
  Hypothesis:
  taller(john, bill)
  Note: you need the transitivity axiom as an extra premise, otherwise
  Prover9 cannot chain the two comparisons.

Example 6 (most, approximated as universal):
  Premise: "Most students study hard"
  Hypothesis: "Some students study hard"
  Premises:
  all x (student(x) -> study_hard(x))
  Hypothesis:
  exists x (student(x) & study_hard(x))
  Note: "most" is approximated as "all" (rule 12). This makes the
  entailment provable, which is correct (most implies some).

Example 7 (definite description):
  Premise: "The cat sat on the mat"
  Hypothesis: "A cat sat on the mat"
  Premises:
  exists x (cat(x) & all y (cat(y) -> y = x) & sat_on(x, mat1))
  Hypothesis:
  exists x (cat(x) & sat_on(x, mat1))

Example 8 (neutral / unknown):
  Premise: "John is a student"
  Hypothesis: "John is a good student"
  Premises:
  student(john)
  Hypothesis:
  student(john) & good(john)
  Note: this is NOT provable. Being a student does not mean being good.
  Prover9 will not find a proof. MACE4 will find a countermodel.

=== END ===

Output format (exactly):
Premises:
<one formula per line>
Hypothesis:
<single formula>

No commentary, no explanation, no natural language.
"""
