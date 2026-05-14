# OYXOY → FraCaS Section Mapping

## FraCaS sections (reference)

1. Generalized Quantifiers
2. Plurals
3. (Nominal) Anaphora
4. Ellipsis
5. Adjectives
6. Comparatives
7. Temporal Reference
8. Verbs
9. Attitudes

---

## Full forced mapping

Every OYXOY leaf tag placed under exactly one FraCaS section. Strained placements flagged with ⚠.

### Lexical Semantics

| OYXOY tag | FraCaS § | Rationale | Confidence |
|---|---|---|---|
| Lexical Entailment → Hyponymy | §1 Generalized Quantifiers | Monotonicity in restrictor/scope (`every dog` ⊨ `every poodle`) | High |
| Lexical Entailment → Hypernymy | §1 Generalized Quantifiers | Same — upward monotonicity | High |
| Lexical Entailment → Synonymy | §8 Verbs | Lexical equivalence is treated in the Verbs section in FraCaS | Medium |
| Lexical Entailment → Antonymy | §8 Verbs | Lexical opposition between verbs/predicates | Medium |
| Lexical Entailment → Meronymy ⚠ | §2 Plurals | Part-whole patterns interface with collective NPs; weakest fit in this column | Low |
| Morphological Modification ⚠ | §5 Adjectives | Degree morphemes (*παρά-*) and α-privative behave like adjectival modifiers/negation | Low |
| Factivity → Factive | §9 Attitudes | Canonical FraCaS placement | High |
| Factivity → Non-Factive | §9 Attitudes | Canonical FraCaS placement | High |
| Symmetry | §8 Verbs | Symmetric predicates are a Verbs phenomenon | High |
| Collectivity | §2 Plurals | Collective vs. distributive is the core of §2 | High |
| Redundancy | §5 Adjectives | Intersective-modifier drop is the prototypical redundancy case | Medium |
| FAO (e.g. *μόνο*) ⚠ | §1 Generalized Quantifiers | Focus-sensitive *only* is handled with GQs in the FraCaS tradition | Low |

### Predicate-Argument Structure

| OYXOY tag | FraCaS § | Rationale | Confidence |
|---|---|---|---|
| Syntactic Ambiguity ⚠ | §5 Adjectives | PP-attachment / modifier-scope ambiguity lives alongside adjectival scope; alternatively §3 | Low |
| Core Arguments | §8 Verbs | Argument-structure changes (transitive/intransitive) are §8 | High |
| Alternations | §8 Verbs | Voice/diathesis alternations are §8 | High |
| Ellipsis | §4 Ellipsis | Direct match | High |
| Anaphora/Coreference | §3 Anaphora | Direct match | High |
| Intersectivity → Intersective | §5 Adjectives | Canonical §5 phenomenon (*Κινέζος*) | High |
| Intersectivity → Non-Intersective | §5 Adjectives | Canonical §5 phenomenon (*επιδέξιος χορευτής*) | High |
| Restrictivity → Restrictive | §3 Anaphora | Relative clauses sit under anaphora in FraCaS; alternatively §5 | Medium |
| Restrictivity → Non-Restrictive | §3 Anaphora | Same | Medium |

### Logic

| OYXOY tag | FraCaS § | Rationale | Confidence |
|---|---|---|---|
| Single Negation | §1 Generalized Quantifiers | Negation as boolean operator on GQs | Medium |
| Multiple Negations | §1 Generalized Quantifiers | Same | Medium |
| Conjunction | §2 Plurals | NP/VP conjunction → collective readings | Medium |
| Disjunction | §1 Generalized Quantifiers | Boolean combinations of GQs | Medium |
| Conditionals ⚠ | §9 Attitudes | Closest analog: hypothetical/intensional contexts; very strained | Low |
| Negative Concord ⚠ | §1 Generalized Quantifiers | NPI/NC items are quantificational, but FraCaS doesn't cover NC (English doesn't have it) | Low |
| Quantification → Universal | §1 Generalized Quantifiers | Direct match | High |
| Quantification → Existential | §1 Generalized Quantifiers | Direct match | High |
| Quantification → Non-Standard | §1 Generalized Quantifiers | Direct match | High |
| Comparatives | §6 Comparatives | Direct match | High |
| Temporals | §7 Temporal Reference | Direct match | High |

### Common Sense / Knowledge

| OYXOY tag | FraCaS § | Rationale | Confidence |
|---|---|---|---|
| Common Sense/Knowledge ⚠ | §9 Attitudes | FraCaS deliberately excludes world knowledge; §9 is the closest neighbor since attitude reports lean on it | Low |

---

## Distribution

| FraCaS § | # of OYXOY tags | Tags |
|---|---|---|
| §1 Generalized Quantifiers | 9 | Hyponymy, Hypernymy, FAO, Single Neg, Multiple Neg, Disjunction, Negative Concord, Universal, Existential, Non-Standard |
| §2 Plurals | 3 | Meronymy, Collectivity, Conjunction |
| §3 Anaphora | 3 | Anaphora/Coreference, Restrictive, Non-Restrictive |
| §4 Ellipsis | 1 | Ellipsis |
| §5 Adjectives | 5 | Morphological Modification, Redundancy, Syntactic Ambiguity, Intersective, Non-Intersective |
| §6 Comparatives | 1 | Comparatives |
| §7 Temporal Reference | 1 | Temporals |
| §8 Verbs | 5 | Synonymy, Antonymy, Symmetry, Core Arguments, Alternations |
| §9 Attitudes | 4 | Factive, Non-Factive, Conditionals, Common Sense |

§1 dominates (~30% of tags) — honest reflection of how much GQ-theoretic monotonicity drives FraCaS reasoning.

---

## Problem cases (low confidence, candidates for random assignment)

These are the placements where no defensible single FraCaS section exists. If you want to randomize, randomize over the **candidate set** listed for each, not over all 9 sections.

| OYXOY tag | Candidate FraCaS sections for random pick | Why no clean fit |
|---|---|---|
| Meronymy | §2, §5, §8 | Part-whole reasoning crosses NP semantics (§2/§5) and verb argument structure (§8); FraCaS has no meronymy phenomena |
| Morphological Modification | §5, §8 | FraCaS is English-centric; Greek productive morphology (*παρά-*, α-privative) maps either to adjectival semantics (§5) or to verbal-degree (§8) |
| FAO (Focus-Associating Operators) | §1, §9 | *Only*/*even* are studied with GQs (§1) but also interact with focus-sensitive attitude contexts (§9) |
| Syntactic Ambiguity | §3, §5 | PP-attachment can resolve to anaphora-like (§3) or modifier-scope (§5); FraCaS treats this only incidentally |
| Conditionals | §1, §9 | FraCaS has no conditional section; both intensionality (§9) and GQ-style universal-over-worlds (§1) are defensible |
| Negative Concord | §1, §8 | NC is absent from English-based FraCaS; tag interfaces with GQ-NPI (§1) and verbal negation (§8) |
| Common Sense/Knowledge | §9, or "any" | Explicitly excluded from FraCaS by design; §9 is closest but uniform random over all 9 sections is also reasonable |

---

## Suggested annotation policy

- **High-confidence mappings**: use the table above directly (no randomization needed).
- **Medium-confidence mappings** (§3 for restrictivity, §5 for redundancy, §8 for synonymy/antonymy, etc.): use the table; if you later find FraCaS-style sub-balancing skews badly, revisit.
- **Low-confidence (⚠) mappings**: either (a) keep the forced placement above for analysis consistency, or (b) randomly assign per-sample from the candidate-set column on the right. Recommend keeping a flag (`forced_mapping: true`) on these so downstream analysis can isolate them.
- **Common Sense / Knowledge**: consider keeping outside the FraCaS taxonomy entirely as an "extra-FraCaS" residual category — this is the cleanest move given FraCaS's design exclusion.
