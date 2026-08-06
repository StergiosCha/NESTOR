# FOL Pipeline — Decision Cheatsheet

## Phase A: Prover9 P ⊢ H → **Entailment** (exit)
## Phase B: Prover9 P ⊢ ¬H → **Contradiction** (exit)

Αν κανένα proof δε βγει, πάμε MACE4:

## Phase C: MACE4 P ∧ ¬H → found_c
## Phase D: MACE4 P ∧ H → found_d

| found_c | found_d | Label |
|---------|---------|-------|
| model | model | **Unknown** |
| model | no model | Undecided |
| no model | model | Undecided |
| no model | no model | Undecided |

## Γιατί

- **Prover9 αποδεικνύει** (universal) → σίγουρο αποτέλεσμα
- **MACE4 βρίσκει μοντέλο** → σίγουρο ότι κάτι είναι satisfiable
- **MACE4 ΔΕΝ βρίσκει μοντέλο** → δε σημαίνει τίποτα (ίσως δεν χωράει στο domain size)

Unknown = υπάρχει κόσμος που ο P αληθεύει χωρίς H, ΚΑΙ κόσμος που αληθεύει μαζί με H. Άρα ο P δεν αποφασίζει για το H.
