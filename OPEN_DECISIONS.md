# NESTOR NeSy — Open Decisions

Things that need to be decided and built. Discuss as a team, then do them.

---

## 1. Few-shot examples for FOL/Coq translation

Current prompts are zero-shot. Should we give the LLM example NL→FOL and NL→Coq translations? We have a mapping from OYXOY categories to FraCaS sections (9 sections). Plan: 3 examples per section, selected by category match. Contested categories (Meronymy, Redundancy, Syntactic Ambiguity) get randomly assigned to one of their possible sections each run.

**Decision:** Zero-shot vs few-shot? If few-shot, who writes the 27 gold examples?

---

## 2. Blind mode (C1) for Coq

FOL pipeline already works blind — Prover9 proves or MACE4 finds countermodel. Coq doesn't. You need to build it: try `P → H` (entailment theorem) and `P → ¬H` (contradiction theorem), see which compiles. If neither: unknown.

**Who:** Coq sub-team. This is your main Week 2 task.

---

## 3. C2 condition (Phase 1 predictions)

C2 feeds the LLM's own Phase 1 prediction as the label for formalisation. Not implemented. Needs: load Phase 1 results JSON, match by item ID, pass predicted label to the pipeline.

**Who:** Either sub-team. Add `--condition c1/c2/c3` flag to both pipelines.

---

## 4. Greek data

Pipelines currently only handle English FraCaS XML. Greek FraCaS and OYXOY are JSON with tags instead of sections. Need a loader that reads `data/greek_fracas/greek_fracas.json` and `data/oyxoy/OYXOY.json` and produces the same item format the pipelines expect.

**Who:** Whoever gets to it first. Small task.

---

## 5. Valentino approach

`--approach valentino` exists in the Coq pipeline but is untested. It formalises the LLM's natural language explanation E, not P and H directly. Try it on 5 items and see if it produces better Coq.

**Who:** Coq sub-team, Week 3.

---

## 6. Model comparison

Available: gpt-4o, deepseek-r1, llama-70b, llama-8b, krikri-8b. API calls cost money. Plan: start everything with gpt-4o. Once pipelines are stable, run one batch each with deepseek-r1 and llama-70b for comparison.

**Rule:** Do not run more than 50 items per model without asking Stergios.

---

## 7. Verification loop: k=1 vs k=3

Default is k=3 retries. Does retrying help? Run the same batch with `MAX_RETRIES=1` and `MAX_RETRIES=3`, compare accuracy and compilation rates.

**Who:** Both sub-teams, Week 3.

---

## 8. The 2×2 matrix (Phase 3)

Final deliverable: FOL success/fail × Coq success/fail on the same items. Where do they agree? Where does one succeed and the other fails? Why? This is the paper's main result table.

**Who:** Everyone, Week 4. Requires both pipelines working on the same dataset first.

---

## Timeline

| Week | FOL sub-team | Coq sub-team |
|------|-------------|-------------|
| 1 | Run demo, read papers, discuss Q1-Q5 | Run demo, read papers, discuss Q1-Q5 |
| 2 | Hand-test 5 items Section 1, fix parsing | Hand-test 5 items Section 1, build C1 blind mode |
| 3 | Sections 1-5, test k=1 vs k=3 | Sections 1-3, test Valentino, implement C2 |
| 4 | Full run, error analysis, write-up | Full run, error analysis, write-up |
