NESTOR Phase 2: NeSy Sub-team Briefing

You have a working skill (nli-fol-prover) that wraps Prover9, Mace4, and E Prover and can translate simple English sentences to FOL via an LLM. Think of it as plumbing — it shows you how to call the provers, parse their output, detect proofs vs countermodels, and run experiments across multiple LLMs. Use it as infrastructure. Do not treat it as the system.

What you need to build on top of it:

The FraCaS test suite has multi-premise items (sometimes 3-4 premises chaining together), not just single P/H pairs. The translation prompt must handle this — the LLM needs to produce a consistent set of FOL formulas where predicate names, variable conventions, and ontological commitments are shared across all premises and the hypothesis. This is where one-shot translation breaks. When the LLM translates P1 as using "person(x)" and P2 as using "human(x)" for the same concept, the prover sees them as unrelated and fails. Your prompt engineering has to enforce consistency, and your verification loop has to catch and fix these alignment failures.

OYXOY adds Greek, common-sense reasoning, and items where pure formalisation of the premises is not enough — you need background knowledge. This is where the Valentino condition comes in: instead of formalising P and H directly, you formalise the explanation E that justifies why P entails H, then prove E→H. The system needs to handle both paths (direct formalisation and explanation-mediated formalisation) and know when to try which.

The verification loop (k=3) is the core contribution. When Prover9 returns an error or Mace4 finds a trivial countermodel (e.g., empty domain), feed the prover's output back to the LLM with a structured error message and ask it to revise the formalisation. This is not generic self-refinement — the feedback comes from a sound formal system, which makes it trustworthy in a way that LLM self-critique is not. Read the Self-Debug paper (B1) for the pattern, but note that our feedback is semantically richer than compiler errors: a countermodel tells you exactly which interpretation breaks the proof.

The Coq thing is a different beast. We need a parallel pipeline with the same interface but targeting Coq/MTT instead of FOL. The coq_foundations/ library gives you the type-theoretic infrastructure (common nouns as types, adjectives as dependent types, quantifiers as Pi/Sigma types). Your LLM prompt is fundamentally different from the FOL prompt because you are generating typed terms, not untyped formulas, and coqc gives you type errors, not just "proof not found." The verification loop feedback is therefore richer. Whether the FOL and Coq pipelines should communicate (Q3 in the work plan) — start independent, compare results, decide later.

The experiment.py script runs any number of LLMs on any JSONL test set. Extend it to support multi-premise items, Greek input, the Valentino condition path, and Coq as a prover backend alongside Prover9/Mace4. The 2×2 matrix (FOL vs Coq × direct vs Valentino) on FraCaS Section 1 is your proof of concept — get that working first.

These are all things that will come up in formalisation and we need to discuss them. 
