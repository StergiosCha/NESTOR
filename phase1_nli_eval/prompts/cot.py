"""Chain-of-thought prompt bodies"""

EN_SINGLE = """Given the premise(s) and hypothesis below, determine whether the hypothesis follows from the premise(s). Think step by step before giving your final answer.

Premise(s): {premise}
Hypothesis: {hypothesis}

Answer: Yes, No, or Unknown.
Explanation: Walk through your reasoning step by step in 2–4 sentences, identifying the specific linguistic or logical mechanism, then state the final answer."""

EN_MULTI = """Given the premise(s) and hypothesis below, determine whether the hypothesis follows from the premise(s). More than one answer may apply. Think step by step before giving your final answer.

Premise(s): {premise}
Hypothesis: {hypothesis}

Answer: Entailment, Contradiction, Unknown. Give every answer that applies.
Explanation: Walk through your reasoning step by step in 2–4 sentences, identifying the specific linguistic or logical mechanism for each chosen answer."""

EL_SINGLE = """Δεδομένης/ων της/των προκείμενης/ων και της υπόθεσης παρακάτω, όρισε αν η υπόθεση ακολουθεί από την/τις προκείμενη/ες. Αντί να απαντήσεις απευθείας, σκέψου βήμα προς βήμα πριν δώσεις την τελική απάντηση.

Προκείμενη/ες: {premise}
Υπόθεση: {hypothesis}

Απάντηση: Ναι, Όχι, ή Άγνωστο.
Εξήγηση: Παρουσίασε τη συλλογιστική σου βήμα προς βήμα σε 2–4 προτάσεις, ορίζοντας τον συγκεκριμένο γλωσσικό ή λογικό μηχανισμό, και κατέληξε στην τελική απάντηση."""

EL_MULTI = """Δεδομένης/ων της/των προκείμενης/ων και της υπόθεσης παρακάτω, όρισε αν η υπόθεση ακολουθεί από την/τις προκείμενη/ες. Είναι δυνατόν να υπάρχουν περισσότερες από μία σωστές απαντήσεις. Αντί να απαντήσεις απευθείας, σκέψου βήμα προς βήμα πριν δώσεις την τελική απάντηση.

Προκείμενη/ες: {premise}
Υπόθεση: {hypothesis}

Απάντηση: Συνεπαγωγή, Αντίφαση, Ουδέτερο. Δώσε όλες τις πιθανές απαντήσεις.
Εξήγηση: Παρουσίασε τη συλλογιστική σου βήμα προς βήμα σε 2–4 προτάσεις, ορίζοντας τον συγκεκριμένο γλωσσικό ή λογικό μηχανισμό για κάθε επιλεγμένη απάντηση."""
