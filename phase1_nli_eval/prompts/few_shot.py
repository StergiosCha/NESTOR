"""Few-shot prompt bodies 
{examples} placeholder filled at runtime and formatted in the prompt language's surface label vocabulary.
"""

EN_SINGLE = """Given the premise(s) and hypothesis below, determine whether the hypothesis follows from the premise(s).

Examples:
{examples}

Premise(s): {premise}
Hypothesis: {hypothesis}

Answer: Yes, No, or Unknown.
Explanation: In 1–3 sentences, explain why this answer is correct. Identify the specific linguistic or logical mechanism involved."""

EN_MULTI = """Given the premise(s) and hypothesis below, determine whether the hypothesis follows from the premise(s). More than one answer may apply.

Examples:
{examples}

Premise(s): {premise}
Hypothesis: {hypothesis}

Answer: Entailment, Contradiction, Unknown. Give every answer that applies.
Explanation: In 1–3 sentences, explain why each chosen answer is correct. Identify the specific linguistic or logical mechanism involved."""

EL_SINGLE = """Δεδομένης/ων της/των προκείμενης/ων και της υπόθεσης παρακάτω, όρισε αν η υπόθεση ακολουθεί από την/τις προκείμενη/ες.

Παραδείγματα:
{examples}

Προκείμενη/ες: {premise}
Υπόθεση: {hypothesis}

Απάντηση: Ναι, Όχι, ή Άγνωστο.
Εξήγηση: Σε 1–3 προτάσεις, εξήγησε γιατί είναι σωστή αυτή η απάντηση. Όρισε τον συγκεκριμένο γλωσσικό ή λογικό μηχανισμό ο οποίος εμπλέκεται."""

EL_MULTI = """Δεδομένης/ων της/των προκείμενης/ων και της υπόθεσης παρακάτω, όρισε αν η υπόθεση ακολουθεί από την/τις προκείμενη/ες. Είναι δυνατόν να υπάρχουν περισσότερες από μία σωστές απαντήσεις.

Παραδείγματα:
{examples}

Προκείμενη/ες: {premise}
Υπόθεση: {hypothesis}

Απάντηση: Συνεπαγωγή, Αντίφαση, Ουδέτερο. Δώσε όλες τις πιθανές απαντήσεις.
Εξήγηση: Σε 1–3 προτάσεις, εξήγησε γιατί είναι σωστή/ες αυτή/ες η/οι απάντηση/ες. Όρισε τον συγκεκριμένο γλωσσικό ή λογικό μηχανισμό ο οποίος εμπλέκεται."""
