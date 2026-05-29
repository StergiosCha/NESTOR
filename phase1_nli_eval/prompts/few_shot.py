"""Few-shot prompt bodies.

{examples} placeholder filled at runtime in the prompt language's surface label vocabulary.
Each body ends with a JSON-output instruction adapted to language and schema.
Field names (answer/explanation, απάντηση/εξήγηση) match parse_response's aliases.
Literal JSON braces are doubled so str.format leaves them intact.
"""

EN_SINGLE = """Given the premise(s) and hypothesis below, determine whether the hypothesis follows from the premise(s).

Premise(s): {premise}
Hypothesis: {hypothesis}

Use the following examples as guidance:
{examples}


Answer: Yes, No, or Unknown.
Explanation: In 1–3 sentences, explain why this answer is correct. Identify the specific linguistic or logical mechanism involved.

Respond with valid JSON only, in exactly this form: {{"answer": <label>, "explanation": "<1–3 sentences>"}}"""

EN_MULTI = """Given the premise(s) and hypothesis below, determine whether the hypothesis follows from the premise(s). More than one answer may apply.

Premise(s): {premise}
Hypothesis: {hypothesis}

Use the following examples as guidance:
{examples}

Answer: Entailment, Contradiction, Unknown. Give every answer that applies.
Explanation: In 1–3 sentences, explain why each chosen answer is correct. Identify the specific linguistic or logical mechanism involved.

Respond with valid JSON only, in exactly this form: {{"answer": [<label>, ...], "explanation": "<1–3 sentences>"}}"""

EL_SINGLE = """Δεδομένης/ων της/των προκείμενης/ων και της υπόθεσης παρακάτω, όρισε αν η υπόθεση ακολουθεί από την/τις προκείμενη/ες.

Προκείμενη/ες: {premise}
Υπόθεση: {hypothesis}

Χρησιμοποίησε τα ακόλουθα παραδείγματα ως οδηγό:
{examples}

Απάντηση: Ναι, Όχι, ή Άγνωστο.
Εξήγηση: Σε 1–3 προτάσεις, εξήγησε γιατί είναι σωστή αυτή η απάντηση. Όρισε τον συγκεκριμένο γλωσσικό ή λογικό μηχανισμό ο οποίος εμπλέκεται.

Απάντησε μόνο με έγκυρο JSON, ακριβώς σε αυτή τη μορφή: {{"απάντηση": <ετικέτα>, "εξήγηση": "<1–3 προτάσεις>"}}"""

EL_MULTI = """Δεδομένης/ων της/των προκείμενης/ων και της υπόθεσης παρακάτω, όρισε αν η υπόθεση ακολουθεί από την/τις προκείμενη/ες. Είναι δυνατόν να υπάρχουν περισσότερες από μία σωστές απαντήσεις.

Προκείμενη/ες: {premise}
Υπόθεση: {hypothesis}

Χρησιμοποίησε τα ακόλουθα παραδείγματα ως οδηγό:
{examples}

Απάντηση: Συνεπαγωγή, Αντίφαση, Ουδέτερο. Δώσε όλες τις πιθανές απαντήσεις.
Εξήγηση: Σε 1–3 προτάσεις, εξήγησε γιατί είναι σωστή/ες αυτή/ες η/οι απάντηση/ες. Όρισε τον συγκεκριμένο γλωσσικό ή λογικό μηχανισμό ο οποίος εμπλέκεται.

Απάντησε μόνο με έγκυρο JSON, ακριβώς σε αυτή τη μορφή: {{"απάντηση": [<ετικέτα>, ...], "εξήγηση": "<1–3 προτάσεις>"}}"""
