"""Phase 1 prompt assembly.

One template module per technique (zero_shot, few_shot, cot), each exposing
`EN_SINGLE`, `EN_MULTI`, `EL_SINGLE`, `EL_MULTI`. `build_prompt` selects the
right template from (technique, language, sample.multilabel), formats it, and
appends a one-line JSON fallback instruction only when the model's provider
does NOT support a native JSON-schema response_format.
"""

from __future__ import annotations

import random
from data.schema import Sample
from phase1_nli_eval.prompts import cot, few_shot, zero_shot

_TEMPLATES = {"zero-shot": zero_shot, "few-shot": few_shot, "cot": cot}

# Canonical-to-surface label, keyed by (language, multilabel). Used to format
# few-shot exemples in the prompt's own surface vocabulary so the example
# Answer:/Απάντηση: lines match the instruction the LLM is given.
_CANONICAL_TO_SURFACE = {
    ("en", False): {"Entailment": "Yes", "Contradiction": "No", "Unknown": "Unknown"},
    ("en", True):  {"Entailment": "Entailment", "Contradiction": "Contradiction", "Unknown": "Unknown"},
    ("el", False): {"Entailment": "Ναι", "Contradiction": "Όχι", "Unknown": "Άγνωστο"},
    ("el", True):  {"Entailment": "Συνεπαγωγή", "Contradiction": "Αντίφαση", "Unknown": "Ουδέτερο"},
}

# Field headings used when formatting few-shot exemples, per language.
_EXAMPLE_HEADINGS = {
    "en": ("Premise(s)", "Hypothesis", "Answer"),
    "el": ("Προκείμενη/ες", "Υπόθεση", "Απάντηση"),
}

# One-line JSON fallback appended only when the provider has no native json_schema response_format. 
JSON_INSTRUCTION = {
    "en": 'Respond with a JSON object only: {"answer": <label or list of labels>, "explanation": "<1–3 sentences>"}.',
    "el": 'Απάντησε μόνο με ένα JSON αντικείμενο: {"απάντηση": <ετικέτα ή λίστα ετικετών>, "εξήγηση": "<1–3 προτάσεις>"}.',
}


def select_template(technique: str, language: str, multilabel: bool) -> str:
    module = _TEMPLATES[technique]
    suffix = "MULTI" if multilabel else "SINGLE"
    return getattr(module, f"{language.upper()}_{suffix}")


def select_examples(sample: Sample, pool: list[Sample], k: int = 3) -> list[Sample]:
    candidates = [s for s in pool if s.id != sample.id]
    if not candidates:
        return []
    return random.sample(candidates, min(k, len(candidates)))


def format_examples(examples: list[Sample], language: str, multilabel: bool) -> str:
    surface = _CANONICAL_TO_SURFACE[(language, multilabel)]
    premise_h, hypothesis_h, answer_h = _EXAMPLE_HEADINGS[language]
    blocks = []
    for e in examples:
        rendered_labels = ", ".join(surface.get(lbl, lbl) for lbl in e.labels)
        blocks.append(
            f"{premise_h}: {e.premise}\n"
            f"{hypothesis_h}: {e.hypothesis}\n"
            f"{answer_h}: {rendered_labels}"
        )
    return "\n\n".join(blocks)


def build_prompt(
    sample: Sample,
    technique: str,
    language: str,
    multilabel: bool,
    examples: list[Sample] | None = None,
    native_json_schema: bool = False,
) -> list[dict]:

    template = select_template(technique, language, multilabel)
    body = template.format(
        premise=sample.premise,
        hypothesis=sample.hypothesis,
        examples=format_examples(examples or [], language, multilabel),
    )
    if not native_json_schema:
        body = f"{body}\n\n{JSON_INSTRUCTION[language]}"
    return [{"role": "user", "content": body}]
