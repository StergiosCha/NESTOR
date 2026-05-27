"""Phase 1 prompt assembly.

One template module per technique (zero_shot, few_shot, cot), each exposing
`EN_SINGLE`,MULTI`, `EL_SINGLE`, `EL_MULTI`. 
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
) -> list[dict]:
    template = select_template(technique, language, multilabel)
    body = template.format(
        premise=sample.premise,
        hypothesis=sample.hypothesis,
        examples=format_examples(examples or [], language, multilabel),
    )
    return [{"role": "user", "content": body}]
