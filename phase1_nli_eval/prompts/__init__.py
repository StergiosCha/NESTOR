"""Phase 1 prompt assembly.

One template module per technique (zero_shot, few_shot, cot), each exposing
`EN_SINGLE`,MULTI`, `EL_SINGLE`, `EL_MULTI`. 
"""

from __future__ import annotations

import zlib
import random
from data.schema import LABELS, Sample
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
    "en": ("Example", "Premise(s)", "Hypothesis", "Answer"),
    "el": ("Παράδειγμα", "Προκείμενη/ες", "Υπόθεση", "Απάντηση"),
}

def select_template(technique: str, language: str, multilabel: bool) -> str:
    module = _TEMPLATES[technique]
    suffix = "MULTI" if multilabel else "SINGLE"
    return getattr(module, f"{language.upper()}_{suffix}")


def seed(sample_id: str) -> int:
    """Returns a stable, reproducible integer seed for sample_id"""
    return zlib.crc32(sample_id.encode("utf-8"))


def select_examples(sample: Sample, pool: list[Sample], k: int = 3) -> list[Sample]:
    """Pick up to k few-shot examples from the same-dataset `pool`.

    Candidates sharing >=1 fracas_section with the query form the pool; 
    an empty query-section list drops the section constraint (whole-pool draw). 
    We take one example per still-uncovered label: a single-label exemple covers one label,
    a multilabel example covers all of its labels at once.
    Deterministic per query via a stable seed on sample.id.
    """
    rng = random.Random(seed(sample.id))
    candidates = [s for s in pool if s.id != sample.id]
    if not candidates:
        return []

    if sample.fracas_sections:
        query_sections = set(sample.fracas_sections)
        matched = [s for s in candidates if query_sections.intersection(s.fracas_sections)]
    else:
        matched = candidates
    if not matched:
        return []

    chosen: list[Sample] = []
    taken: set[str] = set()
    covered: set[str] = set()
    for label in LABELS:
        if label in covered or len(chosen) >= k:
            continue
        havers = [s for s in matched if label in s.labels and s.id not in taken]
        if havers:
            pick = rng.choice(havers)
            chosen.append(pick)
            taken.add(pick.id)
            covered.update(pick.labels)

    if len(chosen) < k:
        leftovers = [s for s in matched if s.id not in taken]
        rng.shuffle(leftovers)
        chosen.extend(leftovers[: k - len(chosen)])

    return chosen


def format_examples(examples: list[Sample], language: str, multilabel: bool) -> str:
    surface = _CANONICAL_TO_SURFACE[(language, multilabel)]
    example_h, premise_h, hypothesis_h, answer_h = _EXAMPLE_HEADINGS[language]
    blocks = []
    for i, e in enumerate(examples, 1):
        rendered_labels = ", ".join(surface.get(lbl, lbl) for lbl in e.labels)
        blocks.append(
            f"--- {example_h} {i} ---\n"
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
