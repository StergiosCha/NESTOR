"""Unified Sample schema shared by all NESTOR dataset loaders."""

import json
from dataclasses import dataclass, field

LABELS = ("Entailment", "Contradiction", "Unknown")

# Case-folded surface labels (as emitted by the LLM under the prompts in
# `P1 prompts.md`) → canonical entries of LABELS. parse_response normalises
# every parsed label through this map.
LABEL_SURFACE_MAP = {
    "yes": "Entailment",
    "ναι": "Entailment",
    "entailment": "Entailment",
    "συνεπαγωγή": "Entailment",
    "no": "Contradiction",
    "όχι": "Contradiction",
    "contradiction": "Contradiction",
    "αντίφαση": "Contradiction",
    "unknown": "Unknown",
    "άγνωστο": "Unknown",
    "neutral": "Unknown",
    "ουδέτερο": "Unknown",
}

# case-folded JSON-key aliases for LLM responses
LABEL_KEY_ALIASES = frozenset({"label", "answer", "απάντηση"})
REASONING_KEY_ALIASES = frozenset({"reasoning", "explanation", "εξήγηση"})

SOURCES = (
    "fracas",
    "fracas-translated",
    "fracas-extended",
    "multilabel-fracas",
    "oyxoy",
)

MULTILABEL_SOURCES = frozenset({"multilabel-fracas", "oyxoy"})

LANGUAGES = ("en", "el")

FRACAS_LABEL_MAP = {
    "yes": "Entailment",
    "no": "Contradiction",
    "unknown": "Unknown",
    "undef": "Unknown",
}

FRACAS_SECTIONS = (
    "Generalized Quantifiers",
    "Plurals",
    "Anaphora",
    "Ellipsis",
    "Adjectives",
    "Comparatives",
    "Temporal Reference",
    "Verbs",
    "Attitudes",
)

# Sections as they appear in the original FraCaS XML <comment class="section"> headers.
FRACAS_XML_SECTION_MAP = {
    "GENERALIZED QUANTIFIERS": "Generalized Quantifiers",
    "PLURALS": "Plurals",
    "(NOMINAL) ANAPHORA": "Anaphora",
    "ELLIPSIS": "Ellipsis",
    "ADJECTIVES": "Adjectives",
    "COMPARATIVES": "Comparatives",
    "TEMPORAL REFERENCE": "Temporal Reference",
    "VERBS": "Verbs",
    "ATTITUDES": "Attitudes",
}

# OYXOY tag to canonical FraCaS section mapping.
# Tags absent from this dict contribute nothing to a Sample's fracas_sections.
# Contested tags (no defensible single section) map to a list of candidates;
# the OYXOY loader appends every candidate to the sample's fracas_sections.
OYXOY_TO_FRACAS_SECTION: dict[str, str | list[str]] = {
    # --- FIXED ---
    "Lexical Entailment:Lexical Semantics:Hyponymy": "Generalized Quantifiers",
    "Lexical Entailment:Lexical Semantics:Hypernymy": "Generalized Quantifiers",
    "Lexical Entailment:Lexical Semantics:Synonymy": "Verbs",
    "Lexical Entailment:Lexical Semantics:Antonymy": "Verbs",
    "Lexical Entailment:Morphological Modification": "Adjectives",
    "Lexical Entailment:Factivity:Factive": "Attitudes",
    "Lexical Entailment:Factivity:Non-Factive": "Attitudes",
    "Lexical Entailment:Symmetry/Collectivity": "Plurals",
    "Lexical Entailment:FAO": "Generalized Quantifiers",
    "Predicate-Argument Structure:Core Arguments": "Verbs",
    "Predicate-Argument Structure:Alternations": "Verbs",
    "Predicate-Argument Structure:Ellipsis": "Ellipsis",
    "Predicate-Argument Structure:Anaphora/Coreference": "Anaphora",
    "Predicate-Argument Structure:Intersectivity:Intersective": "Adjectives",
    "Predicate-Argument Structure:Intersectivity:Non-Intersective": "Adjectives",
    "Predicate-Argument Structure:Restrictivity:Restrictive": "Anaphora",
    "Predicate-Argument Structure:Restrictivity:Non-Restrictive": "Anaphora",
    "Logic:Single Negation": "Generalized Quantifiers",
    "Logic:Multiple Negations": "Generalized Quantifiers",
    "Logic:Conjunction": "Plurals",
    "Logic:Disjunction": "Generalized Quantifiers",
    "Logic:Conditionals": "Attitudes",
    "Logic:Negative Concord": "Generalized Quantifiers",
    "Logic:Quantification:Universal": "Generalized Quantifiers",
    "Logic:Quantification:Existential": "Generalized Quantifiers",
    "Logic:Quantification:Non-Standard": "Generalized Quantifiers",
    "Logic:Comparatives": "Comparatives",
    "Logic:Temporal": "Temporal Reference",
    "Common Sense/Knowledge": "Attitudes",
    # --- CONTESTED: randomly pick one at inference time ---
    "Lexical Entailment:Lexical Semantics:Meronymy": ["Plurals", "Generalized Quantifiers"],
    "Lexical Entailment:Redundancy": ["Generalized Quantifiers", "Adjectives", "Temporal Reference"],
    "Predicate-Argument Structure:Syntactic Ambiguity": ["Adjectives", "Generalized Quantifiers"],
}


@dataclass(frozen=True)
class Sample:
    id: str
    source: str
    premise: str
    hypothesis: str
    language: str
    labels: list[str] = field(default_factory=list)
    tags: list[str] = field(default_factory=list)
    fracas_sections: list[str] = field(default_factory=list)

    @property
    def multilabel(self) -> bool:
        return self.source in MULTILABEL_SOURCES


@dataclass(frozen=True)
class Result:
    label: str | list[str]
    reasoning: str


def to_canonical_label(surface: object) -> str | None:
    if not isinstance(surface, str):
        return None
    return LABEL_SURFACE_MAP.get(surface.strip().casefold())


def pick(obj: dict, aliases: frozenset[str]):
    for k, v in obj.items():
        if isinstance(k, str) and k.strip().casefold() in aliases:
            return v
    return None


def dump_entry(sample: "Sample", parsed: "Result | None", raw: str, gold: list[str]) -> dict:
    """Shape one result-file entry. Persisted predicted labels are canonical.

    On parse failure (`parsed is None`) the raw payload is retained, predicted is
    None, reasoning is "" and success=0. On parse success, success is set-equality
    over the canonical predicted-label list vs. `gold`.
    """
    base = {
        "id": sample.id,
        "source": sample.source,
        "language": sample.language,
        "premise": sample.premise,
        "hypothesis": sample.hypothesis,
        "tags": list(sample.tags),
        "fracas_sections": list(sample.fracas_sections),
        "gold": gold,
    }
    if parsed is None:
        return {**base, "predicted": None, "reasoning": "", "raw": raw, "success": 0}
    predicted_list = parsed.label if isinstance(parsed.label, list) else [parsed.label]
    success = 1 if set(predicted_list) == set(gold) else 0
    return {**base, "predicted": parsed.label, "reasoning": parsed.reasoning, "success": success}


def parse_response(raw: str, multilabel: bool) -> Result | None:
    """Parse the model's JSON response into a canonical Result, or None on any mismatch.

    Accepts language-localised JSON keys:
      label key:     "label" | "answer" | "απάντηση" 
      reasoning key: "reasoning" | "explanation" | "εξήγηση"
      
    The label value may be a surface form or already canonical; normalised via LABEL_SURFACE_MAP.
    """
    try:
        obj = json.loads(raw)
    except (json.JSONDecodeError, TypeError):
        return None
    if not isinstance(obj, dict):
        return None
    label = pick(obj, LABEL_KEY_ALIASES)
    reasoning = pick(obj, REASONING_KEY_ALIASES)
    if not isinstance(reasoning, str):
        return None
    if multilabel:
        if not isinstance(label, list) or not label:
            return None
        canonical = [to_canonical_label(x) for x in label]
        if any(c is None for c in canonical):
            return None
        return Result(label=canonical, reasoning=reasoning)  # type: ignore
    canonical = to_canonical_label(label)
    if canonical is None:
        return None
    return Result(label=canonical, reasoning=reasoning)
