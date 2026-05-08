"""Unified Sample schema shared by all NESTOR dataset loaders."""

from dataclasses import dataclass, field

LABELS = ("Entailment", "Contradiction", "Unknown")
SOURCES = ("fracas", "greek-fracas", "oyxoy")

FRACAS_LABEL_MAP = {
    "yes": "Entailment",
    "no": "Contradiction",
    "unknown": "Unknown",
    "undef": "Unknown",
}


@dataclass(frozen=True)
class Sample:
    id: str
    source: str
    premise: str
    hypothesis: str
    labels: list[str] = field(default_factory=list)
    tags: list[str] = field(default_factory=list)
