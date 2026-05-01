"""FraCaS loader module.

Two views of the same XML:
  - load_rich(): phase-1 schema, keeps premises as a list and section metadata.
  - load_flat(): phase-2 schema, premises joined into a single string.

Both call the same underlying parser; load_flat is just a projection of load_rich.
"""

import xml.etree.ElementTree as ET
from pathlib import Path


SECTIONS = {
    1: "Quantifiers (generalized quantifiers, scope, monotonicity)",
    2: "Plurals (collective/distributive readings, plural quantification)",
    3: "Anaphora (pronoun resolution, donkey sentences, accessibility)",
    4: "Ellipsis (VP ellipsis, sluicing, antecedent selection)",
    5: "Adjectives (intersective, subsective, privative, intensional)",
    6: "Comparatives (degree semantics, scalar implicature)",
    7: "Temporal (tense, aspect, temporal adverbials)",
    8: "Verbs (aktionsart, event structure, argument alternations)",
    9: "Attitudes (propositional attitudes, de re/de dicto, opacity)",
}

_SECTION_BOUNDARIES = [
    (1, 80, 1), (81, 113, 2), (114, 141, 3), (142, 196, 4),
    (197, 219, 5), (220, 250, 6), (251, 325, 7), (326, 333, 8),
    (334, 346, 9),
]

_GOLD_MAP = {"yes": "yes", "no": "no", "unknown": "unknown", "undef": "unknown"}


def get_section(pid: int) -> int:
    """Map FraCaS problem ID to section number (0 if out of range)."""
    for low, high, sec in _SECTION_BOUNDARIES:
        if low <= pid <= high:
            return sec
    return 0


def load_rich(xml_path) -> list[dict]:
    """Phase-1 schema. Returns problems as:
        {id:int, section:int, section_name:str,
         premises:list[str], hypothesis:str, gold:'yes'|'no'|'unknown'}
    """
    tree = ET.parse(Path(xml_path))
    root = tree.getroot()
    problems = []

    for problem in root.iter("problem"):
        raw_pid = problem.get("id", "")
        gold = _GOLD_MAP.get(problem.get("fracas_answer", "").strip().lower())
        if gold is None:
            continue

        pid = int(raw_pid) if raw_pid.isdigit() else 0
        section = get_section(pid)

        premises = [
            "".join(p.itertext()).strip()
            for p in problem.findall(".//p")
            if "".join(p.itertext()).strip()
        ]

        h_elem = problem.find(".//h")
        hypothesis = "".join(h_elem.itertext()).strip() if h_elem is not None else ""

        if not premises or not hypothesis:
            continue

        problems.append({
            "id": pid,
            "section": section,
            "section_name": SECTIONS.get(section, f"Section {section}"),
            "premises": premises,
            "hypothesis": hypothesis,
            "gold": gold,
        })

    return problems


def _to_flat(rich_item: dict) -> dict:
    return {
        "id": f"fracas-{rich_item['id']}",
        "premise": " ".join(rich_item["premises"]),
        "hypothesis": rich_item["hypothesis"],
        "gold": rich_item["gold"],
    }


def load_flat(xml_path) -> list[dict]:
    """Phase-2 schema. Returns problems as:
        {id:'fracas-N', premise:str, hypothesis:str, gold:str}
    """
    return [_to_flat(r) for r in load_rich(xml_path)]
