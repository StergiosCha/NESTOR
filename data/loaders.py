"""Dataset loaders for FraCaS, multilabel FraCaS and OYXOY.
Each load_* function returns a list[Sample] under the unified schema
in data/schema.py.
"""

import json
import re
import xml.etree.ElementTree as ET
from pathlib import Path

from data.schema import (
    FRACAS_LABEL_MAP,
    FRACAS_XML_SECTION_MAP,
    OYXOY_TO_FRACAS_SECTION,
    Sample,
)

_FRACAS_NUMBERING = re.compile(r"^\s*\d+(?:\.\d+)*\s+")


def _fracas_sections_from_tags(tags) -> list[str]:
    seen, out = set(), []
    for t in tags:
        sec = OYXOY_TO_FRACAS_SECTION.get(t)
        if sec is not None and sec not in seen:
            seen.add(sec)
            out.append(sec)
    return out


def load_fracas(xml_path) -> list[Sample]:
    root = ET.parse(Path(xml_path)).getroot()
    section = subsection = ""
    samples: list[Sample] = []

    for elem in root:
        if elem.tag == "comment":
            cls = elem.get("class")
            if cls in ("section", "subsection"):
                title = _FRACAS_NUMBERING.sub("", "".join(elem.itertext()).strip())
                if cls == "section":
                    section, subsection = title, ""
                else:
                    subsection = title
            continue

        if elem.tag != "problem":
            continue

        gold = FRACAS_LABEL_MAP.get(elem.get("fracas_answer", "").strip().lower())
        if gold is None:
            continue

        raw_pid = elem.get("id", "")
        if not raw_pid.isdigit():
            continue
        pid = int(raw_pid)

        premises = [
            "".join(p.itertext()).strip()
            for p in elem.findall(".//p")
            if "".join(p.itertext()).strip()
        ]
        h_elem = elem.find(".//h")
        hypothesis = "".join(h_elem.itertext()).strip() if h_elem is not None else ""
        if not premises or not hypothesis:
            continue

        tag = f"{section}:{subsection}" if subsection else section
        samples.append(Sample(
            id=f"fracas-{pid:04d}",
            source="fracas",
            premise=" ".join(premises),
            hypothesis=hypothesis,
            language="en",
            labels=[gold],
            tags=[tag] if tag else [],
            fracas_sections=[FRACAS_XML_SECTION_MAP[section]] if section else [],
        ))

    return samples


def _load_json(json_path, source: str) -> list[Sample]:
    raw = json.loads(Path(json_path).read_text(encoding="utf-8"))
    out = []
    for i, s in enumerate(raw["samples"], start=1):
        tags = list(s.get("tags", []))
        out.append(Sample(
            id=f"{source}-{i:04d}",
            source=source,
            premise=s["premise"],
            hypothesis=s["hypothesis"],
            language="el",
            labels=list(s.get("labels", [])),
            tags=tags,
            fracas_sections=_fracas_sections_from_tags(tags),
        ))
    return out


def load_multilabel_fracas(json_path) -> list[Sample]:
    return _load_json(json_path, "multilabel-fracas")


def load_oyxoy(json_path) -> list[Sample]:
    return _load_json(json_path, "oyxoy")


def _script_text(elem):
    if elem is None:
        return ""
    sc = elem.find("script")
    return (sc.text or "").strip() if sc is not None else ""


def _load_fracas_greek_xml(xml_path, source: str) -> list[Sample]:
    root = ET.parse(Path(xml_path)).getroot()
    section = subsection = ""
    samples: list[Sample] = []

    for elem in root.iter():
        if elem.tag == "comment":
            cls = elem.get("class")
            if cls in ("section", "subsection"):
                title = _FRACAS_NUMBERING.sub("", "".join(elem.itertext()).strip())
                if cls == "section":
                    section, subsection = title, ""
                else:
                    subsection = title
            continue

        if elem.tag != "problem":
            continue

        gold = FRACAS_LABEL_MAP.get(elem.get("fracas_answer", "").strip().lower())
        if gold is None:
            continue

        raw_pid = elem.get("id", "")
        if not raw_pid.isdigit():
            continue
        pid = int(raw_pid)

        premises = [t for t in (_script_text(p) for p in elem.findall("p")) if t]
        hypothesis = _script_text(elem.find("h"))
        if not premises or not hypothesis:
            continue

        tag = f"{section}:{subsection}" if subsection else section
        samples.append(Sample(
            id=f"fracas-{pid:04d}",
            source=source,
            premise=" ".join(premises),
            hypothesis=hypothesis,
            language="el",
            labels=[gold],
            tags=[tag] if tag else [],
            fracas_sections=[FRACAS_XML_SECTION_MAP[section]] if section else [],
        ))

    return samples


def load_translated_fracas(xml_path) -> list[Sample]:
    return _load_fracas_greek_xml(xml_path, "fracas-translated")


def load_extended_fracas(xml_path) -> list[Sample]:
    return _load_fracas_greek_xml(xml_path, "fracas-extended")
