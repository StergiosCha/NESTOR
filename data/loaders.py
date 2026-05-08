"""Dataset loaders for FraCaS, Greek FraCaS and OYXOY. 
Each load_* function returns a list[Sample] under
the unified schema in ~/data/schema.py

Assuming Greek FraCaS follows exact OYXOY-style json format"
"""

import json
import re
import xml.etree.ElementTree as ET
from pathlib import Path

from data.schema import FRACAS_LABEL_MAP, Sample

_FRACAS_NUMBERING = re.compile(r"^\s*\d+(?:\.\d+)*\s+")


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
            labels=[gold],
            tags=[tag] if tag else [],
        ))

    return samples


def load_json(json_path, source: str) -> list[Sample]:
    raw = json.loads(Path(json_path).read_text(encoding="utf-8"))
    return [
        Sample(
            id=f"{source}-{i:04d}",
            source=source,
            premise=s["premise"],
            hypothesis=s["hypothesis"],
            labels=list(s.get("labels", [])),
            tags=list(s.get("tags", [])),
        )
        for i, s in enumerate(raw["samples"], start=1)
    ]


def load_greek_fracas(json_path) -> list[Sample]:
    return load_json(json_path, "greek-fracas")


def load_oyxoy(json_path) -> list[Sample]:
    return load_json(json_path, "oyxoy")
