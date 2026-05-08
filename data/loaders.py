"""Dataset loaders for FraCaS, Greek FraCaS and OYXOY. 
Each load_* function returns a list[Sample] under
the unified schema in ~/data/schema.py

Assuming Greek FraCaS follows exact OYXOY-style json format"
"""

import json
from pathlib import Path

from data.schema import Sample


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
