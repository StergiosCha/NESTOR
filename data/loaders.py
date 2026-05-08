import json
from pathlib import Path

from data.schema import Sample


def load_greek_fracas(json_path) -> list[Sample]:
    raw = json.loads(Path(json_path).read_text(encoding="utf-8"))
    return [
        Sample(
            id=f"greek-fracas-{i:04d}",
            source="greek-fracas",
            premise=s["premise"],
            hypothesis=s["hypothesis"],
            labels=list(s.get("labels", [])),
            tags=list(s.get("tags", [])),
        )
        for i, s in enumerate(raw["samples"], start=1)
    ]
