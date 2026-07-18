"""Judge-stats shell: per-file scored-item count and mean scores.

To be extended.
"""

from __future__ import annotations

import json
from pathlib import Path

CRITERIA = ("phenomenon_id", "soundness", "consistency")

SCORES_DIR = Path(__file__).resolve().parent.parent / "judge_scores"
STATS_PATH = SCORES_DIR / "judge_stats.json"


def discover_score_files(scores_dir: Path = SCORES_DIR) -> list[Path]:
    return sorted(scores_dir.glob("*/*__scores.json"))


def _mean(values: list[int]) -> float | None:
    return sum(values) / len(values) if values else None


def summarize_file(path: Path) -> dict:
    """Scored-item count, mean total, and mean per criterion for one score file."""
    data = json.loads(path.read_text(encoding="utf-8"))
    scores = data.get("scores", [])
    metadata = data.get("metadata", {})
    return {
        "file": path.name,
        "dataset": metadata.get("dataset"),
        "model": metadata.get("model"),
        "technique": metadata.get("technique"),
        "language": metadata.get("language"),
        "judge_model": metadata.get("judge_model"),
        "scored_count": len(scores),
        "mean_total": _mean([s["total"] for s in scores]),
        "mean_phenomenon_id": _mean([s["phenomenon_id"] for s in scores]),
        "mean_soundness": _mean([s["soundness"] for s in scores]),
        "mean_consistency": _mean([s["consistency"] for s in scores]),
    }


def build_stats(scores_dir: Path = SCORES_DIR) -> dict:
    return {"files": [summarize_file(p) for p in discover_score_files(scores_dir)]}


def save_stats(stats: dict, path: Path = STATS_PATH) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(stats, ensure_ascii=False, indent=2), encoding="utf-8")
    return path


def main() -> int:
    stats = build_stats()
    path = save_stats(stats)
    print(f"[judge_stats] {len(stats['files'])} file(s) -> {path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
