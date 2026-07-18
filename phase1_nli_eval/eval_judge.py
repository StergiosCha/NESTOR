"""LLM-as-judge prompt builder, response parser, and score-object builder."""

from __future__ import annotations

import json

from data.schema import _extract_json
from phase1_nli_eval.evaluation.build import LLM_ERROR_PREFIX

PHENOMENON_SCORES = {0, 1, 2}
SOUNDNESS_SCORES = {0, 1, 2}
CONSISTENCY_SCORES = {0, 1}

JUDGE_TEMPLATE = """You are an expert evaluator of Natural Language Inference explanations.

Given:
- Premise(s): {premise}
- Hypothesis: {hypothesis}
- Gold phenomenon tag: {tags}
- Model's predicted label: {predicted}
- Model's explanation: {reasoning}

Score the explanation on three criteria:

1. Phenomenon Identification (0/1/2):
   2 = Explanation correctly identifies the phenomenon matching the gold tag
   1 = Explanation addresses a related but wrong phenomenon
   0 = Explanation is generic, circular, or identifies an irrelevant phenomenon

2. Soundness (0/1/2):
   2 = Reasoning is logically valid and linguistically accurate
   1 = Reasoning contains minor errors but overall direction is correct
   0 = Reasoning is wrong, contradictory, or incoherent

3. Label-Explanation Consistency (0/1):
   1 = The explanation supports the predicted label (regardless of correctness)
   0 = The explanation contradicts or is unrelated to the predicted label

Respond with valid json only in exactly this shape:
{{"phenomenon_id": <0|1|2>, "soundness": <0|1|2>, "consistency": <0|1>, "justification": "<brief>"}}"""


def _as_text(value: object) -> str:
    """Turn a plain value or a list of values into one line of text."""
    if isinstance(value, list):
        return ", ".join(str(v) for v in value)
    return str(value)


def build_judge_prompt(entry: dict) -> list[dict]:
    """Build the (English-only) judge chat messages for one Phase-1 result entry."""
    body = JUDGE_TEMPLATE.format(
        premise=entry.get("premise", ""),
        hypothesis=entry.get("hypothesis", ""),
        tags=_as_text(entry.get("tags", [])),
        predicted=_as_text(entry.get("predicted")),
        reasoning=entry.get("reasoning", ""),
    )
    return [{"role": "user", "content": body}]


def parse_judge_response(raw: str) -> dict | None:
    """Parse the judge's raw text into the three scores + justification, or None if invalid."""
    try:
        obj = json.loads(_extract_json(raw))
    except (json.JSONDecodeError, TypeError):
        return None
    if not isinstance(obj, dict):
        return None
    phenomenon_id = obj.get("phenomenon_id")
    soundness = obj.get("soundness")
    consistency = obj.get("consistency")
    justification = obj.get("justification")
    if not isinstance(phenomenon_id, int) or phenomenon_id not in PHENOMENON_SCORES:
        return None
    if not isinstance(soundness, int) or soundness not in SOUNDNESS_SCORES:
        return None
    if not isinstance(consistency, int) or consistency not in CONSISTENCY_SCORES:
        return None
    if not isinstance(justification, str):
        return None
    return {
        "phenomenon_id": phenomenon_id,
        "soundness": soundness,
        "consistency": consistency,
        "justification": justification,
    }


def build_score_object(entry: dict, parsed: dict) -> dict:
    """Combine a Phase-1 entry with its parsed judge scores into one score object."""
    total = parsed["phenomenon_id"] + parsed["soundness"] + parsed["consistency"]
    return {
        "id": entry.get("id"),
        "gold": entry.get("gold"),
        "predicted": entry.get("predicted"),
        "tags": entry.get("tags"),
        "phenomenon_id": parsed["phenomenon_id"],
        "soundness": parsed["soundness"],
        "consistency": parsed["consistency"],
        "justification": parsed["justification"],
        "total": total,
    }


def is_scorable(entry: dict) -> bool:
    """Whether a Phase-1 entry should be sent to the judge at all."""
    if entry.get("predicted") is None:
        return False
    reasoning = entry.get("reasoning")
    if not isinstance(reasoning, str) or not reasoning.strip():
        return False
    raw = entry.get("raw")
    if isinstance(raw, str) and raw.startswith(LLM_ERROR_PREFIX):
        return False
    return True
