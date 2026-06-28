"""Phase 2 FOL prompt assembly.

Fixed canonical prompt tier (F1). `build_prompt` fills the F1 template with a
condition-specific block and returns chat messages; `build_correction_prompt`
assembles the error-feedback retry prompt for the fix loop.

Conditions (the `{condition_block}` placeholder is populated accordingly):
  c1 (blind)          - no label given; the block is empty.
  c2 (phase-1 pred)   - inject a previous model's predicted label.
  c3 (gold)           - inject the gold relation.
  c4 (phase-1 + expl) - inject the predicted label and its explanation.
"""

from __future__ import annotations

from phase2_fol.prompts import fol_fix, nl_to_fol_F1

PROMPT_TIER = "F1"

_SYSTEM_TRANSLATE = "You are an expert in first-order logic and formal semantics."
_SYSTEM_FIX = "You are an expert in first-order logic. Fix the errors."

# Per-condition text spliced into the F1 template's {condition_block} slot.
# Non-empty blocks carry their own trailing blank line; c1 leaves the slot empty.
_CONDITION_BLOCKS = {
    "c1": "",
    "c2": "A previous model predicted: {phase1_label}\n\n",
    "c3": "The correct entailment relation is: {gold_label}\n\n",
    "c4": "A previous model predicted: {phase1_label}\nIts explanation: {phase1_explanation}\n\n",
}


def build_prompt(
    condition: str,
    premise: str,
    hypothesis: str,
    gold_label: str = "",
    phase1_label: str = "",
    phase1_explanation: str = "",
) -> list[dict]:
    """Assemble the translation prompt as chat messages for the F1 tier."""
    condition_block = _CONDITION_BLOCKS.get(condition, "").format(
        gold_label=gold_label or "",
        phase1_label=phase1_label or "",
        phase1_explanation=phase1_explanation or "",
    )
    body = nl_to_fol_F1.TEMPLATE.format(
        premise=premise,
        hypothesis=hypothesis,
        condition_block=condition_block,
    )
    return [
        {"role": "system", "content": _SYSTEM_TRANSLATE},
        {"role": "user", "content": body},
    ]


def build_correction_prompt(
    premise: str,
    hypothesis: str,
    previous_fol: str,
    error_message: str,
) -> list[dict]:
    """Assemble the correction-loop prompt as chat messages."""
    body = fol_fix.TEMPLATE.format(
        premise=premise,
        hypothesis=hypothesis,
        previous_fol=previous_fol,
        error_message=error_message,
    )
    return [
        {"role": "system", "content": _SYSTEM_FIX},
        {"role": "user", "content": body},
    ]
