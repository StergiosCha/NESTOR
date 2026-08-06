"""
NESTOR Phase 2 -- Coq Pipeline
==============================
NL -> Coq (via LLM) -> coqc -> result

Prompt tiers:
  T0: Syntax rules only (Montague-style Entity -> Prop)
  T1: T0 + Montague.v foundation file
  T2: T0 + section-matched foundation files
  T3: T0 + rich context (more files per section)

Conditions:
  C1 (blind): No label given. LLM decides the relation.
  C2 (Phase 1 prediction): LLM gets Phase 1 predicted label.
  C3 (gold label): LLM gets the gold label.
  C4 (Phase 1 + explanation): LLM gets Phase 1 label + NL explanation.

Two approaches:
  Direct: Formalise P, H directly. Proof IS the explanation.
  Valentino: Formalise the LLM's explanation E. Check P U E |= H.

Verification loop:
  If coqc fails, feed error back to LLM, retry up to k=3.

Requirements:
  pip install openai python-dotenv
  coqc in PATH (Coq 8.18+ recommended)
"""

import json
import os
import re
from collections import Counter
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from dotenv import load_dotenv

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from clients.azure import get_client, call_llm
from utils.fracas import load_flat

load_dotenv()

COQC_PATH = os.environ.get("COQC_PATH", "coqc")
COQ_TIMEOUT = int(os.environ.get("COQ_TIMEOUT", "60") or 60)
MAX_RETRIES = int(os.environ.get("MAX_RETRIES", "3") or 3)

PROMPT_DIR = Path(__file__).parent / "prompts"
FOUNDATIONS_DIR = Path(__file__).resolve().parent.parent / "coq_foundations"

COQ_MAX_TOKENS = 2500


# ============================================================
# PHASE 1 RESULTS (for C2/C4 conditions)
# ============================================================

PHASE1_RESULTS_DIR = (
    Path(__file__).resolve().parent.parent / "phase1_nli_eval" / "results"
)

# Retained for reference: the single-model, 30-item legacy file the C2/C4
# lookup used to read. Not used any more -- see load_phase1_results.
PHASE1_LEGACY_PATH = PHASE1_RESULTS_DIR / "fracas_results_azure.json"

_phase1_cache = {}
_COQC_VERSION = "<not probed>"


def load_phase1_results(dataset="fracas", model="gpt-4o",
                        technique="zero-shot", language="en"):
    """Phase 1 predictions for one dataset x model x technique x language.

    Reads the per-model result files that Phase 1 actually produced,
    phase1_nli_eval/results/{dataset}/{dataset}__{model}__{technique}__
    {language}.json, and returns {item_number: entry}.

    The previous implementation read a single legacy file,
    phase1_nli_eval/results/fracas_results_azure.json, which contains
    ONLY gpt-4o and ONLY 30 of the 342 FraCaS items. Under C2/C4 that
    silently returned "unknown" for the other 312 items and fed every
    model gpt-4o's predictions -- so the conditions would have been
    measuring something other than what they claim.
    """
    key = (dataset, model, technique, language)
    if key in _phase1_cache:
        return _phase1_cache[key]

    path = (PHASE1_RESULTS_DIR / dataset /
            f"{dataset}__{model}__{technique}__{language}.json")
    if not path.exists():
        raise FileNotFoundError(
            f"Phase 1 results not found: {path}\n"
            f"  C2/C4 need the Phase 1 run for {model} on {dataset} "
            f"({technique}, {language}). Available for this dataset: "
            + ", ".join(sorted(
                p.name for p in (PHASE1_RESULTS_DIR / dataset).glob("*.json")))
            if (PHASE1_RESULTS_DIR / dataset).exists()
            else f"Phase 1 results not found: {path}")

    with open(path, encoding="utf-8") as f:
        data = json.load(f)
    index = {}
    for it in data.get("results", []):
        n = item_number(it.get("id"))
        if n is not None:
            index[n] = it
    _phase1_cache[key] = index
    return index


def get_phase1_prediction(item_id, model="gpt-4o", dataset="fracas",
                          technique="zero-shot", language="en"):
    """Phase 1 predicted label and its reasoning for one item.

    The prediction is looked up for the SAME model that is now being
    asked to formalise, which is what C2/C4 mean: the model sees its own
    first-round answer. Raises if the item is absent rather than
    returning a placeholder, because a silent "unknown" would make C2
    indistinguishable from C1 on the affected items.
    """
    index = load_phase1_results(dataset=dataset, model=model,
                                technique=technique, language=language)
    n = item_number(item_id)
    entry = index.get(n)
    if entry is None:
        raise KeyError(
            f"no Phase 1 prediction for item {item_id!r} (number {n}) in "
            f"{dataset}/{model}/{technique}/{language}")
    pred = entry.get("predicted")
    if isinstance(pred, list):
        pred = ", ".join(str(x) for x in pred)
    return {
        "label": pred if pred else "unknown",
        # Phase 1 stores the model's rationale under "reasoning"
        "explanation": entry.get("reasoning") or entry.get("explanation") or "",
    }


# ============================================================
# PROMPT TIER & SECTION MAPPING
# ============================================================

PROMPT_FILES = {
    "T0": "nl_to_coq_T0.txt",
    "T1": "nl_to_coq_T1.txt",
    "T2": "nl_to_coq_T2.txt",
    "T3": "nl_to_coq_T3.txt",
}

# T2: 1-2 foundation files per section
SECTION_FILES = {
    "1": ["Montague.v", "BarwiseCooper.v"],
    "2": ["Link1983.v", "Montague.v"],
    "3": ["DonkeyScope.v", "Montague.v"],
    "4": ["Montague.v"],
    "5": ["AdjectivesExtension.v", "MTT_base.v"],
    "6": ["AdjectivesExtension.v", "Montague.v"],
    "7": ["DowtyTense.v", "Montague.v"],
    "8": ["PTQ.v", "kratzer2.v"],
    "9": ["MTT_base.v", "Montague.v"],
}

# T3: more files per section (richer context)
SECTION_FILES_T3 = {
    "1": ["Montague.v", "BarwiseCooper.v", "Quantifiers.v", "DonkeyScope.v"],
    "2": ["Link1983.v", "Montague.v", "champollion_full.v"],
    "3": ["DonkeyScope.v", "Montague.v", "BarwiseCooper.v"],
    "4": ["Montague.v"],
    "5": ["AdjectivesExtension.v", "MTT_base.v", "Quantifiers.v"],
    "6": ["AdjectivesExtension.v", "Montague.v", "MTT_base.v"],
    "7": ["DowtyTense.v", "Montague.v", "Aspect.v", "ImperfectiveParadox.v"],
    "8": ["PTQ.v", "kratzer2.v", "PTQ_deep.v"],
    "9": ["MTT_base.v", "Montague.v"],
}


# FraCaS section boundaries by problem number, from the FraCaS test suite.
# Mirrors utils/fracas.py::_SECTION_BOUNDARIES -- kept here so the pipeline
# has no hard dependency on the loader's internals.
_SECTION_BOUNDARIES = [
    (1, 80, 1),     # Generalized Quantifiers
    (81, 113, 2),   # Plurals
    (114, 141, 3),  # (Nominal) Anaphora
    (142, 196, 4),  # Ellipsis
    (197, 219, 5),  # Adjectives
    (220, 250, 6),  # Comparatives
    (251, 325, 7),  # Temporal Reference
    (326, 333, 8),  # Verbs
    (334, 346, 9),  # Attitudes
]

SECTION_NAMES = {
    1: "Generalized Quantifiers", 2: "Plurals", 3: "Anaphora",
    4: "Ellipsis", 5: "Adjectives", 6: "Comparatives",
    7: "Temporal Reference", 8: "Verbs", 9: "Attitudes",
}


# Gold labels are stored as yes/no/unknown in the FraCaS XML but the FOL
# pipeline passes the NLI relation names into its C3 prompt
# (fol_pipeline.py: gold_label = ", ".join(sample.labels)). Use the same
# vocabulary here so C3 is expressed identically across Phase 2a and 2b.
GOLD_TO_RELATION = {
    "yes": "Entailment",
    "no": "Contradiction",
    "unknown": "Unknown",
    "undef": "Unknown",
    "neutral": "Unknown",
    "entailment": "Entailment",
    "contradiction": "Contradiction",
}

# C3 tells the model the relation. Saying only "the relation is
# Entailment" leaves it to infer which theorem to close, so name the
# target explicitly -- otherwise the extra information does not reach
# the part of the task being measured.
GOLD_DIRECTIVE = {
    "Entailment": ("Therefore `Theorem entailment` MUST be closed with "
                   "Qed, and `Theorem contradiction` MUST end in Abort."),
    "Contradiction": ("Therefore `Theorem contradiction` MUST be closed "
                      "with Qed, and `Theorem entailment` MUST end in Abort."),
    "Unknown": ("Therefore NEITHER theorem can be proved: write both and "
                "end both in Abort."),
}


def item_number(item_id):
    """Trailing integer of an item id, or None.

    Handles every id shape in the corpus: "fracas-1", "fracas-0001",
    "fracas-346", "fracas-multilabel-0009", "oyxoy-0009".
    """
    m = re.search(r"(\d+)\s*$", str(item_id))
    return int(m.group(1)) if m else None


def get_section_from_id(item_id):
    """FraCaS section number (as a string) for an item id.

    The section is a function of the PROBLEM NUMBER, not of any field in
    the id string. The previous implementation took
    `str(item_id).split("-")[1]`, which on the ids the loader actually
    emits ("fracas-1" ... "fracas-346", and zero-padded variants) returns
    the problem number instead of the section. Because that value never
    matched a SECTION_FILES key, T2 and T3 silently fell through to the
    `["Montague.v"]` default and received no section-matched foundation
    files at all -- so configuration C had never really been run.

    Returns "1" only as a genuine fallback for unparseable ids.
    """
    n = item_number(item_id)
    if n is None:
        return "1"
    for lo, hi, sec in _SECTION_BOUNDARIES:
        if lo <= n <= hi:
            return str(sec)
    return "1"


def stratified_sample(items, per_section, seed=0):
    """N items per FraCaS section, for a pilot that covers all phenomena.

    A plain `--limit 30` takes the first 30 items, which are all section 1
    (Generalized Quantifiers) and tell you nothing about the other eight.
    """
    import random
    rng = random.Random(seed)
    by_sec = {}
    for it in items:
        by_sec.setdefault(get_section_from_id(it["id"]), []).append(it)
    out = []
    for sec in sorted(by_sec, key=lambda s: int(s)):
        pool = by_sec[sec]
        out.extend(rng.sample(pool, min(per_section, len(pool))))
    return out


# ------------------------------------------------------------------
# ERROR TAXONOMY
# ------------------------------------------------------------------
# Patterns confirmed against coqc 8.12.2 (see coqc_diagnosis.md).
COQ_ERROR_RULES = [
    ("timeout", r"^TIMEOUT$"),
    ("coqc_missing", r"not found\. Install Coq|not found\. Install"),
    ("empty_output", r"\A\s*\Z"),
    # the ill-typed premise->hypothesis pattern: the single most common
    # failure in the pilot generations
    ("prop_vs_proof_term",
     r"which should be Set, Prop or Type"),
    ("pending_proof", r"There are pending proofs"),
    ("unbound_identifier",
     r"The reference .* was not found|Unbound|Cannot find the declaration"),
    ("type_error",
     r"has type|Illegal application|is not a function|Cannot infer|"
     r"The term .* is expected"),
    ("tactic_failure",
     r"Unable to unify|No applicable tactic|Attempt to save an incomplete|"
     r"not an inductive|No such hypothesis|tactic failure|"
     r"cannot be applied|Not an exact proof"),
    ("missing_library",
     r"Unable to locate library|Cannot find a physical path"),
    ("syntax_error", r"Syntax error|illegal begin|was expected"),
]


def classify_coq_error(output):
    """Map coqc output onto a taxonomy category (first match wins)."""
    s = str(output or "")
    for name, pat in COQ_ERROR_RULES:
        if re.search(pat, s, re.MULTILINE):
            return name
    return "uncategorised"


def select_items_by_section(items, section):
    """Items whose FraCaS section equals `section`.

    The previous CLI filter was
        it["id"].split("-")[1].startswith(section)
    which for section "1" matched fracas-1 and fracas-100..199 -- 111
    items drawn from every section of the suite. This filters on the
    computed section instead.
    """
    want = str(section).strip()
    return [it for it in items if get_section_from_id(it["id"]) == want]


DATASET_PATHS = {
    "fracas": "data/fracas/fracas.xml",
    "fracas-translated":
        "data/translated_fracas/fracas_greek_final_ipa_team_crete.xml",
    "fracas-extended":
        "data/extended_fracas/fracas_greek_extended_team_crete.xml",
    "fracas-multilabel": "data/multilabel_fracas/multilabel_fracas.json",
    "oyxoy": "data/oyxoy/OYXOY.json",
}


def load_items(dataset="fracas", data_path=None):
    """Items for any of the five datasets, in this pipeline's flat shape.

    `utils.fracas.load_flat` handles only the original English FraCaS XML;
    the Greek XML variants carry a different element structure and the two
    multilabel sets are JSON with a `labels` list, so routing everything
    through `data.loaders` (which already parses all five) is what makes
    the non-fracas datasets runnable at all.

    `gold` is kept as a list for the multilabel sources and collapsed to a
    scalar elsewhere, because a single-verdict prover cannot express
    {Entailment, Unknown} and those items must be scored by the subset rule
    rather than string equality (see `is_correct`).
    """
    repo_root = Path(__file__).resolve().parent.parent
    if dataset not in DATASET_PATHS:
        raise ValueError(
            f"unknown dataset '{dataset}'; expected one of "
            f"{', '.join(sorted(DATASET_PATHS))}")

    sys.path.insert(0, str(repo_root))
    from data.loaders import load_dataset

    cwd = os.getcwd()
    try:
        os.chdir(repo_root)          # loaders.py uses repo-relative paths
        samples = load_dataset(dataset)
    finally:
        os.chdir(cwd)

    multilabel = dataset in ("fracas-multilabel", "oyxoy")
    items = []
    for s in samples:
        labels = [str(x) for x in (s.labels or [])]
        items.append({
            "id": s.id,
            "premise": s.premise,
            "hypothesis": s.hypothesis,
            "gold": labels if multilabel else (labels[0] if labels else ""),
            "language": s.language,
            "tags": list(s.tags or []),
            "fracas_sections": list(s.fracas_sections or []),
        })
    return items


_GOLD_ALIASES = {
    "entailment": {"yes", "entailment", "entail"},
    "contradiction": {"no", "contradiction", "contradict"},
    "neutral": {"unknown", "neutral", "undef", "undefined"},
}


def is_correct(pred, gold):
    """Does `pred` (one Coq verdict) match `gold` (a label or label set)?

    A Coq run yields exactly one verdict per item -- proved, refuted, or
    neither -- so on the 140 multi-gold items in oyxoy and
    fracas-multilabel string equality would mark every one wrong by
    construction. Those are scored by the subset rule already used in the
    Phase 1 and FOL analyses: a prediction contained in the gold set counts
    as correct. Single-label datasets are unaffected, since there the gold
    set has one member and the subset rule reduces to equality.
    """
    canon = None
    for name, aliases in _GOLD_ALIASES.items():
        if pred == name:
            canon = aliases
            break
    if canon is None:
        return False
    golds = gold if isinstance(gold, (list, tuple, set)) else [gold]
    return any(str(g).strip().lower() in canon for g in golds)


def load_foundation_files(file_list):
    """Load foundation .v files and concatenate them with delimiters."""
    context = ""
    for fname in file_list:
        fpath = FOUNDATIONS_DIR / fname
        if fpath.exists():
            content = fpath.read_text(encoding="utf-8")
            context += f"--- BEGIN {fname} ---\n"
            context += content
            context += f"\n--- END {fname} ---\n\n"
        else:
            context += f"--- {fname} NOT FOUND (skipped) ---\n\n"
    return context


def build_coq_prompt(prompt_tier, condition, premise, hypothesis,
                     gold_label=None, item_id=None, phase1_model="gpt-4o",
                     dataset="fracas", technique="zero-shot", language="en"):
    """Build the full Coq prompt with condition-specific content.

    prompt_tier: "T0", "T1", "T2", or "T3"
    condition:   "c1" (blind), "c2" (Phase 1 prediction),
                 "c3" (gold label), "c4" (Phase 1 prediction + rationale)
    phase1_model: whose Phase 1 answer C2/C4 should show. Defaults to the
                 model being run, set by the caller.
    """
    filename = PROMPT_FILES.get(prompt_tier, "nl_to_coq_T0.txt")
    template = (PROMPT_DIR / filename).read_text(encoding="utf-8")

    # Prepare condition-specific values
    phase1_label = ""
    phase1_explanation = ""
    if condition in ("c2", "c4") and item_id:
        p1 = get_phase1_prediction(item_id, model=phase1_model,
                                   dataset=dataset, technique=technique,
                                   language=language)
        phase1_label = p1["label"]
        phase1_explanation = p1["explanation"]

    # C3 hands the model the gold relation. The corpora store gold as
    # yes/no/unknown, which is meaningless as a Coq instruction, so
    # translate it into the relation name AND say which theorem to close.
    # Without this the C3 prompt read "The correct relation is: yes".
    #
    # oyxoy and fracas-multilabel store gold as a LIST, and 140 of their
    # items carry more than one admissible relation. A single Coq run
    # yields one verdict, so a multi-gold item has no single "correct"
    # theorem to close: collapsing it to its first element would state a
    # falsehood in the C3 prompt (claiming Entailment is THE relation when
    # Unknown is equally admissible) and would leak an arbitrary choice
    # into the condition being measured. Such items therefore get no
    # directive -- C3 degenerates to C1 for them, which is recorded in
    # `gold_ambiguous` so the analysis can report the affected subset
    # rather than silently averaging it in.
    gold_ambiguous = False
    if isinstance(gold_label, (list, tuple, set)):
        golds = [str(g).strip() for g in gold_label if str(g).strip()]
        gold_ambiguous = len(golds) > 1
        gold_label = golds[0] if len(golds) == 1 else None
    gold_label = GOLD_TO_RELATION.get(str(gold_label).strip().lower(),
                                      gold_label) if gold_label else gold_label
    gold_directive = "" if gold_ambiguous else GOLD_DIRECTIVE.get(gold_label, "")

    # Prepare foundation file content for T1/T2/T3
    montague_v = ""
    foundation_files = ""
    section = get_section_from_id(item_id) if item_id else "1"

    if prompt_tier == "T1":
        montague_path = FOUNDATIONS_DIR / "Montague.v"
        if montague_path.exists():
            montague_v = montague_path.read_text(encoding="utf-8")

    elif prompt_tier == "T2":
        files = SECTION_FILES.get(section, ["Montague.v"])
        foundation_files = load_foundation_files(files)

    elif prompt_tier == "T3":
        files = SECTION_FILES_T3.get(section, ["Montague.v"])
        foundation_files = load_foundation_files(files)

    # Fill template placeholders
    prompt = template.format(
        premise=premise,
        hypothesis=hypothesis,
        gold_label=gold_label or "",
        gold_directive=gold_directive,
        phase1_label=phase1_label,
        phase1_explanation=phase1_explanation,
        montague_v=montague_v,
        foundation_files=foundation_files,
    )

    # Emit ONLY the active condition. The template lists C1--C4 as a menu;
    # previously C1 stripped the whole block but C2/C3/C4 left all four
    # lines in place, so a C3 prompt also showed the C2 and C4 lines with
    # empty placeholders ("Prediction: . Explanation:") and told the model
    # about conditions that did not apply to its run. Replace the block
    # with the single relevant instruction.
    active = {
        "c1": "",
        # C2/C4 show the model its OWN first-round (Phase 1) answer for
        # this item, not another model's, so word it that way.
        "c2": (f"In an earlier round you answered this item directly, "
               f"without formalising it. Your answer was: {phase1_label}\n"
               f"That answer may be wrong. Formalise the pair and let the "
               f"proof decide.\n"),
        "c3": ((f"The correct relation is: {gold_label}\n"
                f"{gold_directive}\n") if gold_label else
               ("This item admits more than one correct relation, so no "
                "single relation is given. Formalise the pair and let the "
                "proof decide.\n")),
        "c4": (f"In an earlier round you answered this item directly, "
               f"without formalising it. Your answer was: {phase1_label}\n"
               f"Your reasoning was: {phase1_explanation}\n"
               f"That answer may be wrong. Formalise the pair and let the "
               f"proof decide.\n"),
    }.get(condition, "")
    replacement = ("" if not active
                   else f"=== GIVEN INFORMATION ===\n\n{active}\n")
    prompt, n_sub = re.subn(
        r"=== CONDITION.*?=== END CONDITION ===\s*",
        replacement, prompt, flags=re.DOTALL)
    if n_sub != 1:
        raise RuntimeError(
            f"condition block not found exactly once (found {n_sub}) in the "
            f"{prompt_tier} template -- check the '=== CONDITION ===' / "
            "'=== END CONDITION ===' markers")

    # Contamination guard, C1 only. The C1--C4 menu lives in the template
    # and is removed by the regex above, so an edit that breaks the
    # "=== CONDITION ===" / "=== END CONDITION ===" markers would leak the
    # gold label into every blind prompt without changing any observable
    # behaviour. Fail loudly instead of silently reporting a contaminated
    # C1 number.
    #
    # C2/C3/C4 are SUPPOSED to carry label information: C3 gives the gold
    # relation so that compilation and proof success measure formalisation
    # ability rather than label prediction. Only C1 is checked here.
    if condition == "c1":
        leaks = []
        if "CONDITION" in prompt:
            leaks.append("condition block not stripped")
        for probe in ("The correct relation is", "C3 (gold label)",
                      "A previous model predicted"):
            if probe in prompt:
                leaks.append(f"template text present: {probe!r}")
        # Only the CONDITION block's own sentences carry the item's label.
        # A generic instruction such as "determine whether the relation is
        # entailment, contradiction, or neutral", or "if this proof goes
        # through the relation is ENTAILMENT", appears in every prompt
        # independently of this item's gold and is not a leak -- so match
        # the label-bearing templates, not the bare word.
        if gold_label:
            for pat in (r"The correct relation is\s*:?\s*{g}",
                        r"gold\s+label\s*:?\s*{g}",
                        r"correct\s+(?:answer|label)\s*(?:is|:)\s*{g}"):
                if re.search(pat.format(g=re.escape(str(gold_label))),
                             prompt, re.IGNORECASE):
                    leaks.append(f"gold label {gold_label!r} stated in prompt")
                    break
        if leaks:
            raise RuntimeError(
                "C1 prompt contamination -- refusing to run a blind "
                "condition that contains label information: "
                + "; ".join(leaks))
    elif condition == "c3":
        # the converse check: C3 is pointless if the label never arrived.
        # A multi-gold item legitimately has no single label to state, so it
        # is exempt -- but a missing label with no ambiguity is still a bug.
        if not gold_label and not gold_ambiguous:
            raise RuntimeError(
                "condition c3 requires a gold label but none was passed")
        if gold_label and str(gold_label) not in prompt:
            raise RuntimeError(
                f"condition c3: gold label {gold_label!r} did not reach the "
                "prompt -- check the CONDITION block in the template")

    return prompt


# ============================================================
# COQ TRANSLATION
# ============================================================

def load_prompt(name):
    return (PROMPT_DIR / name).read_text(encoding="utf-8")


def extract_coq_code(raw_text):
    """Extract Coq code from LLM output (handles ```coq blocks)."""
    # Try to find code block
    match = re.search(r"```(?:coq)?\s*\n(.*?)```", raw_text, re.DOTALL)
    if match:
        return match.group(1).strip()
    # If no code block, assume the whole thing is Coq
    # Strip any obvious non-Coq lines
    lines = raw_text.strip().split("\n")
    coq_lines = []
    for line in lines:
        # Skip lines that look like natural language commentary
        if line.strip().startswith("This") or line.strip().startswith("Here"):
            continue
        coq_lines.append(line)
    return "\n".join(coq_lines).strip()


def translate_to_coq_direct(client, model, premise, hypothesis,
                            prompt_tier="T0", condition="c1",
                            gold_label=None, item_id=None, dataset="fracas", technique="zero-shot", language="en"):
    """Direct approach: formalise P, H in Coq using prompt tier and condition."""
    prompt = build_coq_prompt(prompt_tier, condition, premise, hypothesis,
                              gold_label=gold_label, item_id=item_id,
                              phase1_model=model, dataset=dataset,
                              technique=technique, language=language)
    messages = [
        {"role": "system",
         "content": "You are an expert in Coq and formal semantics. Output only valid Coq code."},
        {"role": "user", "content": prompt},
    ]
    raw = call_llm(client, model, messages, max_tokens=COQ_MAX_TOKENS)
    return extract_coq_code(raw), raw


def translate_to_coq_valentino(client, model, premise, hypothesis, explanation):
    """Valentino approach: formalise explanation E, prove P U E |= H."""
    template = load_prompt("valentino_coq.txt")
    prompt = template.format(
        premise=premise, hypothesis=hypothesis, explanation=explanation)
    messages = [
        {"role": "system",
         "content": "You are an expert in Coq and formal semantics. Output only valid Coq code."},
        {"role": "user", "content": prompt},
    ]
    raw = call_llm(client, model, messages, max_tokens=COQ_MAX_TOKENS)
    return extract_coq_code(raw), raw


# ============================================================
# COQ COMPILER
# ============================================================

# ------------------------------------------------------------------
# POST-PROCESSING
# ------------------------------------------------------------------
# Every rule below was checked against coqc 8.12.2 before being added;
# the probe transcript is in coqc_diagnosis.md. The point worth
# recording: rewriting `Hypothesis` to `Axiom` -- the fix that seemed
# obvious from reading the generations -- does NOT help. Both forms
# declare a PROOF TERM of the stated proposition, so a subsequent
# `Theorem entailment : premise -> hypothesis.` is ill-typed either way:
#
#   Error: The term "premise" has type "exists x : Entity, ..."
#          which should be Set, Prop or Type.
#
# What the code needs is `Definition premise : Prop := ...`, which names
# the proposition itself and can therefore appear on either side of `->`.

_DECL_KEYWORDS = r"(?:Hypothesis|Hypotheses|Axiom|Axioms|Variable|Variables|Conjecture)"

# A declaration whose body is a full proposition rather than a predicate
# type: starts with a quantifier/connective, or is an applied predicate.
_PROP_BODY = (r"(?=\s*(?:exists\b|forall\b|~|\(|"
              r"[A-Za-z_][A-Za-z0-9_']*\s+[A-Za-z_(]))")


def _names_used_as_propositions(code):
    """Names that appear where a Prop is required (either side of `->`
    in a Theorem/Lemma/Goal statement, or under a negation there).

    Only those declarations need converting; a genuine axiom that is
    only ever `apply`d should stay an Axiom.
    """
    used = set()
    for m in re.finditer(r"^\s*(?:Theorem|Lemma|Goal|Corollary|Remark)\b[^:]*:"
                         r"(.*?)(?:\.\s*$)", code, re.MULTILINE | re.DOTALL):
        stmt = m.group(1)
        # identifiers that stand alone as operands of -> or ~
        for tok in re.findall(r"[A-Za-z_][A-Za-z0-9_']*", stmt):
            used.add(tok)
    return used



# LLMs very often emit the Unicode logic symbols they saw in textbooks
# instead of Coq's ASCII operators. coqc's lexer rejects these outright
# ("Syntax Error: Lexer: Undefined token"), which loses the whole file
# before any semantics is checked. Confirmed as the dominant failure in
# the pilot generations: 1337 of 2736 contained at least one such symbol.
UNICODE_MAP = {
    "\u2192": "->", "\u21d2": "->", "\u27f6": "->", "\u27f9": "->",
    "\u2194": "<->", "\u21d4": "<->",
    "\u2200": "forall", "\u2203": "exists",
    "\u2227": "/\\", "\u2228": "\\/",
    "\u00ac": "~", "\u223c": "~",
    "\u2260": "<>", "\u2264": "<=", "\u2265": ">=",
    "\u2208": "In", "\u2261": "=",
    "\u22a5": "False", "\u22a4": "True",
    "\u2018": "'", "\u2019": "'", "\u201c": '"', "\u201d": '"',
    "\u2013": "-", "\u2014": "-", "\u00a0": " ",
}


def normalise_unicode(code):
    """Replace Unicode logic/typography with Coq ASCII equivalents."""
    out = code
    for uni, ascii_ in UNICODE_MAP.items():
        out = out.replace(uni, ascii_)
    # a quantifier written "forallx" after substitution needs a space
    out = re.sub(r"\b(forall|exists)(?=[A-Za-z_])", r"\1 ", out)
    return out


def postprocess_coq(code):
    """Repair the mechanical failure modes seen in real generations.

    Returns (fixed_code, applied) where `applied` lists the rule names
    that fired, so the harness can report which repairs mattered.
    """
    applied = []
    if not code or not code.strip():
        return code, applied

    original = code

    # 0. Unicode logic symbols -> ASCII. Must run FIRST: every later rule
    #    matches on ASCII Coq keywords.
    uni = normalise_unicode(code)
    if uni != code:
        code = uni
        applied.append("normalise_unicode")

    # 1. Strip markdown fences the extractor may have left behind.
    if "```" in code:
        code = re.sub(r"^\s*```(?:coq)?\s*$", "", code, flags=re.MULTILINE)
        applied.append("strip_fences")

    # 2. Declarations of whole propositions that are then used as
    #    propositions -> Definition ... : Prop := ...
    #    This is the repair that actually raises the compilation rate.
    used = _names_used_as_propositions(code)

    def _to_definition(m):
        name = m.group("name")
        if name in used:
            return f"Definition {name} : Prop :="
        return m.group(0)

    new_code, n = re.subn(
        rf"^{_DECL_KEYWORDS}\s+(?P<name>[A-Za-z_][A-Za-z0-9_']*)\s*:{_PROP_BODY}",
        _to_definition, code, flags=re.MULTILINE)
    if n and new_code != code:
        code = new_code
        applied.append("decl_to_definition")

    # 3. `Hypothesis`/`Variable` outside a Section is only a warning in
    #    8.x, but it makes the declaration Local and unusable after an
    #    Import. Normalise the remainder to Axiom (safe: these are the
    #    ones NOT used as propositions).
    new_code, n = re.subn(r"^(?:Hypothesis|Hypotheses)\b", "Axiom",
                          code, flags=re.MULTILINE)
    if n:
        code = new_code
        applied.append("hypothesis_to_axiom")
    new_code, n = re.subn(r"^(?:Variables?)\s+(?=[A-Za-z_][A-Za-z0-9_']*\s*:)",
                          "Parameter ", code, flags=re.MULTILINE)
    if n:
        code = new_code
        applied.append("variable_to_parameter")

    # 4. A proof left open makes coqc fail with "There are pending
    #    proofs" and loses the whole file, including theorems that did
    #    close. Terminate the dangling block.
    # Both keywords occur mid-line as often as at line start
    # ("Proof. firstorder. Qed." is a single line in most generations),
    # so these must not be anchored with ^.
    n_proof = len(re.findall(r"\bProof\b\s*\.", code))
    n_close = len(re.findall(r"\b(?:Qed|Defined|Abort|Admitted)\s*\.", code))
    if n_proof > n_close:
        code = code.rstrip()
        if not code.endswith("."):
            code += "."
        code += "\nAbort.\n" * (n_proof - n_close)
        applied.append("close_pending_proof")

    # 5. `Admitted` compiles but asserts the goal without proving it,
    #    which would score as a completed proof. Downgrade to Abort so
    #    the label extractor treats it as undecided.
    new_code, n = re.subn(r"\bAdmitted\s*\.", "Abort.", code)
    if n:
        code = new_code
        applied.append("admitted_to_abort")

    # 6. Requires of libraries outside the standard distribution abort
    #    the file. Drop requires of the foundation files, whose content
    #    is already inlined in the prompt.
    new_code, n = re.subn(
        r"^\s*Require\s+(?:Import\s+|Export\s+)?"
        r"(?:Montague|BarwiseCooper|MTT_base|Quantifiers|FCS|PTQ|Link1983|"
        r"DonkeyScope|DowtyTense|AdjectivesExtension|kratzer\w*|Aspect|"
        r"ImperfectiveParadox|champollion\w*)\b[^.]*\.\s*$",
        "", code, flags=re.MULTILINE | re.IGNORECASE)
    if n:
        code = new_code
        applied.append("drop_foundation_require")

    if code != original and not applied:
        applied.append("whitespace")
    return code, applied


def coqc_version():
    """coqc version string, recorded in result metadata.

    The compiler version changes what compiles, so a results file that
    does not name it cannot be reproduced or compared across machines.
    """
    try:
        r = subprocess.run([COQC_PATH, "--version"], capture_output=True,
                           text=True, timeout=30)
        return (r.stdout or r.stderr).strip().split("\n")[0]
    except Exception as e:
        return f"<unavailable: {type(e).__name__}>"


def run_coqc(coq_code, timeout=None, postprocess=True):
    """Compile Coq code with coqc.

    Returns:
        compiled: bool -- did coqc exit 0?
        proof_complete: bool -- did at least one theorem close with Qed?
        output: str -- compiler output (errors etc.)

    `proof_complete` used to be `compiled and "Abort" not in coq_code`,
    which is wrong in both directions: a file whose entailment theorem
    closes with Qed AND whose contradiction theorem ends in Abort is the
    NORMAL shape of a correct entailment answer, and that test scored it
    as incomplete. Conversely a file with no theorem at all scored as
    complete. Verified against coqc 8.12.2: a file where every theorem
    is Abort'ed still exits 0, so `compiled` alone says nothing about
    whether anything was proved.
    """
    timeout = timeout or COQ_TIMEOUT
    applied = []
    if postprocess:
        coq_code, applied = postprocess_coq(coq_code)

    tmpdir = tempfile.mkdtemp(prefix="coqrun_")
    coq_file = os.path.join(tmpdir, "item.v")
    with open(coq_file, "w", encoding="utf-8") as f:
        f.write(coq_code)

    try:
        result = subprocess.run(
            [COQC_PATH, coq_file],
            capture_output=True, text=True, timeout=timeout,
            cwd=tmpdir,
        )
        output = result.stdout + result.stderr
        compiled = result.returncode == 0
        proof_complete = compiled and bool(
            re.search(r"\bQed\s*\.", coq_code))
        if applied:
            output = f"[postprocess: {','.join(applied)}]\n" + output
        return compiled, proof_complete, output
    except subprocess.TimeoutExpired:
        return False, False, "TIMEOUT"
    except FileNotFoundError:
        return False, False, (
            f"ERROR: {COQC_PATH} not found. Install Coq or set COQC_PATH.")
    finally:
        shutil.rmtree(tmpdir, ignore_errors=True)


def extract_coq_label(coq_code):
    """Extract the NLI label from compiled Coq code.

    Logic:
      - If entailment theorem has Qed -> "entailment"
      - If contradiction theorem has Qed -> "contradiction"
      - If both Abort -> "neutral"
      - Fallback heuristic for single-theorem files
    """
    # Use negative lookahead (?!Theorem) to avoid crossing into the
    # next theorem block. Without this, "Theorem entailment...Abort...
    # Theorem contradiction...Qed" would falsely match entailment->Qed.
    has_entailment_qed = bool(re.search(
        r"Theorem\s+entailment\b(?:(?!Theorem).)*?Qed\.",
        coq_code, re.DOTALL))
    has_contradiction_qed = bool(re.search(
        r"Theorem\s+contradiction\b(?:(?!Theorem).)*?Qed\.",
        coq_code, re.DOTALL))

    if has_entailment_qed and not has_contradiction_qed:
        return "entailment"
    if has_contradiction_qed and not has_entailment_qed:
        return "contradiction"
    if not has_entailment_qed and not has_contradiction_qed:
        # Both theorems Abort'ed (or neither is present). For an NLI task
        # this is the "no proof either way" outcome, which is what
        # `unknown` means -- but it is also what a file with no theorems
        # at all looks like, so distinguish the two.
        if re.search(r"^\s*Theorem\s+(?:entailment|contradiction)\b",
                     coq_code, re.MULTILINE):
            return "neutral"
        return "undecided"

    # Both closed with Qed: the formalisation proved H and ~H, so the
    # axioms are inconsistent. This is a degenerate output, not an
    # entailment -- report it rather than silently guessing.
    return "inconsistent"


# ============================================================
# VERIFICATION LOOP
# ============================================================

def fix_coq(client, model, premise, hypothesis, label, previous_coq,
            error_message):
    """Ask LLM to fix Coq code based on compiler error."""
    template = load_prompt("coq_fix.txt")
    prompt = template.format(
        premise=premise, hypothesis=hypothesis, label=label,
        previous_coq=previous_coq, error_message=error_message,
    )
    messages = [
        {"role": "system",
         "content": "You are an expert in Coq. Fix the compilation errors."},
        {"role": "user", "content": prompt},
    ]
    raw = call_llm(client, model, messages, max_tokens=COQ_MAX_TOKENS)
    return extract_coq_code(raw), raw


def run_coq_pipeline(client, model, premise, hypothesis, label,
                     approach="direct", explanation=None, max_retries=None,
                     prompt_tier="T0", condition="c1",
                     gold_label=None, item_id=None, dataset="fracas", technique="zero-shot", language="en"):
    """Full Coq pipeline with verification loop.

    approach: "direct" or "valentino"
    prompt_tier: "T0", "T1", "T2", "T3"
    condition: "c1", "c2", "c3", "c4"
    """
    max_retries = max_retries or MAX_RETRIES
    errors = []

    for attempt in range(1, max_retries + 1):
        # Step 1: Get Coq code
        if attempt == 1:
            if approach == "direct":
                coq_code, raw = translate_to_coq_direct(
                    client, model, premise, hypothesis,
                    prompt_tier=prompt_tier, condition=condition,
                    gold_label=gold_label, item_id=item_id,
                    dataset=dataset, technique=technique, language=language)
            else:
                coq_code, raw = translate_to_coq_valentino(
                    client, model, premise, hypothesis, explanation)
        else:
            coq_code, raw = fix_coq(
                client, model, premise, hypothesis, label,
                previous_code, errors[-1])

        previous_code = coq_code

        if not coq_code.strip():
            errors.append("Empty Coq code returned by LLM.")
            continue

        # Step 2: Compile
        compiled, proof_complete, output = run_coqc(coq_code)

        # Extract the label the LLM chose from the Coq code structure
        predicted_label = extract_coq_label(coq_code)

        if compiled and proof_complete:
            return {
                "coq_code": coq_code,
                "compiled": True, "proof_complete": True,
                "predicted_label": predicted_label,
                "approach": approach,
                "attempts": attempt, "errors": errors,
            }

        if compiled and not proof_complete:
            # Compiled but proof was Aborted
            return {
                "coq_code": coq_code,
                "compiled": True, "proof_complete": False,
                "predicted_label": predicted_label,
                "approach": approach,
                "attempts": attempt, "errors": errors,
            }

        # Compilation failed -- extract error for feedback
        errors.append(output[:1000])  # truncate long errors

    return {
        "coq_code": coq_code if coq_code else "",
        "compiled": False, "proof_complete": False,
        "predicted_label": "error",
        "approach": approach,
        "attempts": max_retries, "errors": errors,
    }


# ============================================================
# BATCH RUNNER
# ============================================================

def run_batch(items, client, model, approach="direct", output_file=None,
              prompt_tier="T0", condition="c1", dataset="fracas",
              technique="zero-shot", language="en"):
    """Run Coq pipeline on a list of NLI items."""
    global _COQC_VERSION
    _COQC_VERSION = coqc_version()
    print(f"coqc: {_COQC_VERSION}")
    if "unavailable" in _COQC_VERSION or "not found" in _COQC_VERSION.lower():
        raise RuntimeError(
            f"coqc is not usable ({_COQC_VERSION}). Every item would fail "
            f"identically. Set COQC_PATH (currently {COQC_PATH!r}).")
    def _payload(rs):
        """Build the {metadata, results, summary} wrapper for `rs`."""
        return {
            "metadata": {
                "dataset": dataset,
                "model": model,
                "prompt_tier": prompt_tier,
                "condition": condition,
                "approach": approach,
                "coqc_version": _COQC_VERSION,
                "coqc_path": COQC_PATH,
                "coq_timeout": COQ_TIMEOUT,
                "max_retries": MAX_RETRIES,
                "postprocess": True,
                "n_items": len(rs),
                "written_at": time.strftime("%Y-%m-%dT%H:%M:%SZ",
                                            time.gmtime()),
            },
            "results": rs,
            "summary": {
                "total": len(rs),
                "compiled": sum(1 for r in rs if r["compiled"]),
                "proof_complete": sum(1 for r in rs if r["proof_complete"]),
                "correct": sum(1 for r in rs if r.get("correct")),
            },
        }

    def _flush(rs):
        """Write results after EVERY item, not just at the end of the cell.

        A reasoning model can take minutes per item, so a 27-item cell runs
        for the better part of an hour. Writing only at the end means a
        Ctrl-C or a crash at item 26 discards all 26 completed items and
        their API spend. Written via a temp file + os.replace so an
        interrupt mid-write cannot leave truncated JSON on disk.
        """
        if not output_file:
            return
        os.makedirs(os.path.dirname(output_file) or ".", exist_ok=True)
        tmp = output_file + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(_payload(rs), f, indent=2, ensure_ascii=False)
        os.replace(tmp, output_file)

    # Resume inside a partially-completed cell: keep items already done and
    # re-run only the rest, so an interrupted cell costs nothing to restart.
    results = []
    done_ids = set()
    if output_file and os.path.exists(output_file):
        try:
            with open(output_file, encoding="utf-8") as f:
                prev = json.load(f)
            results = [r for r in prev.get("results", [])
                       if r.get("predicted_label") != "api_error"]
            done_ids = {r.get("id") for r in results}
            if done_ids:
                print(f"  resuming: {len(done_ids)} item(s) already done")
        except (json.JSONDecodeError, OSError):
            results, done_ids = [], set()

    for i, item in enumerate(items):
        if item.get("id") in done_ids:
            continue
        t_item = time.time()
        print(f"[{i+1}/{len(items)}] {item.get('id', i+1)}: ", end="",
              flush=True)

        # A transient API failure must not destroy the whole cell. Without
        # this guard an APITimeoutError on item 7 of 27 loses the six
        # completed items with it and writes no file at all. Record the
        # failure as an item-level error and carry on; the item is
        # distinguishable afterwards by predicted_label == "api_error".
        try:
            result = run_coq_pipeline(
                client, model,
                item["premise"], item["hypothesis"],
                item.get("gold", "entailment"),
                approach=approach,
                explanation=item.get("explanation"),
                prompt_tier=prompt_tier,
                condition=condition,
                gold_label=item.get("gold"),
                item_id=item.get("id"),
                dataset=dataset, technique=technique, language=language,
            )
        except Exception as exc:
            print(f"API ERROR ({type(exc).__name__}); recorded and skipped")
            results.append({
                "id": item.get("id", i + 1),
                "gold": item.get("gold", ""),
                "premise_nl": item["premise"],
                "hypothesis_nl": item["hypothesis"],
                "approach": approach,
                "attempts": 0,
                "compiled": False,
                "proof_complete": False,
                "correct": False,
                "coq_code": "",
                "predicted_label": "api_error",
                "errors": [f"{type(exc).__name__}: {exc}"],
            })
            _flush(results)
            continue
        result["id"] = item.get("id", i+1)
        result["gold"] = item.get("gold", "")
        result["premise_nl"] = item["premise"]
        result["hypothesis_nl"] = item["hypothesis"]

        # Check correctness
        pred = result.get("predicted_label", "")
        gold = item.get("gold", "")
        correct = is_correct(pred, gold)
        result["correct"] = correct

        status = "compiled" if result["compiled"] else "FAILED"
        if result["proof_complete"]:
            status = "PROVED"
        tag = "+" if correct else "-"
        dt = time.time() - t_item
        print(f"{status} [{pred}] (attempt {result['attempts']}) {tag} "
              f"{dt:.0f}s")

        results.append(result)
        _flush(results)
        time.sleep(0.5)

    # Final write. The payload shape matches what the Phase 1 and FOL
    # pipelines produce, so the analysis scripts read all three the same
    # way, and each file records the compiler version, tier and condition
    # it was produced with.
    if output_file:
        _flush(results)
        print(f"\nResults saved to {output_file}")

    # Summary
    total = len(results)
    compiled = sum(1 for r in results if r["compiled"])
    proved = sum(1 for r in results if r["proof_complete"])
    correct_n = sum(1 for r in results if r.get("correct"))
    avg_attempts = (sum(r["attempts"] for r in results) / total
                    if total else 0)

    print(f"\n--- Summary ({model}, {approach}, {prompt_tier}, {condition}) ---")
    print(f"Total: {total}")
    print(f"Compiled: {compiled}/{total} ({compiled/total:.1%})")
    print(f"Proof complete: {proved}/{total} ({proved/total:.1%})")
    print(f"Correct: {correct_n}/{total} ({correct_n/total:.1%})")
    print(f"Avg attempts: {avg_attempts:.1f}")

    return results


# ============================================================
# MAIN
# ============================================================

if __name__ == "__main__":
    import argparse
    from clients.models import MODELS

    parser = argparse.ArgumentParser(description="NESTOR Coq Pipeline")
    parser.add_argument("--data", default="../data/fracas/fracas.xml",
                        help="Path to dataset (FraCaS XML or JSON)")
    parser.add_argument("--model", default="gpt-4o",
                        help="Model key (see clients/models.py)")
    parser.add_argument("--approach", default="direct",
                        choices=["direct", "valentino"],
                        help="Coq approach: direct or valentino")
    parser.add_argument("--output", default=None,
                        help="Output JSON file")
    parser.add_argument("--limit", type=int, default=None,
                        help="Max items to process")
    parser.add_argument("--section", default=None,
                        help="FraCaS section filter (e.g. '1' for quantifiers)")
    parser.add_argument("--tier", default="T0",
                        choices=["T0", "T1", "T2", "T3"],
                        help="Prompt tier: T0 (syntax), T1 (+Montague.v), "
                             "T2 (+section files), T3 (+rich context)")
    parser.add_argument("--condition", default="c1",
                        choices=["c1", "c2", "c3", "c4"],
                        help="Condition: c1 (blind), c2 (phase1 pred), "
                             "c3 (gold), c4 (phase1+expl)")
    parser.add_argument("--dataset", default="fracas",
                        help="Dataset name, used for C2/C4 Phase 1 lookup "
                             "and in the output metadata")
    parser.add_argument("--stratified", type=int, default=None,
                        help="Pilot mode: sample N items per FraCaS section "
                             "(9 sections, so N=3 gives 27 items)")
    parser.add_argument("--seed", type=int, default=0,
                        help="RNG seed for --stratified")
    args = parser.parse_args()

    # Only check vars needed for the selected model
    required = [("AZURE_API_KEY", os.environ.get("AZURE_API_KEY", ""))]
    if MODELS.get(args.model, {}).get("provider") == "azure-openai":
        required.append(("AZURE_OPENAI_ENDPOINT",
                         os.environ.get("AZURE_OPENAI_ENDPOINT", "")))
    elif MODELS.get(args.model, {}).get("provider") == "azure-ai":
        required.append(("AZURE_AI_ENDPOINT",
                         os.environ.get("AZURE_AI_ENDPOINT", "")))
    missing = [name for name, val in required if not val]
    if missing:
        print(f"ERROR: missing required env vars: {', '.join(missing)}")
        print("  copy .env.example to .env and fill in values")
        sys.exit(1)

    items = load_items(args.dataset, args.data)
    n_loaded = len(items)
    if args.section:
        items = select_items_by_section(items, args.section)
        print(f"Section {args.section} "
              f"({SECTION_NAMES.get(int(args.section), '?')}): "
              f"{len(items)} of {n_loaded} items")
    if args.stratified:
        items = stratified_sample(items, args.stratified, seed=args.seed)
        print(f"Stratified pilot sample: {len(items)} items "
              f"({args.stratified} per section, seed={args.seed})")
    if args.limit:
        items = items[:args.limit]

    if not items:
        print("ERROR: no items selected -- check --section / --limit")
        sys.exit(1)

    print(f"Loaded {len(items)} items from {args.data}")
    print(f"Model: {args.model}, Tier: {args.tier}, "
          f"Condition: {args.condition}, Approach: {args.approach}")
    seccount = Counter(get_section_from_id(it["id"]) for it in items)
    print("  section spread: "
          + ", ".join(f"{k}:{seccount[k]}" for k in sorted(seccount)) + "\n")

    client = get_client(args.model)
    output = (args.output
              or f"results/coq_{args.tier}_{args.condition}_{args.model}"
                 f"_{len(items)}items.json")
    run_batch(items, client, args.model, approach=args.approach,
              output_file=output,
              prompt_tier=args.tier, condition=args.condition,
              dataset=args.dataset)
