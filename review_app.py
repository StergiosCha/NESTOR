"""
NLI Explanation Review App
===========================
A local-only Streamlit app for human validation of NLI explanations, matching
the Phase 1 evaluation plan's 3-criterion rubric:
    phenomenon_id (0/1/2), soundness (0/1/2), consistency (0/1)
Each criterion gets its own score AND its own comment box, since they are
independent grading rubrics (a note about *why* the phenomenon ID is wrong
is a different thing from a note about *why* the reasoning is unsound).
Works on JSON files shaped like:
{
  "metadata": {"dataset": ..., "model": ..., "technique": ..., "language": ...},
  "results": [
     {"id": ..., "premise": ..., "hypothesis": ..., "gold": [...],
      "predicted": ..., "reasoning": ..., "tags": [...], "success": ..., ...},
     ...
  ],
  "summary": {...}
}
Run locally with:
    streamlit run review_app.py
Each reviewer gets their own save file per dataset file
(reviews/<file>.<reviewer>.reviews.json), so multiple annotators never
overwrite each other's work. Nothing is ever sent anywhere else.
"""
import json
import random
import re
from datetime import datetime
from pathlib import Path
import pandas as pd
import streamlit as st
st.set_page_config(page_title="NLI Explanation Reviewer", layout="wide")
# --------------------------------------------------------------------------
# App location & fixed defaults — the app lives in NESTOR/, the data to
# review lives in NESTOR/phase_1_nli_eval/results/, so both are resolved
# relative to this file instead of requiring manual navigation.
# --------------------------------------------------------------------------
APP_DIR = Path(__file__).resolve().parent
DEFAULT_RESULTS_ROOT = APP_DIR / "phase1_nli_eval" / "results"
DEFAULT_REVIEWS_DIR = APP_DIR / "reviews"
README_PATH = APP_DIR / "REVIEW_APP_README.md"
# --------------------------------------------------------------------------
# README viewer — available in the sidebar at all times, including before
# a reviewer name has been chosen.
# --------------------------------------------------------------------------
with st.sidebar.expander("📖 README / instructions"):
    if README_PATH.exists():
        try:
            st.markdown(README_PATH.read_text(encoding="utf-8"))
        except OSError as e:
            st.caption(f"Couldn't read the README: {e}")
    else:
        st.caption(f"No REVIEW_APP_README.md found at `{README_PATH}`.")
# --------------------------------------------------------------------------
# Reviewer login gate — pick an existing username or create a new one
# before anything else loads. Existing usernames are discovered from the
# "reviewer" field already stored inside saved review files.
# --------------------------------------------------------------------------
def discover_known_usernames(reviews_root: Path):
    """Existing filenames look like `{stem}.{reviewer_slug}.reviews.json`.
    `reviewer_slug` can never itself contain a "." (sanitize_for_filename
    replaces any non alnum/_/- character with "_" before saving), so the
    segment after the last "." before the ".reviews.json" suffix is always
    the reviewer slug, even if the dataset stem itself contains dots."""
    names = set()
    if not reviews_root.exists():
        return []
    suffix = ".reviews.json"
    for f in reviews_root.rglob(f"*{suffix}"):
        stem_and_reviewer = f.name[: -len(suffix)]
        if "." not in stem_and_reviewer:
            continue
        _, reviewer_slug = stem_and_reviewer.rsplit(".", 1)
        if reviewer_slug:
            names.add(reviewer_slug)
    return sorted(names, key=str.lower)
def load_json_dict(path: Path) -> dict:
    if path.exists():
        try:
            with open(path, "r", encoding="utf-8") as f:
                return json.load(f)
        except (json.JSONDecodeError, OSError):
            return {}
    return {}
if "reviewer_name" not in st.session_state:
    st.title("NLI Explanation Reviewer")
    st.subheader("Who's reviewing?")
    known_users = discover_known_usernames(DEFAULT_REVIEWS_DIR)
    st.caption(
        "Pick your name if you've reviewed before, or add a new one below — "
        "each reviewer gets their own save file, so nobody's work is ever overwritten."
    )
    login_options = (["(select)"] + known_users if known_users else []) + ["+ Add new reviewer..."]
    picked = st.selectbox("Reviewer", login_options, index=0)
    typed_name = ""
    if picked == "+ Add new reviewer...":
        typed_name = st.text_input("New reviewer name / initials")
    final_name = typed_name.strip() if picked == "+ Add new reviewer..." else (
        "" if picked == "(select)" else picked
    )
    if st.button("Continue", type="primary", disabled=not final_name.strip()):
        st.session_state["reviewer_name"] = final_name.strip()
        st.rerun()
    st.stop()
reviewer_name = st.session_state["reviewer_name"]
# --------------------------------------------------------------------------
# Rubric definition (matches PHASE1_EVALUATION_PLAN.md judge prompt)
# --------------------------------------------------------------------------
CRITERIA = {
    "phenomenon_id": {
        "label": "Phenomenon identification",
        "help": "Does the explanation correctly identify the phenomenon matching the gold tags?",
        "options": [
            (2, "2 — correctly identifies the phenomenon matching the gold tags"),
            (1, "1 — addresses a related but incorrect phenomenon"),
            (0, "0 — generic, circular, or identifies an irrelevant phenomenon"),
        ],
    },
    "soundness": {
        "label": "Soundness",
        "help": "Is the reasoning logically valid and linguistically accurate?",
        "options": [
            (2, "2 — logically valid and linguistically accurate"),
            (1, "1 — minor errors, but overall direction is correct"),
            (0, "0 — wrong, contradictory, or incoherent"),
        ],
    },
    "consistency": {
        "label": "Consistency with predicted label",
        "help": "Does the explanation actually support the label the model predicted?",
        "options": [
            (1, "1 — explanation supports the predicted label"),
            (0, "0 — explanation contradicts or is unrelated to the predicted label"),
        ],
    },
}
CRITERION_KEYS = list(CRITERIA.keys())
# --------------------------------------------------------------------------
# Data loading helpers
# --------------------------------------------------------------------------
@st.cache_data(show_spinner=False)
def load_json_file(path: str, mtime: float):
    """Load a dataset JSON file. `mtime` is part of the cache key so edited
    files are picked back up automatically."""
    with open(path, "r", encoding="utf-8") as f:
        data = json.load(f)
    results = data.get("results", [])
    for i, r in enumerate(results):
        if "id" not in r or r["id"] is None:
            r["id"] = f"row-{i}"
    return data.get("metadata", {}), results, data.get("summary", {})
def list_json_files(folder: str, recursive: bool = False):
    p = Path(folder)
    if not p.exists() or not p.is_dir():
        return []
    if recursive:
        return sorted(p.rglob("*.json"))
    return sorted([f for f in p.iterdir() if f.is_file() and f.suffix.lower() == ".json"])
IGNORED_SUBFOLDERS = {"reviews", "__pycache__"}
def list_subfolders(folder: str):
    p = Path(folder)
    if not p.exists() or not p.is_dir():
        return []
    try:
        return sorted(
            [d for d in p.iterdir()
             if d.is_dir() and not d.name.startswith(".") and d.name not in IGNORED_SUBFOLDERS],
            key=lambda d: d.name.lower(),
        )
    except OSError:
        return []
def build_breadcrumbs(root_path: Path, current_path: Path):
    """Return [(label, path), ...] from root down to current_path."""
    crumbs = [(root_path.name or str(root_path), root_path)]
    try:
        rel = current_path.relative_to(root_path)
    except ValueError:
        return crumbs
    accum = root_path
    for part in rel.parts:
        accum = accum / part
        crumbs.append((part, accum))
    return crumbs
def save_json_dict(path: Path, data: dict):
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)
def sanitize_for_filename(name: str) -> str:
    name = name.strip().lower().replace(" ", "_")
    keep = [c if (c.isalnum() or c in "_-") else "_" for c in name]
    cleaned = "".join(keep).strip("_")
    return cleaned or "anonymous"
def reviewer_file_path(reviews_dir: str, stem: str, reviewer: str) -> Path:
    return Path(reviews_dir) / f"{stem}.{sanitize_for_filename(reviewer)}.reviews.json"
def load_all_reviewers(reviews_dir: str, stem: str) -> dict:
    """Merge every reviewer's file for this dataset into
    {sample_id: {reviewer_slug: {phenomenon_id, soundness, consistency, ...}}}."""
    merged: dict = {}
    p = Path(reviews_dir)
    if not p.exists():
        return merged
    prefix = f"{stem}."
    suffix = ".reviews.json"
    for f in p.glob(f"{stem}.*.reviews.json"):
        reviewer_slug = f.name[len(prefix):-len(suffix)]
        data = load_json_dict(f)
        for sample_id, entry in data.items():
            merged.setdefault(sample_id, {})[reviewer_slug] = entry
    return merged
def load_judge_scores(path: Path) -> dict:
    """Load an LLM-judge scored file (phase1_nli_eval/judge_scores/{dataset}/*.json)
    into the same per-sample shape as human reviews, so it can be compared like
    any other reviewer."""
    if not path.exists():
        return {}
    data = load_json_dict(path)
    scores = data.get("scores", [])
    out = {}
    for s in scores:
        sid = str(s.get("id"))
        out[sid] = {
            "phenomenon_id": s.get("phenomenon_id"),
            "soundness": s.get("soundness"),
            "consistency": s.get("consistency"),
            "phenomenon_id_notes": "",
            "soundness_notes": "",
            "consistency_notes": "",
            "general_notes": "",
            "reviewer": "llm_judge",
            "reviewed_at": data.get("metadata", {}).get("completed_at", ""),
        }
    return out
def flatten(v):
    if v is None:
        return ""
    if isinstance(v, list):
        return ", ".join(str(x) for x in v)
    return str(v)
def is_fully_scored(entry) -> bool:
    if not entry:
        return False
    return all(entry.get(k) is not None for k in CRITERION_KEYS)
def is_partially_scored(entry) -> bool:
    if not entry:
        return False
    return any(entry.get(k) is not None for k in CRITERION_KEYS) and not is_fully_scored(entry)
def total_score(entry):
    if not entry or any(entry.get(k) is None for k in CRITERION_KEYS):
        return None
    return sum(entry.get(k) for k in CRITERION_KEYS)
# --------------------------------------------------------------------------
# Human validation sampling (10% per dataset, seed 42) — mirrors the plan
# --------------------------------------------------------------------------
def natural_key(s: str):
    m = re.search(r"(\d+)\s*$", s)
    return (0, int(m.group(1))) if m else (1, s)
def compute_human_validation_sample(item_ids):
    unique_sorted = sorted(set(item_ids), key=natural_key)
    random.seed(42)
    k = max(1, len(unique_sorted) // 10)
    return sorted(random.sample(unique_sorted, k), key=natural_key)
def guess_dataset_name(metadata: dict, path: Path) -> str:
    if metadata.get("dataset"):
        return str(metadata["dataset"])
    return path.stem.split("__")[0]
def guess_model_name(metadata: dict, path: Path) -> str:
    if metadata.get("model"):
        return str(metadata["model"])
    parts = path.stem.split("__")
    return parts[1] if len(parts) > 1 else ""
# --------------------------------------------------------------------------
# Cohen's kappa (no sklearn dependency needed)
# --------------------------------------------------------------------------
def cohen_kappa(a, b):
    pairs = [(x, y) for x, y in zip(a, b) if x is not None and y is not None]
    n = len(pairs)
    if n == 0:
        return None, 0
    categories = sorted({x for x, _ in pairs} | {y for _, y in pairs})
    po = sum(1 for x, y in pairs if x == y) / n
    pe = 0.0
    for c in categories:
        pa = sum(1 for x, _ in pairs if x == c) / n
        pb = sum(1 for _, y in pairs if y == c) / n
        pe += pa * pb
    if pe == 1:
        return 1.0, n
    return (po - pe) / (1 - pe), n
# --------------------------------------------------------------------------
# Sidebar: data source — defaults to phase_1_nli_eval/results next to the
# app, and requires an explicit subfolder choice (the loose JSON files
# directly inside results/ are ignored on purpose).
# --------------------------------------------------------------------------
st.sidebar.title("Data source")
st.sidebar.markdown(f"**Reviewer:** {reviewer_name}")
if st.sidebar.button("Switch reviewer"):
    del st.session_state["reviewer_name"]
    st.rerun()
root_dir_input = st.sidebar.text_input(
    "Results folder",
    value=str(DEFAULT_RESULTS_ROOT),
    help="Defaults to phase_1_nli_eval/results next to the app — override only "
         "if your data lives somewhere else.",
)
try:
    root_path = Path(root_dir_input).expanduser().resolve()
except OSError:
    root_path = DEFAULT_RESULTS_ROOT.resolve()
if not root_path.exists() or not root_path.is_dir():
    st.sidebar.error("That results folder doesn't exist.")
    st.title("NLI Explanation Reviewer")
    st.stop()
subfolders = list_subfolders(str(root_path))
if not subfolders:
    st.sidebar.error("No subfolders found inside the results folder to choose from.")
    st.title("NLI Explanation Reviewer")
    st.stop()
subfolder_names = [d.name for d in subfolders]
chosen_subfolder = st.sidebar.selectbox(
    "Choose the subfolder to work on",
    ["(select)"] + subfolder_names,
    index=0,
    help="The loose .json files directly inside the results folder are ignored "
         "on purpose — pick the subfolder that has the files you want to review.",
)
if chosen_subfolder == "(select)":
    st.title("NLI Explanation Reviewer")
    st.info("Choose a subfolder from the sidebar to begin.")
    st.stop()
browse_path = subfolders[subfolder_names.index(chosen_subfolder)]
recursive = st.sidebar.checkbox(
    "Include files from nested subfolders", value=False,
    help="Off: only show files directly inside the chosen subfolder. On: show "
         "every JSON file nested anywhere below it.",
)
json_files = list_json_files(str(browse_path), recursive=recursive)
if not json_files:
    st.sidebar.warning(
        "No .json files found in that subfolder."
        + ("" if recursive else " Try enabling nested search.")
    )
    st.title("NLI Explanation Reviewer")
    st.stop()
# Show relative paths in the picker so files with the same name in different
# nested subfolders (e.g. recursive mode) stay distinguishable.
file_labels = [str(f.relative_to(browse_path)) for f in json_files]
selected_label = st.sidebar.selectbox("Choose a file", file_labels)
selected_path = json_files[file_labels.index(selected_label)]
reviews_dir = st.sidebar.text_input("Reviews folder (where scores are saved)",
                                     value=str(DEFAULT_REVIEWS_DIR))
review_file_path = reviewer_file_path(reviews_dir, selected_path.stem, reviewer_name or "unnamed")
mtime = selected_path.stat().st_mtime
metadata, results, summary = load_json_file(str(selected_path), mtime)
dataset_name = guess_dataset_name(metadata, selected_path)
model_name = guess_model_name(metadata, selected_path)
reviews_key = f"reviews::{selected_path}::{sanitize_for_filename(reviewer_name or 'unnamed')}"
if reviews_key not in st.session_state:
    st.session_state[reviews_key] = load_json_dict(review_file_path)
reviews = st.session_state[reviews_key]
all_reviews = load_all_reviewers(reviews_dir, selected_path.stem)
# Optional LLM-judge scores, treated as just another "reviewer" for comparison
with st.sidebar.expander("LLM-judge scores (optional)"):
    default_judge_path = str(
        APP_DIR / "phase1_nli_eval" / "judge_scores" / dataset_name / f"{selected_path.stem}__scores.json"
    )
    judge_path_str = st.text_input("Path to judge-scored JSON", value=default_judge_path)
    judge_scores = load_judge_scores(Path(judge_path_str))
    if judge_scores:
        st.caption(f"Loaded {len(judge_scores)} judge scores — available for agreement comparisons below.")
        all_reviews = dict(all_reviews)  # avoid mutating cached-ish structure in place
        for sid, entry in judge_scores.items():
            all_reviews.setdefault(sid, {})["llm_judge"] = entry
    else:
        st.caption("No judge-scored file found at that path yet — that's fine, it's optional.")
if st.session_state.get("current_file") != str(selected_path):
    st.session_state["current_file"] = str(selected_path)
    st.session_state["nav_idx"] = 0
# --------------------------------------------------------------------------
# Header: metadata + summary + progress
# --------------------------------------------------------------------------
st.title("NLI Explanation Reviewer")
st.caption(f"Dataset: `{dataset_name}` · Model: `{model_name}` · File: `{selected_path.name}`")
with st.expander("Dataset metadata & summary", expanded=False):
    c1, c2 = st.columns(2)
    with c1:
        st.markdown("**Metadata**")
        st.json(metadata)
    with c2:
        st.markdown("**Summary (from file)**")
        st.json(summary)
my_reviewed_count = sum(1 for r in results if is_fully_scored(reviews.get(str(r["id"]))))
team_reviewed_count = sum(
    1 for r in results
    if any(is_fully_scored(entry) for entry in all_reviews.get(str(r["id"]), {}).values())
)
reviewer_slugs = sorted({rev for entry in all_reviews.values() for rev in entry})
mcol1, mcol2, mcol3, mcol4, mcol5 = st.columns(5)
mcol1.metric("Total samples", len(results))
mcol2.metric("Scored by you", f"{my_reviewed_count}/{len(results)}")
mcol3.metric("Scored by anyone", f"{team_reviewed_count}/{len(results)}")
if summary.get("accuracy") is not None:
    mcol4.metric("Model accuracy", f"{summary.get('accuracy'):.2%}")
mism = sum(1 for r in results if r.get("success") == 0)
mcol5.metric("Model mismatches", mism)
if reviewer_slugs:
    st.caption("Reviewers with saved data for this file: " + ", ".join(reviewer_slugs))
st.divider()
# --------------------------------------------------------------------------
# Human validation sample (10% per dataset, seed 42)
# --------------------------------------------------------------------------
human_val_path = Path(reviews_dir) / "human_validation_samples.json"
human_val_data = load_json_dict(human_val_path)
with st.sidebar.expander("Human validation sample (10%, seed 42)"):
    st.caption(
        "Per the eval plan: sample 10% of items per dataset (seed 42), "
        "reused across all 9 models. IDs are sorted naturally before "
        "sampling for reproducibility."
    )
    existing_sample = human_val_data.get(dataset_name)
    if existing_sample:
        st.write(f"Sample for `{dataset_name}`: **{len(existing_sample)}** items saved.")
    else:
        st.write(f"No sample generated yet for `{dataset_name}`.")
    if st.button("Generate / verify sample for this dataset"):
        item_ids = [str(r["id"]) for r in results]
        sample_ids = compute_human_validation_sample(item_ids)
        human_val_data[dataset_name] = sample_ids
        save_json_dict(human_val_path, human_val_data)
        st.success(f"Saved {len(sample_ids)} sample IDs for `{dataset_name}` to "
                    f"`{human_val_path}`.")
        st.rerun()
sample_ids_for_dataset = set(human_val_data.get(dataset_name, []))
only_sample = False
if sample_ids_for_dataset:
    only_sample = st.sidebar.checkbox(
        f"Only show human-validation sample ({len(sample_ids_for_dataset)} items)",
        value=False,
    )
st.divider()
# --------------------------------------------------------------------------
# Sidebar: filters
# --------------------------------------------------------------------------
def unique_flat_values(field):
    vals = set()
    for r in results:
        v = r.get(field)
        if isinstance(v, list):
            vals.update(v)
        elif v is not None:
            vals.add(v)
    return sorted(str(v) for v in vals)
st.sidebar.title("Filters")
search_text = st.sidebar.text_input("Search premise / hypothesis / reasoning")
gold_opts = unique_flat_values("gold")
gold_sel = st.sidebar.multiselect("Gold label", gold_opts, default=[])
pred_opts = unique_flat_values("predicted")
pred_sel = st.sidebar.multiselect("Predicted label", pred_opts, default=[])
lang_opts = unique_flat_values("language")
lang_sel = st.sidebar.multiselect("Language", lang_opts, default=[])
source_opts = unique_flat_values("source")
source_sel = st.sidebar.multiselect("Source", source_opts, default=[])
section_opts = unique_flat_values("fracas_sections")
section_sel = st.sidebar.multiselect("FraCaS section", section_opts, default=[])
tag_opts = unique_flat_values("tags")
tag_sel = st.sidebar.multiselect("Tags", tag_opts, default=[])
success_choice = st.sidebar.radio(
    "Model result", ["All", "Success only", "Failure only"], index=0
)
st.sidebar.markdown("**Your scores**")
crit_filters = {}
for ck, cinfo in CRITERIA.items():
    labels = ["Not scored"] + [str(v) for v, _ in cinfo["options"]]
    crit_filters[ck] = st.sidebar.multiselect(f"Your {cinfo['label']} score", labels, default=[])
only_unreviewed = st.sidebar.checkbox("Only show samples not fully scored by you", value=False)
only_unreviewed_by_anyone = st.sidebar.checkbox("Only show samples not scored by anyone", value=False)
def matches_filters(r):
    rid = str(r["id"])
    if search_text:
        hay = " ".join([
            str(r.get("premise", "")),
            str(r.get("hypothesis", "")),
            str(r.get("reasoning", "")),
        ]).lower()
        if search_text.lower() not in hay:
            return False
    if gold_sel:
        g = r.get("gold") or []
        g = g if isinstance(g, list) else [g]
        if not set(str(x) for x in g) & set(gold_sel):
            return False
    if pred_sel and str(r.get("predicted")) not in pred_sel:
        return False
    if lang_sel and str(r.get("language")) not in lang_sel:
        return False
    if source_sel and str(r.get("source")) not in source_sel:
        return False
    if section_sel:
        secs = r.get("fracas_sections") or []
        secs = secs if isinstance(secs, list) else [secs]
        if not set(str(x) for x in secs) & set(section_sel):
            return False
    if tag_sel:
        tags = r.get("tags") or []
        tags = tags if isinstance(tags, list) else [tags]
        if not set(str(x) for x in tags) & set(tag_sel):
            return False
    if success_choice == "Success only" and r.get("success") != 1:
        return False
    if success_choice == "Failure only" and r.get("success") == 1:
        return False
    my_entry = reviews.get(rid)
    for ck, sel in crit_filters.items():
        if not sel:
            continue
        val = my_entry.get(ck) if my_entry else None
        val_label = "Not scored" if val is None else str(val)
        if val_label not in sel:
            return False
    if only_unreviewed and is_fully_scored(my_entry):
        return False
    if only_unreviewed_by_anyone and any(
        is_fully_scored(e) for e in all_reviews.get(rid, {}).values()
    ):
        return False
    if only_sample and rid not in sample_ids_for_dataset:
        return False
    return True
filtered = [r for r in results if matches_filters(r)]
if not filtered:
    st.warning("No samples match the current filters.")
    st.stop()
if st.session_state.get("nav_idx", 0) >= len(filtered):
    st.session_state["nav_idx"] = 0
st.sidebar.markdown(f"**{len(filtered)} / {len(results)} samples match filters**")
# --------------------------------------------------------------------------
# Top-level tabs: blind single-sample review vs. the analysis/library view
# --------------------------------------------------------------------------
tab_review, tab_library = st.tabs(["📝 Review", "📚 Library"])
with tab_review:
    # ----------------------------------------------------------------------
    # Navigation
    # ----------------------------------------------------------------------
    nav_col1, nav_col2, nav_col3, nav_col4 = st.columns([1, 1, 3, 2])
    with nav_col1:
        if st.button("Previous", use_container_width=True, key="top_prev_button"):
            st.session_state["nav_idx"] = max(0, st.session_state["nav_idx"] - 1)
    with nav_col2:
        if st.button("Next", use_container_width=True, key="top_next_button"):
            st.session_state["nav_idx"] = min(len(filtered) - 1, st.session_state["nav_idx"] + 1)
    with nav_col3:
        def _status_marker(r):
            rid = str(r["id"])
            mine = reviews.get(rid)
            if is_fully_scored(mine):
                return " ✅"
            if is_partially_scored(mine):
                return " 🟡"
            if any(is_fully_scored(e) for e in all_reviews.get(rid, {}).values()):
                return " 👥"
            return ""
        idx_labels = [
            f"{i+1}. [{r['id']}]" + _status_marker(r)
            for i, r in enumerate(filtered)
        ]
        jump_idx = st.selectbox(
            "Jump to sample",
            options=list(range(len(filtered))),
            format_func=lambda i: idx_labels[i],
            index=st.session_state["nav_idx"],
            label_visibility="collapsed",
        )
        if jump_idx != st.session_state["nav_idx"]:
            st.session_state["nav_idx"] = jump_idx
    with nav_col4:
        st.write(f"Sample {st.session_state['nav_idx'] + 1} of {len(filtered)}")
    current = filtered[st.session_state["nav_idx"]]
    sample_id = str(current["id"])
    st.divider()
    # ----------------------------------------------------------------------
    # Sample display
    # ----------------------------------------------------------------------
    left, right = st.columns([3, 2])
    with left:
        top_badges = []
        if current.get("language"):
            top_badges.append(f"`{current.get('language')}`")
        if current.get("source"):
            top_badges.append(f"`{current.get('source')}`")
        if current.get("fracas_sections"):
            top_badges.append(f"`{flatten(current.get('fracas_sections'))}`")
        if sample_id in sample_ids_for_dataset:
            top_badges.append("`human-val sample`")
        st.markdown(f"### Sample `{sample_id}`")
        st.markdown("  ".join(top_badges))
        if current.get("tags"):
            st.caption("Gold phenomenon tags: " + flatten(current.get("tags")))
        st.markdown("**Premise**")
        st.info(current.get("premise", ""))
        st.markdown("**Hypothesis**")
        st.info(current.get("hypothesis", ""))
        st.markdown("**Reasoning (model's explanation — this is what you're scoring)**")
        st.write(current.get("reasoning", "_none provided_"))
    with right:
        st.markdown("**Gold label**")
        st.success(flatten(current.get("gold")) or "—")
        st.markdown("**Predicted label**")
        pred_val = current.get("predicted")
        is_success = current.get("success") == 1
        if is_success:
            st.success(str(pred_val))
        else:
            st.error(str(pred_val))
        st.markdown("**Model self-reported result**")
        if current.get("success") == 1:
            st.write("Success (predicted matched gold)")
        elif current.get("success") == 0:
            st.write("Failure (predicted did not match gold)")
        else:
            st.write("— not recorded —")
        if current.get("partial_success") is not None:
            st.write(f"Partial success: {current.get('partial_success')}")
        with st.expander("Raw JSON for this sample"):
            st.json(current)
    st.divider()
    # ----------------------------------------------------------------------
    # Review widget — one score + one comment box per criterion
    # ----------------------------------------------------------------------
    st.markdown("### Your review")
    my_slug = sanitize_for_filename(reviewer_name or "unnamed")
    others = {k: v for k, v in all_reviews.get(sample_id, {}).items() if k != my_slug}
    if others:
        with st.expander(f"{len(others)} other reviewer/judge score(s) exist for this sample (click to reveal)"):
            st.caption("Hidden by default so it doesn't bias your own read — per the plan, "
                        "annotators shouldn't compare notes until both are done.")
            for slug, entry in others.items():
                label = "LLM judge" if slug == "llm_judge" else slug
                parts = []
                for ck, cinfo in CRITERIA.items():
                    v = entry.get(ck)
                    parts.append(f"{cinfo['label']}: {'—' if v is None else v}")
                st.markdown(f"**{label}** — " + " · ".join(parts))
                for ck, cinfo in CRITERIA.items():
                    note = entry.get(f"{ck}_notes")
                    if note:
                        st.caption(f"_{cinfo['label']}:_ {note}")
                if entry.get("general_notes"):
                    st.caption(f"_General:_ {entry['general_notes']}")
    existing = reviews.get(sample_id, {})
    score_values = {}
    note_values = {}
    for ck, cinfo in CRITERIA.items():
        st.markdown(f"**{cinfo['label']}**")
        st.caption(cinfo["help"])
        scol, ncol = st.columns([1, 2])
        with scol:
            opt_values = [v for v, _ in cinfo["options"]]
            opt_labels = {v: lbl for v, lbl in cinfo["options"]}
            current_val = existing.get(ck)
            radio_options = ["Not scored"] + opt_values
            default_idx = 0
            if current_val in opt_values:
                default_idx = radio_options.index(current_val)
            chosen = st.radio(
                "Score",
                radio_options,
                index=default_idx,
                format_func=lambda v: "Not scored" if v == "Not scored" else opt_labels[v],
                key=f"score_{selected_path.name}_{sample_id}_{ck}",
                label_visibility="collapsed",
            )
            score_values[ck] = None if chosen == "Not scored" else chosen
        with ncol:
            note_values[ck] = st.text_area(
                f"Notes on {cinfo['label'].lower()} (optional)",
                value=existing.get(f"{ck}_notes", ""),
                key=f"notes_{selected_path.name}_{sample_id}_{ck}",
                height=90,
            )
        st.markdown("")
    general_notes = st.text_area(
        "General notes (optional, anything not tied to a single criterion)",
        value=existing.get("general_notes", ""),
        key=f"general_notes_{selected_path.name}_{sample_id}",
        height=80,
    )
    save_col1, save_col2 = st.columns([1, 4])
    with save_col1:
        save_disabled = not reviewer_name.strip()
        if st.button("Save review", type="primary", use_container_width=True,
                     disabled=save_disabled):
            entry = {
                "reviewer": reviewer_name,
                "reviewed_at": datetime.now().isoformat(timespec="seconds"),
                "general_notes": general_notes,
            }
            for ck in CRITERION_KEYS:
                entry[ck] = score_values[ck]
                entry[f"{ck}_notes"] = note_values[ck]
            reviews[sample_id] = entry
            st.session_state[reviews_key] = reviews
            save_json_dict(review_file_path, reviews)
            st.toast(f"Saved review for {sample_id}", icon="✅")
    with save_col2:
        if save_disabled:
            st.caption("Enter your name in the sidebar to enable saving.")
        elif existing.get("reviewed_at"):
            t = total_score(existing)
            t_str = f", total {t}/5" if t is not None else ""
            st.caption(f"Last saved: {existing['reviewed_at']} by {existing.get('reviewer') or 'unknown'}{t_str}")
        else:
            st.caption("Not saved yet.")
    st.caption(f"Your reviews are stored in: `{review_file_path}` (nobody else writes to this file).")
    st.divider()
    # ----------------------------------------------------------------------
    # Duplicate Next / Previous, right at the bottom — so you can advance to
    # the next sample immediately after saving, without scrolling back up.
    # ----------------------------------------------------------------------
    bottom_col1, bottom_col2, bottom_col3 = st.columns([1, 1, 3])
    with bottom_col1:
        if st.button("◀ Previous", use_container_width=True, key="bottom_prev_button"):
            st.session_state["nav_idx"] = max(0, st.session_state["nav_idx"] - 1)
    with bottom_col2:
        if st.button("Next ▶", use_container_width=True, key="bottom_next_button"):
            st.session_state["nav_idx"] = min(len(filtered) - 1, st.session_state["nav_idx"] + 1)
    with bottom_col3:
        st.caption("Same as the buttons at the top — handy for saving and moving on in one place.")
with tab_library:
    # ----------------------------------------------------------------------
    # Digital-library view: statistics + open, side-by-side sample inspection
    # (unlike the Review tab, nothing here is hidden — this is for analysis,
    # not blind grading).
    # ----------------------------------------------------------------------
    st.markdown("### 📚 Library — statistics & sample inspection")
    st.caption(
        "Every reviewer's (and the LLM judge's) scores are shown openly, side by side. "
        "Use this tab for analysis; use the Review tab for actual blind grading."
    )
    with st.expander("🔍 Filters (mirrors the sidebar, plus a few extras)", expanded=True):
        lib_col1, lib_col2, lib_col3 = st.columns(3)
        with lib_col1:
            lib_search = st.text_input(
                "Search premise / hypothesis / reasoning", value=search_text, key="lib_search"
            )
            lib_gold_sel = st.multiselect("Gold label", gold_opts, default=gold_sel, key="lib_gold")
            lib_pred_sel = st.multiselect("Predicted label", pred_opts, default=pred_sel, key="lib_pred")
        with lib_col2:
            lib_tag_sel = st.multiselect("Tags", tag_opts, default=tag_sel, key="lib_tags")
            lib_section_sel = st.multiselect(
                "FraCaS section", section_opts, default=section_sel, key="lib_sections"
            )
            lib_success = st.radio(
                "Model result", ["All", "Success only", "Failure only"],
                index=["All", "Success only", "Failure only"].index(success_choice),
                key="lib_success", horizontal=True,
            )
        with lib_col3:
            min_reviewers = st.number_input(
                "Minimum # reviewers (incl. judge)", min_value=0, value=0, step=1, key="lib_min_reviewers"
            )
            only_disagreement = st.checkbox(
                "Only samples where reviewers disagree", value=False, key="lib_disagreement"
            )
            lib_comment_search = st.text_input(
                "Search reviewer comments",
                value="",
                key="lib_comment_search",
                help="Searches every reviewer's and the LLM judge's notes "
                     "(per-criterion notes + general notes) for this sample.",
            )
            only_sample_lib = False
            if sample_ids_for_dataset:
                only_sample_lib = st.checkbox(
                    f"Only human-validation sample ({len(sample_ids_for_dataset)})",
                    value=False, key="lib_only_sample",
                )

    def lib_matches(r):
        rid = str(r["id"])
        if lib_search:
            hay = " ".join([
                str(r.get("premise", "")), str(r.get("hypothesis", "")), str(r.get("reasoning", "")),
            ]).lower()
            if lib_search.lower() not in hay:
                return False
        if lib_gold_sel:
            g = r.get("gold") or []
            g = g if isinstance(g, list) else [g]
            if not set(str(x) for x in g) & set(lib_gold_sel):
                return False
        if lib_pred_sel and str(r.get("predicted")) not in lib_pred_sel:
            return False
        if lib_tag_sel:
            tags = r.get("tags") or []
            tags = tags if isinstance(tags, list) else [tags]
            if not set(str(x) for x in tags) & set(lib_tag_sel):
                return False
        if lib_section_sel:
            secs = r.get("fracas_sections") or []
            secs = secs if isinstance(secs, list) else [secs]
            if not set(str(x) for x in secs) & set(lib_section_sel):
                return False
        if lib_success == "Success only" and r.get("success") != 1:
            return False
        if lib_success == "Failure only" and r.get("success") == 1:
            return False
        if only_sample_lib and rid not in sample_ids_for_dataset:
            return False
        entries = all_reviews.get(rid, {})
        if lib_comment_search:
            needle = lib_comment_search.lower()
            comment_fields = ["general_notes"] + [f"{ck}_notes" for ck in CRITERION_KEYS]
            hay = " ".join(
                str(entry.get(f, "")) for entry in entries.values() for f in comment_fields
            ).lower()
            if needle not in hay:
                return False
        if min_reviewers and len(entries) < min_reviewers:
            return False
        if only_disagreement:
            disagree = False
            for ck in CRITERION_KEYS:
                vals = {e.get(ck) for e in entries.values() if e.get(ck) is not None}
                if len(vals) > 1:
                    disagree = True
                    break
            if not disagree:
                return False
        return True

    lib_filtered = [r for r in results if lib_matches(r)]
    st.caption(f"**{len(lib_filtered)} / {len(results)}** samples match library filters.")

    if not lib_filtered:
        st.warning("No samples match the current library filters.")
    else:
        # -------------------------------------------------------------
        # Statistical overview
        # -------------------------------------------------------------
        st.markdown("#### 📊 Statistical overview")
        comp_col1, comp_col2, comp_col3 = st.columns(3)
        n_total_lib = len(lib_filtered)
        n_you_lib = sum(1 for r in lib_filtered if is_fully_scored(reviews.get(str(r["id"]))))
        n_anyone_lib = sum(
            1 for r in lib_filtered
            if any(is_fully_scored(e) for e in all_reviews.get(str(r["id"]), {}).values())
        )
        comp_col1.metric("Scored by you", f"{n_you_lib}/{n_total_lib}")
        comp_col2.metric("Scored by anyone", f"{n_anyone_lib}/{n_total_lib}")
        comp_col3.metric("Not yet scored", n_total_lib - n_anyone_lib)

        stat_col1, stat_col2 = st.columns(2)
        with stat_col1:
            st.markdown("**Score distribution per criterion (all reviewers + judge)**")
            for ck, cinfo in CRITERIA.items():
                vals = []
                for r in lib_filtered:
                    rid = str(r["id"])
                    for entry in all_reviews.get(rid, {}).values():
                        v = entry.get(ck)
                        if v is not None:
                            vals.append(v)
                st.caption(cinfo["label"])
                if vals:
                    dist = pd.Series(vals).value_counts().sort_index()
                    dist.index = dist.index.astype(str)
                    st.bar_chart(dist)
                else:
                    st.caption("_No scores yet._")
        with stat_col2:
            st.markdown("**Average score per reviewer**")
            all_slugs = sorted({
                slug for r in lib_filtered for slug in all_reviews.get(str(r["id"]), {})
            })
            per_reviewer_rows = []
            for slug in all_slugs:
                row = {"reviewer": "LLM judge" if slug == "llm_judge" else slug}
                for ck, cinfo in CRITERIA.items():
                    vals = [
                        all_reviews[str(r["id"])][slug].get(ck)
                        for r in lib_filtered
                        if slug in all_reviews.get(str(r["id"]), {})
                        and all_reviews[str(r["id"])][slug].get(ck) is not None
                    ]
                    row[cinfo["label"]] = round(sum(vals) / len(vals), 2) if vals else None
                n_scored = sum(
                    1 for r in lib_filtered
                    if is_fully_scored(all_reviews.get(str(r["id"]), {}).get(slug))
                )
                row["fully scored"] = f"{n_scored}/{len(lib_filtered)}"
                per_reviewer_rows.append(row)
            if per_reviewer_rows:
                st.dataframe(pd.DataFrame(per_reviewer_rows), hide_index=True, width="stretch")
            else:
                st.caption("No reviewer data yet for the current filter.")

        st.divider()
        # -------------------------------------------------------------
        # Sample browser
        # -------------------------------------------------------------
        st.markdown("#### 🗂️ Sample browser")
        browser_rows = []
        for r in lib_filtered:
            rid = str(r["id"])
            entries = all_reviews.get(rid, {})
            totals = [total_score(e) for e in entries.values() if total_score(e) is not None]
            browser_rows.append({
                "id": rid,
                "premise": (r.get("premise") or "")[:80],
                "gold": flatten(r.get("gold")),
                "predicted": r.get("predicted"),
                "success": r.get("success"),
                "# reviewers": len(entries),
                "avg total (of 5)": round(sum(totals) / len(totals), 2) if totals else None,
                "your total": total_score(reviews.get(rid)),
            })
        browser_df = pd.DataFrame(browser_rows)
        st.dataframe(browser_df, hide_index=True, width="stretch", height=300)

        st.markdown("#### 🔎 Inspect a sample (all reviewers shown together)")
        lib_ids = [row["id"] for row in browser_rows]
        lib_selected_id = st.selectbox("Choose a sample to inspect", lib_ids, key="lib_inspect_select")
        lib_sample = next(r for r in lib_filtered if str(r["id"]) == lib_selected_id)

        li_left, li_right = st.columns([3, 2])
        with li_left:
            st.markdown(f"**Sample `{lib_selected_id}`**")
            if lib_sample.get("tags"):
                st.caption("Gold phenomenon tags: " + flatten(lib_sample.get("tags")))
            st.markdown("**Premise**")
            st.info(lib_sample.get("premise", ""))
            st.markdown("**Hypothesis**")
            st.info(lib_sample.get("hypothesis", ""))
            st.markdown("**Reasoning**")
            st.write(lib_sample.get("reasoning", "_none provided_"))
        with li_right:
            st.markdown("**Gold label**")
            st.success(flatten(lib_sample.get("gold")) or "—")
            st.markdown("**Predicted label**")
            if lib_sample.get("success") == 1:
                st.success(str(lib_sample.get("predicted")))
            else:
                st.error(str(lib_sample.get("predicted")))
            with st.expander("Raw JSON for this sample"):
                st.json(lib_sample)

        st.markdown("**All reviews for this sample**")
        lib_entries = all_reviews.get(lib_selected_id, {})
        if not lib_entries:
            st.caption("No reviews saved yet for this sample.")
        else:
            for slug, entry in lib_entries.items():
                label = "LLM judge" if slug == "llm_judge" else slug
                with st.container(border=True):
                    parts = []
                    for ck, cinfo in CRITERIA.items():
                        v = entry.get(ck)
                        parts.append(f"{cinfo['label']}: {'—' if v is None else v}")
                    t = total_score(entry)
                    t_str = f" (total {t}/5)" if t is not None else ""
                    st.markdown(f"**{label}**{t_str} — " + " · ".join(parts))
                    for ck, cinfo in CRITERIA.items():
                        note = entry.get(f"{ck}_notes")
                        if note:
                            st.caption(f"_{cinfo['label']}:_ {note}")
                    if entry.get("general_notes"):
                        st.caption(f"_General:_ {entry['general_notes']}")
                    if entry.get("reviewed_at"):
                        st.caption(f"Reviewed at: {entry['reviewed_at']}")
# --------------------------------------------------------------------------
# Agreement (Cohen's kappa) — matches the plan's decision rule (kappa >= 0.7)
# --------------------------------------------------------------------------
with st.sidebar.expander("Agreement between two reviewers"):
    compare_options = reviewer_slugs + (["llm_judge"] if judge_scores else [])
    compare_options = sorted(set(compare_options))
    if len(compare_options) < 2:
        st.caption("Need at least two reviewers (or a reviewer + the LLM judge) "
                    "with saved scores to compute agreement.")
    else:
        a_slug = st.selectbox("Reviewer A", compare_options, index=0, key="kappa_a")
        b_default = 1 if len(compare_options) > 1 else 0
        b_slug = st.selectbox("Reviewer B", compare_options, index=b_default, key="kappa_b")
        if a_slug == b_slug:
            st.caption("Pick two different reviewers to compare.")
        else:
            rows = []
            for ck, cinfo in CRITERIA.items():
                a_vals, b_vals = [], []
                for r in results:
                    rid = str(r["id"])
                    entry_a = all_reviews.get(rid, {}).get(a_slug)
                    entry_b = all_reviews.get(rid, {}).get(b_slug)
                    a_vals.append(entry_a.get(ck) if entry_a else None)
                    b_vals.append(entry_b.get(ck) if entry_b else None)
                kappa, n = cohen_kappa(a_vals, b_vals)
                rows.append({
                    "criterion": cinfo["label"],
                    "kappa": None if kappa is None else round(kappa, 3),
                    "n_common": n,
                    "meets_0.7": (kappa is not None and kappa >= 0.7),
                })
            kappa_df = pd.DataFrame(rows)
            st.dataframe(kappa_df, hide_index=True, use_container_width=True)
            if kappa_df["kappa"].isnull().any() or (kappa_df["n_common"] == 0).any():
                st.caption("No overlap yet on some criteria — both reviewers need to score the same samples.")
            elif kappa_df["meets_0.7"].all():
                st.success("All three criteria meet kappa >= 0.7 — per the plan, judge/human scores stand.")
            else:
                failing = kappa_df.loc[~kappa_df["meets_0.7"], "criterion"].tolist()
                st.warning("Below kappa = 0.7 on: " + ", ".join(failing) +
                           " — plan says fall back to full human annotation for these.")
# --------------------------------------------------------------------------
# Export
# --------------------------------------------------------------------------
with st.sidebar.expander("Export"):
    st.markdown("**Your scores, in the plan's spreadsheet column order**")
    if reviews:
        own_rows = []
        for r in results:
            rid = str(r["id"])
            rv = reviews.get(rid, {})
            own_rows.append({
                "item_id": rid,
                "model": model_name,
                "premise": r.get("premise", ""),
                "hypothesis": r.get("hypothesis", ""),
                "gold": flatten(r.get("gold")),
                "predicted": r.get("predicted"),
                "tags": flatten(r.get("tags")),
                "reasoning": r.get("reasoning", ""),
                "phenomenon_id": rv.get("phenomenon_id"),
                "phenomenon_id_notes": rv.get("phenomenon_id_notes", ""),
                "soundness": rv.get("soundness"),
                "soundness_notes": rv.get("soundness_notes", ""),
                "consistency": rv.get("consistency"),
                "consistency_notes": rv.get("consistency_notes", ""),
                "general_notes": rv.get("general_notes", ""),
                "reviewed_at": rv.get("reviewed_at", ""),
            })
        own_df = pd.DataFrame(own_rows)
        st.download_button(
            f"Download your scores (human_scores_{my_slug}.csv)",
            data=own_df.to_csv(index=False).encode("utf-8"),
            file_name=f"human_scores_{my_slug}.csv",
            mime="text/csv",
        )
    else:
        st.caption("You haven't saved any scores for this file yet.")
    st.markdown("**Everyone's scores (long format, one row per sample x reviewer)**")
    if all_reviews:
        export_rows = []
        for r in results:
            rid = str(r["id"])
            entries = all_reviews.get(rid, {})
            base = {
                "id": rid,
                "model": model_name,
                "gold": flatten(r.get("gold")),
                "predicted": r.get("predicted"),
                "tags": flatten(r.get("tags")),
                "model_success": r.get("success"),
            }
            if not entries:
                export_rows.append({**base, "reviewer": "", "phenomenon_id": None,
                                     "soundness": None, "consistency": None, "total": None,
                                     "general_notes": "", "reviewed_at": ""})
            else:
                for slug, rv in entries.items():
                    export_rows.append({
                        **base,
                        "reviewer": rv.get("reviewer", slug),
                        "phenomenon_id": rv.get("phenomenon_id"),
                        "soundness": rv.get("soundness"),
                        "consistency": rv.get("consistency"),
                        "total": total_score(rv),
                        "general_notes": rv.get("general_notes", ""),
                        "reviewed_at": rv.get("reviewed_at", ""),
                    })
        export_df = pd.DataFrame(export_rows)
        st.download_button(
            "Download all reviewers + judge as CSV",
            data=export_df.to_csv(index=False).encode("utf-8"),
            file_name=f"{selected_path.stem}.all_reviews.csv",
            mime="text/csv",
        )
    else:
        st.caption("No reviews saved yet for this file.")
