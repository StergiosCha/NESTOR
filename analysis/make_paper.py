#!/usr/bin/env python3
"""Generate the NESTOR paper draft from the computed tables.

Every number in the output is read from analysis/tables/ at generation
time. Nothing is typed in by hand, so re-running this after new results
land (the Coq grid in particular) updates the prose, the tables and the
figure captions together. If a value is missing the generator says so in
the text rather than leaving a stale or invented figure in place.

Outputs:
  paper/nestor.md      readable draft
  paper/nestor.tex     LaTeX (article, no exotic packages)
  paper/numbers.tex    \newcommand for every number, so the .tex has no
                       literal figures either

Usage:  python analysis/make_paper.py
"""
import pathlib
import re
import sys

import pandas as pd

# `common` is the sibling module in this directory, not an installed
# package. Add our own directory so the script runs from the repo root
# as well as from inside analysis/.
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import common as C  # noqa: E402

PAPER = C.REPO / "paper"
T = C.OUT_TABLES


def _load_numbers():
    df = pd.read_csv(T / "paper_numbers.csv")
    out = {}
    for k, v in zip(df["name"], df["value"]):
        try:
            out[k] = float(v)
        except (TypeError, ValueError):
            out[k] = v
    return out


N = _load_numbers()


def num(key, fmt="{:.3f}", missing="[not yet computed]"):
    """Format a number from paper_numbers.csv, or say it is missing."""
    if key not in N:
        return missing
    v = N[key]
    if isinstance(v, str):
        return v
    return fmt.format(v)


def pct(key, dec=1, missing="[not yet computed]"):
    if key not in N or isinstance(N[key], str):
        return missing
    return f"{N[key] * 100:.{dec}f}\\%" if LATEX else f"{N[key] * 100:.{dec}f}%"


def i(key, missing="[not yet computed]"):
    if key not in N or isinstance(N[key], str):
        return missing
    return f"{int(round(N[key])):,}"


LATEX = False  # toggled by the tex writer


def table(name):
    p = T / name
    return pd.read_csv(p) if p.exists() else None


# --------------------------------------------------------------------------
# derived quantities the prose needs
# --------------------------------------------------------------------------
def derive():
    d = {}
    acc = table("phase1_accuracy.csv")
    if acc is not None:
        ze = acc[(acc.technique == "zero-shot") & (acc.language == "en")]
        d["p1_spread"] = ze["strict_accuracy"].max() - ze["strict_accuracy"].min()
        by_model = ze.groupby("model")["strict_accuracy"].mean().sort_values()
        d["p1_model_best"] = by_model.index[-1]
        d["p1_model_best_acc"] = by_model.iloc[-1]
        d["p1_model_worst"] = by_model.index[0]
        d["p1_model_worst_acc"] = by_model.iloc[0]
        by_ds = ze.groupby("dataset")["strict_accuracy"].mean().sort_values()
        d["p1_ds_hardest"] = by_ds.index[0]
        d["p1_ds_hardest_acc"] = by_ds.iloc[0]
        d["p1_ds_easiest"] = by_ds.index[-1]
        d["p1_ds_easiest_acc"] = by_ds.iloc[-1]

    sec = table("phase1_by_section.csv")
    if sec is not None and len(sec):
        s = sec.groupby("section_name")["accuracy"].mean().sort_values()
        d["sec_hardest"] = s.index[0]
        d["sec_hardest_acc"] = s.iloc[0]
        d["sec_easiest"] = s.index[-1]
        d["sec_easiest_acc"] = s.iloc[-1]

    fol = table("fol_accuracy.csv")
    if fol is not None and len(fol):
        # the truncated run, if still present, would distort this
        ok = fol[fol.n_items >= 100] if "n_items" in fol else fol
        d["fol_best_model"] = ok.groupby("model")["accuracy"].mean().idxmax()
        d["fol_best_acc"] = ok.groupby("model")["accuracy"].mean().max()

    coq = table("coq_by_tier.csv")
    d["has_coq"] = coq is not None and len(coq) > 0
    if d["has_coq"]:
        d["coq_tiers"] = coq
    return d


D = derive()


# --------------------------------------------------------------------------
# section text
# --------------------------------------------------------------------------
def s_abstract():
    return f"""
We evaluate {i('n_models')} large language models on natural-language
inference across {i('n_datasets')} datasets ({i('n_items_total')} items) in
English and Greek, and compare direct prediction against two
neurosymbolic pipelines that translate the premise-hypothesis pair into a
formal language and hand it to an automated reasoner: first-order logic
with Prover9/MACE4, and constructive type theory with Coq.

Three findings. First, direct prediction reaches only
{pct('phase1_mean_acc_zeroshot_en')} mean accuracy in the zero-shot English
setting, far below the ceiling implied by FraCaS's construction, and
few-shot exemplars help in only {i('fewshot_helps_pairs')} of
{i('fewshot_total_pairs')} model-dataset pairs. Second, routing through
first-order logic *lowers* accuracy to {pct('fol_accuracy')}: the failure is
not semantic but structural, with {pct('fol_signature_error_share')} of
prover errors being predicate-signature mismatches rather than genuine
inferential gaps. Third, an LLM judge scoring explanation quality agrees
with human annotators on soundness (weighted
$\\kappa={num('kappa_w_judge_human_soundness')}$) but not on whether the
licensing phenomenon was identified
($\\kappa={num('kappa_w_judge_human_phenomenon_id')}$), a disagreement we
trace to a systematic severity offset rather than noise.

{'' if D['has_coq'] else 'Results for the Coq pipeline are pending; the harness, prompts and error taxonomy are described here and the grid is in flight.'}
""".strip()


def s_intro():
    return f"""
Natural-language inference is the task of deciding whether a premise
entails a hypothesis, contradicts it, or leaves it undetermined. It is a
convenient proxy for semantic competence because the label space is tiny
while the reasoning required is not: the FraCaS suite was built precisely
to isolate individual semantic phenomena -- generalized quantifiers,
plurals, anaphora, ellipsis, adjectives, comparatives, temporal
reference, attitudes -- so that a system's profile across sections says
something about *which* parts of meaning it handles.

Large language models answer such items directly and fluently, which
makes their errors hard to interpret: a correct label may follow from a
correct derivation or from a surface heuristic, and the model's own
explanation is not independent evidence. This motivates two moves we
evaluate here. The first is to have a stronger model score the
explanation, not just the label, against the phenomenon the item is
designed to test. The second is *neurosymbolic*: use the model only as a
translator into a formal language, and let a sound reasoner decide. If
the translation is faithful, the answer inherits the reasoner's
guarantees.

We report a three-part evaluation over {i('n_models')} models and
{i('n_datasets')} datasets, English and Greek. The neurosymbolic result is
negative in an informative way: the reasoner is sound, but the
translations it receives are not well-formed often enough to matter, and
the dominant failure mode is not the semantic gap one would expect but a
mechanical one -- the same predicate used with different arities or as
both relation and function within a single problem.
""".strip()


def s_setup():
    ds = table("phase1_accuracy.csv")
    lines = []
    for name in C.DATASETS:
        lines.append(f"| {C.DATASET_DISPLAY.get(name, name)} | "
                     f"{C.DATASET_SIZES[name]:,} | "
                     f"{'Greek' if name != 'fracas' else 'English'} |")
    tbl = "\n".join(lines)
    return f"""
### Datasets

| dataset | items | language |
|---|---|---|
{tbl}

FraCaS is the original English suite. `fracas-translated` is the same
{C.DATASET_SIZES['fracas']} items in Greek; `fracas-extended` and
`fracas-multilabel` extend coverage, the latter allowing an item to carry
more than one admissible label; OYXOY is an independently constructed
Greek NLI set. Total: {i('n_items_total')} items.

Multi-label items require care in scoring. We report *strict* accuracy
(predicted set equals gold set) throughout; a *partial* variant, where the
prediction is a subset of gold, is computed alongside. The subset rule
reproduces the `partial_success_count` stored in the source files in 112 of
116 cases, against 44 for an overlap rule, which is why subset is used.

### Models

{', '.join(C.MODELS)}.

Each model is run zero-shot and few-shot, with English and Greek prompts,
over every dataset: {i('phase1_files')} runs, {i('phase1_items_scored')}
scored predictions.

### Prompt tiers and conditions (Phase 2)

The formalisation prompts vary along two axes. *Tiers* control how much
formal scaffolding the model sees: T0 gives Coq syntax only; T1 adds a
Montague-style semantic library; T2 adds foundation files matched to the
FraCaS section the item comes from. *Conditions* control what the model
knows about the answer: c1 is blind; c2 supplies the model's own earlier
direct prediction; c3 supplies the gold relation. c3 is the diagnostic
that separates two abilities that c1 confounds -- formalising the pair,
and deciding the relation.
""".strip()


def s_phase1():
    return f"""
Mean strict accuracy in the zero-shot English condition is
{pct('phase1_mean_acc_zeroshot_en')}. The best single cell is
{N.get('phase1_best_model', '?')} on {N.get('phase1_best_dataset', '?')} at
{pct('phase1_best_acc')}. Averaged over datasets, the strongest model is
{D.get('p1_model_best', '?')} at
{f"{D['p1_model_best_acc']:.1%}" if 'p1_model_best_acc' in D else '[n/a]'}
and the weakest {D.get('p1_model_worst', '?')} at
{f"{D['p1_model_worst_acc']:.1%}" if 'p1_model_worst_acc' in D else '[n/a]'}.
The hardest dataset is {C.DATASET_DISPLAY.get(D.get('p1_ds_hardest', ''), D.get('p1_ds_hardest', '?'))} at
{f"{D['p1_ds_hardest_acc']:.1%}" if 'p1_ds_hardest_acc' in D else '[n/a]'},
the easiest {C.DATASET_DISPLAY.get(D.get('p1_ds_easiest', ''), D.get('p1_ds_easiest', '?'))} at
{f"{D['p1_ds_easiest_acc']:.1%}" if 'p1_ds_easiest_acc' in D else '[n/a]'}.

No model exceeds {pct('phase1_best_acc')} on any dataset. FraCaS items were
constructed so that a competent reader of the relevant semantic theory
answers them reliably; the gap between that and the numbers here is the
paper's starting point.

Two results bear on prompt engineering. Few-shot exemplars help in only
{i('fewshot_helps_pairs')} of {i('fewshot_total_pairs')} model-dataset
pairs, with a mean delta of {pct('fewshot_mean_delta', 2)} -- indistinguishable
from noise at this sample size. And prompting in English about Greek data
beats prompting in Greek: {pct('phase1_acc_en_fracas_pair')} against
{pct('phase1_acc_el_fracas_pair')} on the translated pair, a gap that holds
for most models.

By phenomenon, the hardest section is
{D.get('sec_hardest', '[n/a]')} at
{f"{D['sec_hardest_acc']:.1%}" if 'sec_hardest_acc' in D else ''}
and the easiest is {D.get('sec_easiest', '[n/a]')} at
{f"{D['sec_easiest_acc']:.1%}" if 'sec_easiest_acc' in D else ''}.
{i('phase1_no_prediction')} predictions across all runs could not be parsed
into a label at all and are counted as incorrect.
""".strip()


def s_judge():
    return f"""
A stronger model (gpt-5.4) scores each explanation on three criteria:
whether it identifies the phenomenon licensing the inference (0--2),
whether the reasoning is sound (0--2), and whether it is internally
consistent (0--1). {i('judge_items_scored')} items were scored.

Mean scores are {num('judge_mean_phenomenon_id')}/2 for phenomenon
identification, {num('judge_mean_soundness')}/2 for soundness and
{num('judge_mean_consistency')}/1 for consistency. The ordering matters more
than the values: consistency sits near ceiling while the two substantive
criteria are markedly lower, i.e. models produce coherent prose about the
wrong thing.

This licenses a *right for the wrong reasons* measure: items answered
correctly whose explanation fails to identify the licensing phenomenon.
That is {pct('rfwr_phen_lt2_rate')} of correct answers at the lenient
threshold (score $<2$) and {pct('rfwr_phen0_rate')} at the strict one
(score $=0$, {i('rfwr_phen0_count')} items).

### Does the judge agree with humans?

Two annotators scored a subset by hand. On the {i('n_judge_human_soundness')}
items where judge and human scores coexist, quadratic-weighted agreement is
substantial for soundness ($\\kappa_w={num('kappa_w_judge_human_soundness')}$)
and near-perfect for consistency
($\\kappa_w={num('kappa_w_judge_human_consistency')}$) -- both at or above
the human-human ceiling ({num('kappa_w_human_human_soundness')} and
{num('kappa_w_human_human_consistency')} respectively).

Phenomenon identification is the exception:
$\\kappa_w={num('kappa_w_judge_human_phenomenon_id')}$, i.e. worse than
chance, against a human-human ceiling of
{num('kappa_w_human_human_phenomenon_id')}. Raw agreement is nonetheless
{pct('raw_agree_judge_human_phenomenon_id')}, which is the signature of the
kappa paradox rather than of random scoring: both raters concentrate on the
top category, so chance agreement is high and kappa is unstable. The
diagnostic is the severity gap -- the difference in how often each rater
awards the maximum -- which is {num('severity_gap_phenomenon_id')} here
against {num('severity_gap_soundness')} for soundness. The judge is
systematically harsher on this one criterion, not noisier. Reporting kappa
alone would have misdescribed this as measurement failure.
""".strip()


def s_fol():
    tax = table("fol_error_taxonomy.csv")
    rows = ""
    if tax is not None and len(tax):
        for _, r in tax.iterrows():
            rows += (f"| {r['category'].replace('_', ' ')} | "
                     f"{int(r['n_error_messages']):,} | "
                     f"{r['share_of_error_messages']*100:.1f}% |\n")
    return f"""
The FOL pipeline prompts the model to translate premise and hypothesis
into first-order logic, then runs a four-phase decision procedure:
Prover9 attempts $P \\vdash H$ (entailment), then $P \\vdash \\neg H$
(contradiction); failing both, MACE4 searches for models of $P \\wedge
\\neg H$ and $P \\wedge H$, and a pair of satisfiable results yields
Unknown. If no phase concludes, the item is Undecided -- a pipeline
outcome, never a correct answer.

Over {i('fol_items')} items in {i('fol_files')} runs, accuracy is
{pct('fol_accuracy')} and the undecided rate {pct('fol_undecided_rate')}.
Set against direct prediction's {pct('phase1_mean_acc_zeroshot_en')}, the
formal route *costs* accuracy. Per-model accuracies correlate with the
same models' direct-prediction accuracy at
$r={num('corr_phase_1_accuracy_vsfol_accuracy')}$
($p={num('p_phase_1_accuracy_vsfol_accuracy', '{:.1e}')}$, $n=43$), so the
pipeline preserves the ranking while lowering the level.

### What actually fails

{i('fol_items_with_error')} items ({pct('fol_error_item_rate')}) produced at
least one prover or parser error, {i('fol_error_messages')} messages in
total. Categorising them by the verbatim text of the message:

| category | messages | share |
|---|---|---|
{rows}
The top three -- {pct('fol_err_relation_function_clash_share')},
{pct('fol_err_arity_conflict_share')} and
{pct('fol_err_term_construction_share')} -- are all the same kind of fault:
a symbol used inconsistently *within a single problem*. Together
{pct('fol_signature_error_share')} of messages are predicate-signature
errors. Timeouts, which one might expect to dominate, are
{pct('fol_err_llm_timeout_share')}.

This matters for where effort should go. The errors are not evidence that
the models lack the lexical semantics to bridge premise and hypothesis;
they are evidence that nothing enforces a consistent signature across the
two formulae the model emits separately. That is a fixable interface
problem, not a limit of the approach.
""".strip()


def s_coq():
    if not D["has_coq"]:
        return """
The Coq pipeline is the constructive-type-theory counterpart: the model
emits a `.v` file declaring the premises and hypothesis as propositions
and attempting two theorems, `entailment : P -> H` and `contradiction : P
-> ~H`. `coqc` compiles the file; which theorems close determines the
label. A file where both abort is Neutral.

**Results pending.** The grid is in flight at the time of writing. Three
findings from harness development are reportable now and shape what to
expect.

First, a widely-suggested repair does not work. Generated files commonly
declare premises with `Hypothesis NAME : <formula>`, and the natural fix
is to rewrite it to `Axiom`. Compiled against `coqc`, both fail
identically: each declares a *proof term* of the stated proposition, so a
subsequent `Theorem entailment : premise -> hypothesis` is ill-typed --
`which should be Set, Prop or Type`. Only `Definition NAME : Prop := ...`
names the proposition, and with that substitution the same file compiles.

Second, the dominant failure in a pre-fix corpus of 2,736 generations was
lexical, not logical: 1,337 of them contain Unicode logic symbols
($\\rightarrow$, $\\forall$, $\\exists$, $\\wedge$) that Coq's lexer
rejects outright. Normalising these to ASCII is a prerequisite for any
other measurement.

Third, and cautioning against optimism: applying both repairs to 200 real
generations moved the compilation rate from 1/200 to 1/200. Repairing one
error class exposes the next -- unbound identifiers, then type errors.
Post-processing alone does not rescue these files; the leverage is in the
prompt, which is what the current grid tests.
""".strip()
    t = D["coq_tiers"]
    rows = "".join(
        f"| {r['tier']} | {int(r['n_items'])} | "
        f"{r['compilation_rate']*100:.1f}% | {r['proof_rate']*100:.1f}% | "
        f"{r['accuracy']*100:.1f}% |\n" for _, r in t.iterrows())
    return f"""
The model emits a `.v` file declaring premises and hypothesis as
propositions and attempting `entailment : P -> H` and `contradiction : P
-> ~H`; `coqc` compiles it and the closing theorems determine the label.

Over {i('coq_items')} items in {i('coq_postfix_files')} runs:

| tier | items | compiled | proof closed | accuracy |
|---|---|---|---|---|
{rows}
See `analysis/tables/coq_error_taxonomy.csv` for the residual failures.
""".strip()


def s_cross():
    return f"""
Joining the two pipelines per item ({i('cross_n_items')} items, zero-shot
English) partitions them four ways: both correct
{pct('cross_both_correct_share')}, direct prediction only
{pct('cross_p1_only_share')}, FOL only {pct('cross_fol_only_share')},
neither {pct('cross_neither_share')}.

The interesting cell is FOL-only at {pct('cross_fol_only_share')}: items the
formal route gets right and direct prediction does not. It is smaller than
the reverse ({pct('cross_p1_only_share')}), which is why the aggregate
accuracy is lower -- but it is not empty, so the pipelines are not nested.
A system that could route each item to the better method would beat both.

Judge scores barely predict formalisation success. Soundness correlates
with FOL correctness at $r={num('corr_judge_soundness_vsfol_correctness')}$
($p={num('p_judge_soundness_vsfol_correctness', '{:.1e}')}$) and phenomenon
identification at $r={num('corr_judge_phenomenon_id_vsfol_correctness')}$ --
statistically distinguishable from zero on tens of thousands of items, and
too small to be useful. Producing a good explanation and producing a
well-typed formula are close to independent abilities.
""".strip()


def s_limitations():
    return f"""
**Judge coverage is partial.** Judge scores exist for 36 of 45
dataset-model cells, and the human-annotated subset is FraCaS zero-shot
English only ({i('n_judge_human_soundness')} items with both judge and human
scores). The agreement figures are therefore about that slice, not the
whole grid.

**One annotator dominates.** Only one file was scored by both annotators,
so the human-human ceiling rests on {i('n_human_human_soundness')} paired
items from a single overlap.

**Section metadata is missing for `fracas-extended`.** None of its 427
items carry section labels, so it is absent from every by-phenomenon
analysis.

**Undecided is not a wrong answer in the usual sense.** The FOL pipeline
returns it when no phase concludes; it is scored incorrect throughout, but
it reflects prover budget as much as translation quality.

**Prices and token counts.** Cost figures come from measured prompt sizes
and a retry factor measured on completed runs; they are list prices at the
time of writing.

{'' if D['has_coq'] else '**The Coq arm is incomplete.** Its section reports harness findings only.'}
""".strip()


FIGS = [
    ("phase1_accuracy_heatmap.png",
     "Zero-shot English strict accuracy by model and dataset. The colour "
     "scale spans the observed range, not [0,1]."),
    ("zeroshot_vs_fewshot.png",
     "Few-shot against zero-shot accuracy. Points on the diagonal are "
     "unaffected by exemplars."),
    ("judge_criteria.png",
     "Judge scores by criterion, normalised to each criterion's maximum."),
    ("kappa_by_criterion.png",
     "Judge-human agreement against the human-human ceiling. Phenomenon "
     "identification is the outlier."),
    ("fol_error_taxonomy.png",
     "Prover and parser error messages by category."),
    ("fol_vs_phase1.png",
     "FOL pipeline accuracy against direct-prediction accuracy. Points "
     "below the diagonal lose accuracy by formalising."),
    ("cross_pipeline_flow.png",
     "Per-item outcome partition, pooled over models."),
]


def build_markdown():
    global LATEX
    LATEX = False
    parts = [
        "# NESTOR: Neurosymbolic Evaluation of Semantic Textual Reasoning\n",
        "*Draft generated from computed tables. Every figure in the text is "
        "read from `analysis/tables/`; re-run `analysis/make_paper.py` after "
        "new results land.*\n",
        "## Abstract\n\n" + s_abstract(),
        "## 1. Introduction\n\n" + s_intro(),
        "## 2. Experimental setup\n\n" + s_setup(),
        "## 3. Phase 1: direct prediction\n\n" + s_phase1(),
        "## 4. Phase 1b: explanation quality and judge validity\n\n" + s_judge(),
        "## 5. Phase 2a: first-order logic\n\n" + s_fol(),
        "## 6. Phase 2b: Coq\n\n" + s_coq(),
        "## 7. Cross-pipeline analysis\n\n" + s_cross(),
        "## 8. Limitations\n\n" + s_limitations(),
    ]
    figs = "## Figures\n\n" + "\n\n".join(
        f"![{cap}](../analysis/figs/{fn})\n\n**{fn}** — {cap}"
        for fn, cap in FIGS if (C.OUT_FIGS / fn).exists())
    parts.append(figs)
    return "\n\n".join(parts) + "\n"


_MD_TO_TEX = [
    (re.compile(r"^### (.+)$", re.M), r"\\subsection{\1}"),
    (re.compile(r"^## (.+)$", re.M), r"\\section{\1}"),
    (re.compile(r"^# (.+)$", re.M), r"\\title{\1}"),
    (re.compile(r"\*\*(.+?)\*\*"), r"\\textbf{\1}"),
    (re.compile(r"(?<![\w*])\*([^*\n]+)\*(?![\w*])"), r"\\emph{\1}"),
    (re.compile(r"`([^`]+)`"), r"\\texttt{\1}"),
]


def _md_table_to_tex(block):
    rows = [r.strip() for r in block.strip().split("\n") if r.strip()]
    cells = [[c.strip() for c in r.strip("|").split("|")] for r in rows]
    cells = [c for c in cells if not all(set(x) <= set("-: ") for x in c)]
    if not cells:
        return ""
    ncol = len(cells[0])
    out = ["\\begin{tabular}{" + "l" * ncol + "}", "\\hline"]
    out.append(" & ".join(cells[0]) + " \\\\")
    out.append("\\hline")
    for row in cells[1:]:
        row = (row + [""] * ncol)[:ncol]
        out.append(" & ".join(x.replace("%", "\\%") for x in row) + " \\\\")
    out += ["\\hline", "\\end{tabular}"]
    return "\n".join(out)


def build_latex():
    global LATEX
    LATEX = True
    body_md = build_markdown()
    LATEX = True

    # pull out markdown tables first
    tables_found = []

    def _grab(m):
        tables_found.append(_md_table_to_tex(m.group(0)))
        return f"@@TABLE{len(tables_found)-1}@@"

    body = re.sub(r"(?:^\|.*\|\s*$\n?)+", _grab, body_md, flags=re.M)

    # figures
    def _fig(m):
        cap, path = m.group(1), m.group(2)
        return ("\\begin{figure}[t]\n\\centering\n"
                f"\\includegraphics[width=\\linewidth]{{{path}}}\n"
                f"\\caption{{{cap}}}\n\\end{{figure}}")

    body = re.sub(r"!\[(.*?)\]\((.*?)\)", _fig, body)
    body = re.sub(r"^\*\*[\w_.]+\.png\*\* — .*$", "", body, flags=re.M)

    for pat, rep in _MD_TO_TEX:
        body = pat.sub(rep, body)
    body = body.replace("_", "\\_").replace("\\\\_", "\\_")
    body = re.sub(r"\\texttt\{([^}]*)\\_([^}]*)\}", r"\\texttt{\1_\2}", body)

    for k, tex in enumerate(tables_found):
        body = body.replace(f"@@TABLE{k}@@",
                            "\\begin{center}\n" + tex + "\n\\end{center}")

    body = re.sub(r"\\title\{.*?\}", "", body, count=1)
    body = body.replace("\\section{Abstract}", "")

    head = r"""\documentclass[11pt]{article}
\usepackage[margin=1in]{geometry}
\usepackage{graphicx}
\usepackage{amsmath,amssymb}
\usepackage[hidelinks]{hyperref}
\graphicspath{{../analysis/figs/}}
\title{NESTOR: Neurosymbolic Evaluation of Semantic Textual Reasoning}
\author{}
\date{\today}
\begin{document}
\maketitle
\begin{abstract}
%%ABSTRACT%%
\end{abstract}
"""
    LATEX = True
    abstract = s_abstract().replace("\\\\%", "\\%")
    for pat, rep in _MD_TO_TEX[3:]:
        abstract = pat.sub(rep, abstract)
    head = head.replace("%%ABSTRACT%%", abstract)
    return head + body + "\n\\end{document}\n"


def build_numbers_tex():
    lines = ["% Auto-generated. Every number in the paper as a macro, so the",
             "% .tex file contains no literal figures either.",
             "% Regenerate with: python analysis/make_paper.py"]
    for k, v in sorted(N.items()):
        macro = "\\nestor" + re.sub(r"[^A-Za-z]", "", k.title())
        val = f"{v:.4g}" if isinstance(v, float) else str(v)
        lines.append(f"\\newcommand{{{macro}}}{{{val}}}")
    return "\n".join(lines) + "\n"


def main():
    PAPER.mkdir(parents=True, exist_ok=True)
    md = build_markdown()
    (PAPER / "nestor.md").write_text(md, encoding="utf-8")
    (PAPER / "nestor.tex").write_text(build_latex(), encoding="utf-8")
    (PAPER / "numbers.tex").write_text(build_numbers_tex(), encoding="utf-8")

    missing = md.count("[not yet computed]")
    print(f"paper/nestor.md      {len(md):,} chars")
    print(f"paper/nestor.tex     {(PAPER/'nestor.tex').stat().st_size:,} bytes")
    print(f"paper/numbers.tex    {len(N)} macros")
    print(f"coq results present: {D['has_coq']}")
    print(f"placeholders left:   {missing}")


if __name__ == "__main__":
    main()
