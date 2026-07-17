# Review App — Quick Start

## Install

```bash
pip install streamlit pandas
```

## Run

```bash
cd NESTOR
streamlit run review_app.py
```

Opens in your browser at `http://localhost:8501`.

## Usage

1. **Pick your name**: on startup, the app shows a login screen — pick your name from the dropdown if you've reviewed before, or choose "+ Add new reviewer..." and type a new one. Each reviewer gets a separate save file, so you can't overwrite someone else's work. Existing names are read straight from the filenames already in `reviews/` (see "Syncing reviews via git" below), so anyone who's already committed a review file will show up automatically. You can switch reviewers at any time with the **Switch reviewer** button in the sidebar.
2. **Results folder**: defaults automatically to `phase1_nli_eval/results` next to the app — no need to navigate there yourself. Only override this in the sidebar if your data lives somewhere else.
3. **Choose a subfolder**: the results folder contains some loose `.json` files at the top level (ignored on purpose) alongside subfolders that hold the actual files to review. You must explicitly pick one of those subfolders from the sidebar dropdown before any files appear. If that subfolder itself has nested folders, tick "Include files from nested subfolders" to see everything inside it.
4. **Choose a file** from the dropdown, then **score each sample** on 3 criteria:
   - **Phenomenon identification** (0/1/2): Examine the relationship between explanation and phenomenon tag (e.g. GENERALIZED QUANTIFIERS:Conservativity). Does the explanation identify the right phenomenon?
   - **Soundness** (0/1/2): Is the reasoning logically valid?
   - **Consistency** (0/1): Does the explanation support the predicted label?
5. **Save** after each sample. A duplicate **Next / Previous** button pair also sits right below the Save button, so you can save and move on without scrolling back to the top.

### Review tab vs. Library tab

The app has two tabs, switchable at any time without losing your place:

- **📝 Review** — the single-sample, blind-scoring workflow described above. Other reviewers' and the judge's scores for the current sample are hidden by default (in a collapsed expander) so they don't bias your own read.
- **📚 Library** — a browsing and analysis view. Nothing is hidden here: pick any sample and see every reviewer's and the LLM judge's scores and comments side by side. It has its own filter panel (mirroring the sidebar filters, plus extras like minimum reviewer count, "only samples where reviewers disagree", and a reviewer-comment search box), a statistics panel (score distributions, per-reviewer averages, completion counts), and a sortable sample browser table. Use this tab for analysis, not for your own blind grading pass.

### README, on demand

This file is also available inside the app itself — expand **"📖 README / instructions"** at the top of the sidebar any time you need to reference it, including before you've picked a reviewer name.

## Syncing reviews via git

Your reviews are saved locally in `reviews/<filename>.<your_name>.reviews.json`. To share with the team:

```bash
git add reviews/
git commit -m "Add reviews"
git push
```

To see other reviewers' scores, pull first:

```bash
git pull
```

Their scores appear in the "other reviewer scores" expander per sample, and in the agreement (Cohen's kappa) sidebar section.

## Alternative: without the app

If you can't run Streamlit, you can review manually. Create your reviews file at `reviews/<dataset_file>.<your_name>.reviews.json` with this format:

```json
{
  "fracas_001": {
    "reviewer": "YourName",
    "reviewed_at": "2026-07-02T12:00:00",
    "phenomenon_id": 2,
    "phenomenon_id_notes": "",
    "soundness": 1,
    "soundness_notes": "minor error in quantifier scope",
    "consistency": 1,
    "consistency_notes": "",
    "general_notes": ""
  },
  "fracas_002": {
    ...
  }
}
```

The key is the sample `id` from the dataset JSON. Scores: phenomenon_id (0/1/2), soundness (0/1/2), consistency (0/1). Commit and push your file the same way. Note: the app's login screen discovers existing reviewer names from the **filename** (the `<your_name>` part of `reviews/<dataset_file>.<your_name>.reviews.json`), not from the `"reviewer"` field inside the JSON — so make sure that part of the filename is the name you want to show up in the dropdown.

## Inter-annotator agreement

In the sidebar under "Agreement between two reviewers", pick two reviewers to compare. The app computes Cohen's kappa per criterion. Per the eval plan, kappa >= 0.7 means judge scores stand; below that, fall back to full human annotation.
