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

1. **Root folder**: Change it in the sidebar to point at the folder with your eval JSON files (e.g. `results/` or `phase1_eval/`).
2. **Your name**: Type your name/initials in the sidebar — this is required to save reviews. Each reviewer gets a separate file, so you can't overwrite someone else's work.
3. **Score each sample** on 3 criteria:
   - **Phenomenon identification** (0/1/2): Does the explanation identify the right phenomenon?
   - **Soundness** (0/1/2): Is the reasoning logically valid?
   - **Consistency** (0/1): Does the explanation support the predicted label?
4. **Save** after each sample.

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

The key is the sample `id` from the dataset JSON. Scores: phenomenon_id (0/1/2), soundness (0/1/2), consistency (0/1). Commit and push your file the same way.

## Inter-annotator agreement

In the sidebar under "Agreement between two reviewers", pick two reviewers to compare. The app computes Cohen's kappa per criterion. Per the eval plan, kappa >= 0.7 means judge scores stand; below that, fall back to full human annotation.
