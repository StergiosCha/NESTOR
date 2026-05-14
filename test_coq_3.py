"""Quick test: 3 Coq examples (entailment, contradiction, unknown)."""
from dotenv import load_dotenv
load_dotenv()

import os
os.environ.setdefault("COQC_PATH", "coqc")
os.environ.setdefault("COQ_TIMEOUT", "60")
os.environ.setdefault("MAX_RETRIES", "3")

from phase2_coq.coq_pipeline import run_coq_pipeline
from clients.azure import get_client

client = get_client("gpt-4o")

tests = [
    ("Every Italian man wants to be a great tenor. Some Italian men are great tenors.",
     "There are Italian men who want to be a great tenor.",
     "entailment"),
    ("No really great tenors are modest.",
     "There are really great tenors who are modest.",
     "contradiction"),
    ("Few great tenors are poor.",
     "There are great tenors who are poor.",
     "unknown"),
]

for p, h, label in tests:
    print(f"\n=== {label.upper()} ===")
    print(f"P: {p}")
    print(f"H: {h}")
    r = run_coq_pipeline(client, "gpt-4o", p, h, label)
    print(f"Compiled: {r['compiled']}, Proved: {r['proof_complete']}, Attempts: {r['attempts']}")
    if r["errors"]:
        print(f"Errors: {r['errors']}")
    print(r["coq_code"][:400])
