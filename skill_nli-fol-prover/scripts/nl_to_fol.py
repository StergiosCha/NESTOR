"""
Natural Language to First-Order Logic translation.
Uses an LLM (Claude) or rule-based fallback to translate NL to Prover9 FOL syntax.
"""

import re, json

# System prompt for FOL translation
FOL_SYSTEM_PROMPT = """You are a formal semanticist translating natural language sentences
into first-order logic formulas in Prover9 syntax.

## Prover9 Syntax Rules:
- Universal: all x (P(x) -> Q(x))
- Existential: exists x (P(x) & Q(x))
- Implication: ->
- Conjunction: &
- Disjunction: |
- Negation: -
- Biconditional: <->
- Equality: =
- Variables: x, y, z, u, v, w (lowercase)
- Constants: lowercase (john, mary, socrates)
- Predicates: lowercase (cat, run, read)
- Each formula ends WITHOUT a period (the caller adds it)

## Translation Conventions:
1. "All/Every A are/is B" → all x (A(x) -> B(x))
2. "Some/A few A are B" → exists x (A(x) & B(x))
3. "No A is B" → all x (A(x) -> -B(x))
4. "A is B" (proper name) → B(a)  [a = constant]
5. "Most A are B" → cannot express in FOL, approximate as: exists x (A(x) & B(x))
6. Bare plurals / generics: treat as universal: all x (A(x) -> B(x))
7. Definite "the A" → exists x (A(x) & all y (A(y) -> y = x) & ...)
8. Transitive verbs: use 2-place predicates: read(x, y)
9. Adjectives: use 1-place predicates: tall(x), red(x)
10. Relative clauses: conjoin: all x ((man(x) & run(x)) -> ...)
11. "If A then B" → premise: (translation of A), with B as separate formula
12. Negation: "does not", "isn't" → use -

## Output Format:
Return ONLY a JSON object with this exact structure:
{
  "premises": ["formula1", "formula2"],
  "hypothesis": "formula",
  "predicates": {"predicate_name": "natural language meaning"},
  "constants": {"constant_name": "natural language referent"},
  "notes": "any issues or ambiguities in the translation"
}

Do NOT include periods at the end of formulas. Do NOT wrap in markdown."""


def translate_with_llm(premise: str, hypothesis: str, api_key: str = None) -> dict:
    """
    Use Claude API to translate P/H to FOL.
    Returns: {premises: [...], hypothesis: str, predicates: {...}, notes: str}
    """
    import urllib.request

    prompt = f"""Translate this premise-hypothesis pair into first-order logic (Prover9 syntax).

Premise: {premise}
Hypothesis: {hypothesis}

Return ONLY the JSON object, no markdown, no explanation."""

    body = json.dumps({
        "model": "claude-sonnet-4-20250514",
        "max_tokens": 1000,
        "system": FOL_SYSTEM_PROMPT,
        "messages": [{"role": "user", "content": prompt}]
    }).encode()

    headers = {
        "Content-Type": "application/json",
        "x-api-key": api_key or "",
        "anthropic-version": "2023-06-01"
    }

    req = urllib.request.Request(
        "https://api.anthropic.com/v1/messages",
        data=body, headers=headers
    )

    try:
        resp = urllib.request.urlopen(req)
        data = json.loads(resp.read().decode())
        text = data['content'][0]['text'].strip()
        # Strip markdown fences if present
        text = re.sub(r'^```json\s*', '', text)
        text = re.sub(r'\s*```$', '', text)
        return json.loads(text)
    except Exception as e:
        raise RuntimeError(f"LLM translation failed: {e}")


def translate_rule_based(premise: str, hypothesis: str) -> dict:
    """
    Simple rule-based NL→FOL for common patterns.
    Fallback when no API key is available.
    """
    def parse_sentence(s: str) -> str:
        s = s.strip().rstrip('.')
        sl = s.lower()

        # "All/Every X are/is Y"
        m = re.match(r'(?:all|every)\s+(\w+)s?\s+(?:are|is)\s+(\w+)s?', sl)
        if m:
            subj, pred = m.group(1), m.group(2)
            return f"all x ({subj}(x) -> {pred}(x))"

        # "Some X are/is Y"
        m = re.match(r'(?:some|a few)\s+(\w+)s?\s+(?:are|is)\s+(\w+)s?', sl)
        if m:
            subj, pred = m.group(1), m.group(2)
            return f"exists x ({subj}(x) & {pred}(x))"

        # "No X is/are Y"
        m = re.match(r'no\s+(\w+)s?\s+(?:is|are)\s+(\w+)s?', sl)
        if m:
            subj, pred = m.group(1), m.group(2)
            return f"all x ({subj}(x) -> -{pred}(x))"

        # "X is Y" / "X is a Y" (proper name)
        m = re.match(r'(\w+)\s+is\s+(?:a\s+)?(\w+)', sl)
        if m:
            name, pred = m.group(1), m.group(2)
            return f"{pred}({name})"

        # "X Vs" / "X does not V" (proper name + intransitive verb)
        m = re.match(r'(\w+)\s+(?:does not|doesn\'t)\s+(\w+)', sl)
        if m:
            name, verb = m.group(1), m.group(2)
            return f"-{verb}({name})"

        m = re.match(r'(\w+)\s+(\w+)s\b', sl)
        if m:
            name, verb = m.group(1), m.group(2)
            return f"{verb}({name})"

        # Fallback: return as-is (will fail in prover)
        return f"% UNPARSED: {s}"

    p_fol = parse_sentence(premise)
    h_fol = parse_sentence(hypothesis)

    return {
        'premises': [p_fol],
        'hypothesis': h_fol,
        'predicates': {},
        'constants': {},
        'notes': 'Rule-based translation (limited coverage)'
    }


def translate(premise: str, hypothesis: str, api_key: str = None, use_llm: bool = True) -> dict:
    """
    Translate NL pair to FOL. Uses LLM if api_key provided, else rule-based.
    """
    if use_llm and api_key:
        try:
            return translate_with_llm(premise, hypothesis, api_key)
        except Exception as e:
            print(f"  ⚠ LLM failed ({e}), falling back to rule-based")
            return translate_rule_based(premise, hypothesis)
    else:
        return translate_rule_based(premise, hypothesis)
