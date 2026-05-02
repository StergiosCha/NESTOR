#!/usr/bin/env python3
"""
NLI→FOL Multi-LLM Experiment
Compare LLMs on translating NL to FOL and proving entailment.

Usage:
  python3 experiment.py --config experiment_config.json
  python3 experiment.py --models gpt-4o,claude-sonnet,mistral-large --file examples/basic.jsonl

Supports: Azure OpenAI, OpenAI, Anthropic, any OpenAI-compatible endpoint (Ollama, vLLM, Together, etc.)
"""

import json, os, sys, time, re, urllib.request, ssl
from pathlib import Path
from datetime import datetime
from concurrent.futures import ThreadPoolExecutor

sys.path.insert(0, str(Path(__file__).parent))
from run_prover import prove_entailment

# ═══════════════════════════════════════════
# FOL Translation Prompt (shared across LLMs)
# ═══════════════════════════════════════════

FOL_SYSTEM = """You are a formal semanticist. Translate the given premise and hypothesis
into first-order logic in Prover9 syntax.

Prover9 syntax:
- Universal: all x (P(x) -> Q(x))
- Existential: exists x (P(x) & Q(x))
- Connectives: -> & | - <->
- Equality: = !=
- Variables: x, y, z (lowercase)
- Constants: lowercase (john, socrates)
- Predicates: lowercase (cat, run, read)
- NO period at end of formulas

Conventions:
- "All/Every A are B" → all x (A(x) -> B(x))
- "Some A are B" → exists x (A(x) & B(x))
- "No A is B" → all x (A(x) -> -B(x))
- "A is B" (name) → B(a)
- Bare plurals/generics → universal
- Add exists x P(x) presupposition when NL clearly presupposes existence
- Transitive verbs: read(x,y)

Return ONLY valid JSON (no markdown fences):
{
  "premises": ["formula1", "formula2"],
  "hypothesis": "formula",
  "notes": "brief note on any ambiguity"
}"""


# ═══════════════════════════════════════════
# LLM Provider Abstraction
# ═══════════════════════════════════════════

class LLMProvider:
    """Base class for LLM API calls."""

    def __init__(self, name: str, model: str, api_key: str = None,
                 endpoint: str = None, api_version: str = None):
        self.name = name
        self.model = model
        self.api_key = api_key
        self.endpoint = endpoint
        self.api_version = api_version

    def translate(self, premise: str, hypothesis: str) -> dict:
        raise NotImplementedError

    def _parse_response(self, text: str) -> dict:
        """Parse JSON from LLM response, handling markdown fences."""
        text = text.strip()
        text = re.sub(r'^```(?:json)?\s*', '', text)
        text = re.sub(r'\s*```$', '', text)
        return json.loads(text)

    def _make_request(self, url: str, headers: dict, body: dict,
                      timeout: int = 30) -> str:
        """Make HTTP request and return response text."""
        data = json.dumps(body).encode()
        ctx = ssl.create_default_context()
        req = urllib.request.Request(url, data=data, headers=headers)
        resp = urllib.request.urlopen(req, timeout=timeout, context=ctx)
        return json.loads(resp.read().decode())


class AnthropicProvider(LLMProvider):
    """Claude via Anthropic API."""

    def translate(self, premise: str, hypothesis: str) -> dict:
        url = self.endpoint or "https://api.anthropic.com/v1/messages"
        headers = {
            "Content-Type": "application/json",
            "x-api-key": self.api_key,
            "anthropic-version": "2023-06-01"
        }
        body = {
            "model": self.model,
            "max_tokens": 1024,
            "system": FOL_SYSTEM,
            "messages": [{"role": "user", "content":
                f"Premise: {premise}\nHypothesis: {hypothesis}\n\nTranslate to FOL."}]
        }
        resp = self._make_request(url, headers, body)
        text = resp['content'][0]['text']
        return self._parse_response(text)


class OpenAIProvider(LLMProvider):
    """GPT via OpenAI API."""

    def translate(self, premise: str, hypothesis: str) -> dict:
        url = self.endpoint or "https://api.openai.com/v1/chat/completions"
        headers = {
            "Content-Type": "application/json",
            "Authorization": f"Bearer {self.api_key}"
        }
        body = {
            "model": self.model,
            "max_tokens": 1024,
            "messages": [
                {"role": "system", "content": FOL_SYSTEM},
                {"role": "user", "content":
                    f"Premise: {premise}\nHypothesis: {hypothesis}\n\nTranslate to FOL."}
            ]
        }
        resp = self._make_request(url, headers, body)
        text = resp['choices'][0]['message']['content']
        return self._parse_response(text)


class AzureOpenAIProvider(LLMProvider):
    """GPT via Azure OpenAI."""

    def translate(self, premise: str, hypothesis: str) -> dict:
        # Azure URL: {endpoint}/openai/deployments/{model}/chat/completions?api-version=...
        url = (f"{self.endpoint}/openai/deployments/{self.model}"
               f"/chat/completions?api-version={self.api_version or '2024-06-01'}")
        headers = {
            "Content-Type": "application/json",
            "api-key": self.api_key
        }
        body = {
            "max_tokens": 1024,
            "messages": [
                {"role": "system", "content": FOL_SYSTEM},
                {"role": "user", "content":
                    f"Premise: {premise}\nHypothesis: {hypothesis}\n\nTranslate to FOL."}
            ]
        }
        resp = self._make_request(url, headers, body)
        text = resp['choices'][0]['message']['content']
        return self._parse_response(text)


class OpenAICompatibleProvider(LLMProvider):
    """Any OpenAI-compatible API (Ollama, vLLM, Together, Fireworks, Groq, etc.)."""

    def translate(self, premise: str, hypothesis: str) -> dict:
        url = f"{self.endpoint}/v1/chat/completions"
        headers = {"Content-Type": "application/json"}
        if self.api_key:
            headers["Authorization"] = f"Bearer {self.api_key}"
        body = {
            "model": self.model,
            "max_tokens": 1024,
            "messages": [
                {"role": "system", "content": FOL_SYSTEM},
                {"role": "user", "content":
                    f"Premise: {premise}\nHypothesis: {hypothesis}\n\nTranslate to FOL."}
            ]
        }
        resp = self._make_request(url, headers, body)
        text = resp['choices'][0]['message']['content']
        return self._parse_response(text)


def make_provider(config: dict) -> LLMProvider:
    """Factory: create provider from config dict."""
    provider_type = config.get('provider', 'openai')
    cls = {
        'anthropic': AnthropicProvider,
        'openai': OpenAIProvider,
        'azure': AzureOpenAIProvider,
        'compatible': OpenAICompatibleProvider,
        'ollama': OpenAICompatibleProvider,
        'vllm': OpenAICompatibleProvider,
        'together': OpenAICompatibleProvider,
        'groq': OpenAICompatibleProvider,
        'fireworks': OpenAICompatibleProvider,
    }.get(provider_type, OpenAICompatibleProvider)

    return cls(
        name=config.get('name', config.get('model', 'unknown')),
        model=config['model'],
        api_key=config.get('api_key', os.environ.get(config.get('api_key_env', ''), '')),
        endpoint=config.get('endpoint'),
        api_version=config.get('api_version'),
    )


# ═══════════════════════════════════════════
# Experiment Runner
# ═══════════════════════════════════════════

def run_experiment(providers: list[LLMProvider], pairs: list[dict],
                   timeout: int = 10, output_file: str = None) -> dict:
    """
    Run all pairs through all LLMs, prove each, compute accuracy.
    """
    results = {}

    for provider in providers:
        name = provider.name
        results[name] = {
            'model': provider.model,
            'pairs': [],
            'correct': 0,
            'total': 0,
            'errors': 0,
            'entailment_correct': 0, 'entailment_total': 0,
            'contradiction_correct': 0, 'contradiction_total': 0,
            'neutral_correct': 0, 'neutral_total': 0,
            'avg_time': 0,
        }

        print(f"\n{'═'*60}")
        print(f"  MODEL: {name} ({provider.model})")
        print(f"{'═'*60}")

        times = []
        for i, pair in enumerate(pairs):
            p, h = pair['premise'], pair['hypothesis']
            gold = pair.get('label', '')

            print(f"\n  [{i+1}/{len(pairs)}] P: {p}")
            print(f"           H: {h}")
            print(f"           Gold: {gold}")

            t0 = time.time()
            try:
                # Translate
                fol = provider.translate(p, h)
                print(f"           FOL P: {fol['premises']}")
                print(f"           FOL H: {fol['hypothesis']}")

                # Prove
                proof = prove_entailment(fol['premises'], fol['hypothesis'], timeout=timeout)
                verdict = proof['verdict']
                elapsed = time.time() - t0
                times.append(elapsed)

                correct = (verdict == gold) if gold else None
                icon = '✓' if correct else ('✗' if correct is False else '?')
                print(f"           → {icon} {verdict} ({elapsed:.1f}s)")

                results[name]['pairs'].append({
                    'premise': p, 'hypothesis': h, 'gold': gold,
                    'verdict': verdict, 'correct': correct,
                    'fol_premises': fol['premises'],
                    'fol_hypothesis': fol['hypothesis'],
                    'notes': fol.get('notes', ''),
                    'time': elapsed,
                })

                if gold:
                    results[name]['total'] += 1
                    results[name][f'{gold}_total'] += 1
                    if correct:
                        results[name]['correct'] += 1
                        results[name][f'{gold}_correct'] += 1

            except Exception as e:
                elapsed = time.time() - t0
                print(f"           → ⚠ ERROR: {e} ({elapsed:.1f}s)")
                results[name]['errors'] += 1
                results[name]['pairs'].append({
                    'premise': p, 'hypothesis': h, 'gold': gold,
                    'verdict': 'error', 'error': str(e), 'time': elapsed,
                })
                if gold:
                    results[name]['total'] += 1
                    results[name][f'{gold}_total'] += 1

        results[name]['avg_time'] = sum(times) / len(times) if times else 0

    # ═══ Summary Table ═══
    print(f"\n\n{'═'*75}")
    print(f"  RESULTS SUMMARY")
    print(f"{'═'*75}")
    print(f"  {'Model':<25s} {'Acc':>6s} {'Ent':>8s} {'Con':>8s} {'Neu':>8s} {'Err':>5s} {'Time':>6s}")
    print(f"  {'─'*25} {'─'*6} {'─'*8} {'─'*8} {'─'*8} {'─'*5} {'─'*6}")

    for name, r in results.items():
        acc = f"{r['correct']}/{r['total']}" if r['total'] else "N/A"
        ent = f"{r['entailment_correct']}/{r['entailment_total']}" if r['entailment_total'] else "-"
        con = f"{r['contradiction_correct']}/{r['contradiction_total']}" if r['contradiction_total'] else "-"
        neu = f"{r['neutral_correct']}/{r['neutral_total']}" if r['neutral_total'] else "-"
        print(f"  {name:<25s} {acc:>6s} {ent:>8s} {con:>8s} {neu:>8s} {r['errors']:>5d} {r['avg_time']:>5.1f}s")

    print(f"{'═'*75}")

    # Save results
    if output_file:
        with open(output_file, 'w') as f:
            json.dump(results, f, indent=2, default=str)
        print(f"\n  Results saved: {output_file}")

    return results


# ═══════════════════════════════════════════
# Main
# ═══════════════════════════════════════════

def main():
    import argparse
    parser = argparse.ArgumentParser(description="NLI→FOL Multi-LLM Experiment", add_help=False)
    parser.add_argument('--help', action='help')
    parser.add_argument('--config', type=str, help='JSON config file with model definitions')
    parser.add_argument('--file', type=str, default='examples/basic.jsonl', help='JSONL test pairs')
    parser.add_argument('--timeout', type=int, default=10)
    parser.add_argument('--output', type=str, default=None, help='Output JSON file')
    args = parser.parse_args()

    # Load test pairs
    with open(args.file) as f:
        pairs = [json.loads(line) for line in f if line.strip()]
    print(f"Loaded {len(pairs)} test pairs from {args.file}")

    # Load model configs
    if args.config:
        with open(args.config) as f:
            config = json.load(f)
        providers = [make_provider(m) for m in config['models']]
    else:
        # Default: use whatever API keys are in environment
        providers = []
        if os.environ.get('ANTHROPIC_API_KEY'):
            providers.append(make_provider({
                'name': 'claude-sonnet', 'model': 'claude-sonnet-4-20250514',
                'provider': 'anthropic', 'api_key_env': 'ANTHROPIC_API_KEY'
            }))
        if os.environ.get('OPENAI_API_KEY'):
            providers.append(make_provider({
                'name': 'gpt-4o', 'model': 'gpt-4o',
                'provider': 'openai', 'api_key_env': 'OPENAI_API_KEY'
            }))
        if not providers:
            print("No API keys found. Set ANTHROPIC_API_KEY or OPENAI_API_KEY,")
            print("or use --config with a config file. Example config:")
            print(json.dumps(EXAMPLE_CONFIG, indent=2))
            sys.exit(1)

    output = args.output or f"results_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
    run_experiment(providers, pairs, timeout=args.timeout, output_file=output)


EXAMPLE_CONFIG = {
    "models": [
        {
            "name": "claude-sonnet",
            "provider": "anthropic",
            "model": "claude-sonnet-4-20250514",
            "api_key_env": "ANTHROPIC_API_KEY"
        },
        {
            "name": "gpt-4o",
            "provider": "openai",
            "model": "gpt-4o",
            "api_key_env": "OPENAI_API_KEY"
        },
        {
            "name": "gpt-4o-azure",
            "provider": "azure",
            "model": "gpt-4o",
            "endpoint": "https://YOUR_RESOURCE.openai.azure.com",
            "api_key_env": "AZURE_OPENAI_KEY",
            "api_version": "2024-06-01"
        },
        {
            "name": "llama-3.1-70b-together",
            "provider": "together",
            "model": "meta-llama/Meta-Llama-3.1-70B-Instruct-Turbo",
            "endpoint": "https://api.together.xyz",
            "api_key_env": "TOGETHER_API_KEY"
        },
        {
            "name": "mistral-large",
            "provider": "compatible",
            "model": "mistral-large-latest",
            "endpoint": "https://api.mistral.ai",
            "api_key_env": "MISTRAL_API_KEY"
        },
        {
            "name": "gemma-2-local",
            "provider": "ollama",
            "model": "gemma2:27b",
            "endpoint": "http://localhost:11434"
        },
        {
            "name": "qwen-2.5-72b-groq",
            "provider": "groq",
            "model": "qwen-2.5-72b",
            "endpoint": "https://api.groq.com/openai",
            "api_key_env": "GROQ_API_KEY"
        },
        {
            "name": "deepseek-v3",
            "provider": "compatible",
            "model": "deepseek-chat",
            "endpoint": "https://api.deepseek.com",
            "api_key_env": "DEEPSEEK_API_KEY"
        }
    ]
}


if __name__ == "__main__":
    main()
