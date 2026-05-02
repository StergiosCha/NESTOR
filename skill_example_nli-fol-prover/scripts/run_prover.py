"""
Theorem prover wrappers for Prover9, Mace4, and E Prover.
"""

import subprocess, tempfile, os, re
from pathlib import Path


def run_prover9(assumptions_fol: list[str], goal_fol: str, timeout: int = 10) -> dict:
    """
    Run Prover9 to try to prove goal from assumptions.
    Returns: {status: 'proved'|'failed'|'timeout', proof: str, time: float}
    """
    input_text = "formulas(assumptions).\n"
    for a in assumptions_fol:
        input_text += f"  {a}.\n"
    input_text += "end_of_list.\n\n"
    input_text += "formulas(goals).\n"
    input_text += f"  {goal_fol}.\n"
    input_text += "end_of_list.\n"

    with tempfile.NamedTemporaryFile(mode='w', suffix='.in', delete=False) as f:
        f.write(input_text)
        infile = f.name

    try:
        result = subprocess.run(
            ['prover9', '-f', infile],
            capture_output=True, text=True, timeout=timeout
        )
        output = result.stdout + result.stderr

        if 'THEOREM PROVED' in output:
            # Extract proof
            proof_start = output.find('============================== PROOF')
            proof_end = output.find('============================== end of proof')
            proof = output[proof_start:proof_end] if proof_start >= 0 else ""
            # Extract time
            time_match = re.search(r'User_CPU=(\d+\.\d+)', output)
            cpu_time = float(time_match.group(1)) if time_match else 0.0
            return {'status': 'proved', 'proof': proof, 'time': cpu_time, 'input': input_text}
        else:
            return {'status': 'failed', 'proof': '', 'time': 0.0, 'input': input_text, 'output': output[-500:]}

    except subprocess.TimeoutExpired:
        return {'status': 'timeout', 'proof': '', 'time': timeout, 'input': input_text}
    finally:
        os.unlink(infile)


def run_mace4(assumptions_fol: list[str], goal_fol: str, timeout: int = 10, domain_size: int = 10) -> dict:
    """
    Run Mace4 to find a countermodel (model where assumptions hold but goal doesn't).
    If Mace4 finds a model, the goal does NOT follow from assumptions.
    Returns: {status: 'model_found'|'failed'|'timeout', model: str}
    """
    input_text = f"assign(domain_size, {domain_size}).\n\n"
    input_text += "formulas(assumptions).\n"
    for a in assumptions_fol:
        input_text += f"  {a}.\n"
    input_text += "end_of_list.\n\n"
    input_text += "formulas(goals).\n"
    input_text += f"  {goal_fol}.\n"
    input_text += "end_of_list.\n"

    with tempfile.NamedTemporaryFile(mode='w', suffix='.in', delete=False) as f:
        f.write(input_text)
        infile = f.name

    try:
        result = subprocess.run(
            ['mace4', '-f', infile],
            capture_output=True, text=True, timeout=timeout
        )
        output = result.stdout + result.stderr

        if 'end of model' in output:
            model_start = output.find('============================== MODEL')
            model_end = output.find('============================== end of model')
            model = output[model_start:model_end+45] if model_start >= 0 else ""
            return {'status': 'model_found', 'model': model, 'input': input_text}
        else:
            return {'status': 'failed', 'model': '', 'input': input_text}

    except subprocess.TimeoutExpired:
        return {'status': 'timeout', 'model': '', 'input': input_text}
    finally:
        os.unlink(infile)


def run_eprover(assumptions_fol: list[str], goal_fol: str, timeout: int = 10) -> dict:
    """
    Run E Prover using TPTP format.
    Returns: {status: 'proved'|'failed'|'timeout', szs: str}
    """
    tptp = ""
    for i, a in enumerate(assumptions_fol):
        tptp_a = prover9_to_tptp(a)
        tptp += f"fof(ax{i+1}, axiom, {tptp_a}).\n"

    tptp_goal = prover9_to_tptp(goal_fol)
    tptp += f"fof(goal, conjecture, {tptp_goal}).\n"

    with tempfile.NamedTemporaryFile(mode='w', suffix='.p', delete=False) as f:
        f.write(tptp)
        infile = f.name

    try:
        result = subprocess.run(
            ['eprover', '--auto', '--tptp3-format', '-s', infile],
            capture_output=True, text=True, timeout=timeout
        )
        output = result.stdout + result.stderr

        if 'SZS status Theorem' in output:
            return {'status': 'proved', 'szs': 'Theorem', 'tptp': tptp}
        elif 'SZS status CounterSatisfiable' in output:
            return {'status': 'refuted', 'szs': 'CounterSatisfiable', 'tptp': tptp}
        else:
            szs_match = re.search(r'SZS status (\w+)', output)
            szs = szs_match.group(1) if szs_match else 'Unknown'
            return {'status': 'failed', 'szs': szs, 'tptp': tptp, 'output': output[-300:]}

    except subprocess.TimeoutExpired:
        return {'status': 'timeout', 'szs': 'Timeout', 'tptp': tptp}
    finally:
        os.unlink(infile)


def prover9_to_tptp(formula: str) -> str:
    """
    Convert Prover9 formula syntax to TPTP FOF syntax.
    Prover9: all x (P(x) -> Q(x))  →  TPTP: ![X]: (p(X) => q(X))
    """
    s = formula.strip().rstrip('.')

    # Quantifiers
    s = re.sub(r'\ball\s+(\w+)', r'!\[\1\]:', s)
    s = re.sub(r'\bexists\s+(\w+)', r'?\[\1\]:', s)

    # Connectives
    s = s.replace('->', '=>')
    s = s.replace('<->', '<=>')
    s = s.replace(' - ', ' ~')
    s = re.sub(r'^-', '~', s)
    s = re.sub(r'\(-', '(~', s)

    # Variables to uppercase in quantifiers
    # This is approximate — works for simple cases
    for var in re.findall(r'[!?]\[(\w+)\]', s):
        s = re.sub(rf'\b{var}\b', var.upper(), s)

    return s


def prove_entailment(premises_fol: list[str], hypothesis_fol: str,
                     timeout: int = 10) -> dict:
    """
    Full entailment check: try Prover9 (proof), Mace4 (countermodel), E (backup).

    Returns:
        verdict: 'entailment' | 'contradiction' | 'neutral' | 'unknown'
        details: dict with all prover results
    """
    results = {}

    # 1. Try to prove P ⊢ H
    results['prover9'] = run_prover9(premises_fol, hypothesis_fol, timeout)

    if results['prover9']['status'] == 'proved':
        return {
            'verdict': 'entailment',
            'reason': 'Prover9 proved H from P',
            'results': results
        }

    # 2. Try to find countermodel (P true, H false)
    results['mace4'] = run_mace4(premises_fol, hypothesis_fol, timeout)

    # 3. Try to prove P ⊢ ¬H (contradiction check)
    neg_h = f"-({hypothesis_fol})"
    results['prover9_neg'] = run_prover9(premises_fol, neg_h, timeout)

    if results['prover9_neg']['status'] == 'proved':
        return {
            'verdict': 'contradiction',
            'reason': 'Prover9 proved ¬H from P',
            'results': results
        }

    # 4. E Prover as backup
    results['eprover'] = run_eprover(premises_fol, hypothesis_fol, timeout)

    if results['eprover']['status'] == 'proved':
        return {
            'verdict': 'entailment',
            'reason': 'E Prover proved H from P',
            'results': results
        }

    # 5. Determine verdict
    if results['mace4']['status'] == 'model_found':
        return {
            'verdict': 'neutral',
            'reason': 'Mace4 found countermodel (P true, H false possible)',
            'results': results
        }

    return {
        'verdict': 'unknown',
        'reason': 'No proof, no countermodel, no contradiction within timeout',
        'results': results
    }
