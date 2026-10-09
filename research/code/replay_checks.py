"""Replay the named verification scope in a fresh, isolated tree.

This checks reproducibility of finite symbolic/numerical evidence. It is not an
end-to-end exact implementation or formal verification of THEOREM.md.
"""
from __future__ import annotations
import argparse
import hashlib
import importlib.metadata
import json
import math
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tempfile
import time
from typing import Any

EXACT = [
    'exact_checks', 'closure_audit_checks', 'face_and_infinitesimal_checks',
    'hexagon_spectrum_probe', 'final_destructive_checks',
    'field_and_genericity_checks',
]
NUMERICAL = ['hexagon_numeric', 'affine_shift_checks']
ROOT = Path(__file__).resolve().parents[1]

def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def compare(a: Any, b: Any, *, floating: bool, location: str = '') -> None:
    if isinstance(a, dict):
        assert isinstance(b, dict) and a.keys() == b.keys(), location
        for key in a:
            compare(a[key], b[key], floating=floating, location=f'{location}/{key}')
    elif isinstance(a, list):
        assert isinstance(b, list) and len(a) == len(b), location
        for index, (x, y) in enumerate(zip(a, b)):
            compare(x, y, floating=floating, location=f'{location}/{index}')
    elif floating and isinstance(a, (int, float)) and not isinstance(a, bool):
        assert isinstance(b, (int, float)), location
        assert math.isclose(a, b, rel_tol=1e-9, abs_tol=1e-10), (location, a, b)
    else:
        assert a == b, (location, a, b)

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT / 'results/replay_verification.json')
    parser.add_argument('--timeout', type=int, default=120, help='Seconds per script')
    args = parser.parse_args()
    logs = ROOT / 'verification_logs'
    logs.mkdir(exist_ok=True)
    inputs = [p for p in (ROOT / 'code').glob('*.py')]
    inputs += [ROOT / 'results/duality_probe.json']
    inputs += [ROOT / 'results' / f'{name}.json' for name in EXACT + NUMERICAL]
    record: dict[str, Any] = {
        'scope': 'Six exact symbolic suites and two floating suites; original field-minimum records are captured inputs, not independently re-certified global optima.',
        'python': sys.version,
        'platform': platform.platform(),
        'versions': {k: importlib.metadata.version(k) for k in ('numpy', 'scipy', 'sympy')},
        'thread_environment': {'OPENBLAS_NUM_THREADS': '1', 'OMP_NUM_THREADS': '1'},
        'input_sha256': {str(p.relative_to(ROOT)): digest(p) for p in sorted(inputs)},
        'checks': [],
        'limitations': [
            'No full exact ordered-field stability solver was executed.',
            'No proof assistant or external reviewer was used.',
            'Floating comparison tolerance is rel=1e-9, abs=1e-10; it is not an error bound on a global minimum.',
            'The abandoned unsaved 60-case moment batch is outside this replay scope.',
        ],
    }
    with tempfile.TemporaryDirectory(prefix='w3_evidence_replay_') as tmp:
        work = Path(tmp)
        shutil.copytree(ROOT / 'code', work / 'code', ignore=shutil.ignore_patterns('__pycache__'))
        shutil.copytree(ROOT / 'results', work / 'results')
        for relative, expected_hash in record['input_sha256'].items():
            assert digest(work / relative) == expected_hash, relative
        env = os.environ.copy()
        env.update(record['thread_environment'])
        for name in EXACT + NUMERICAL:
            started = time.monotonic()
            run = subprocess.run(
                [sys.executable, str(work / 'code' / f'{name}.py')],
                cwd=work, env=env, text=True, capture_output=True,
                timeout=args.timeout, check=False,
            )
            (logs / f'{name}.log').write_text(run.stdout + '\nSTDERR:\n' + run.stderr)
            if run.returncode:
                raise RuntimeError(f'{name} failed ({run.returncode}); see verification_logs')
            expected = json.loads((ROOT / 'results' / f'{name}.json').read_text())
            actual_file = work / 'results' / f'{name}.json'
            actual = json.loads(actual_file.read_text())
            compare(expected, actual, floating=name in NUMERICAL)
            record['checks'].append({
                'script': name + '.py', 'status': 'PASS',
                'comparison': 'JSON exact equality' if name in EXACT else 'Recursive numeric tolerance and exact nonnumeric comparison',
                'elapsed_seconds': round(time.monotonic() - started, 3),
                'replayed_output_sha256': digest(actual_file),
            })
            print(name + ': PASS', flush=True)
    record['status'] = 'REPLAY-TESTED at the stated scope'
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2))
    print(str(args.output))

if __name__ == '__main__':
    main()
