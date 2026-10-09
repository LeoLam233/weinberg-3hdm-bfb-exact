#!/usr/bin/env python3
"""Portable, serial CI adapter for the pinned W3 validation helpers.

It reuses official external dependency caches, freshly compiles all local W3
sources, then explicitly replays LeanChecker using the same Lean kernel.
"""
from pathlib import Path
import argparse
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean'
RECEIPTS = ROOT / 'ci-receipts'


def run(*args, cwd=LEAN):
    env = os.environ.copy()
    # Source archives have no Git database. Never let an enclosing checkout's
    # remote/HEAD masquerade as the identity of a vendored dependency.
    env['GIT_CEILING_DIRECTORIES'] = str((LEAN / '.lake/packages').resolve())
    subprocess.run([sys.executable, *map(str, args)], cwd=cwd, env=env, check=True)


def plan():
    out = subprocess.run(
        [sys.executable, 'scripts/portable_fresh_build.py', '--entry',
         'W3.FiniteInputMain', '--all-local', '--label', 'ci', '--dry-run'],
        cwd=LEAN, check=True, capture_output=True, text=True,
    )
    result = json.loads(out.stdout)
    (RECEIPTS / 'import-plan.json').write_text(out.stdout)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('stage', choices=['plan', 'cache', 'build', 'audit'])
    args = parser.parse_args()
    RECEIPTS.mkdir(exist_ok=True)
    if args.stage == 'plan':
        result = plan()
        print(json.dumps({'local_modules': len(result['order']),
                          'external_imports': result['external_imports']}, indent=2))
    elif args.stage == 'cache':
        run('scripts/bootstrap_cache.py')
        imports = [m for m in plan()['external_imports'] if m.startswith('Mathlib.')]
        if not imports:
            raise RuntimeError('No Mathlib imports found; refusing an empty cache target')
        run('scripts/run_portable.py', '--cwd', '.lake/packages/mathlib',
            '--label', 'official_cache', '--', '--run', 'Cache/Main.lean',
            '--repo=leanprover-community/mathlib4', '--cache-from=master', 'get', *imports)
    elif args.stage == 'build':
        before = set((LEAN / 'fresh').glob('*/BUILD.json'))
        run('scripts/portable_fresh_build.py', '--entry', 'W3.FiniteInputMain',
            '--all-local', '--label', 'github_ci')
        created = set((LEAN / 'fresh').glob('*/BUILD.json')) - before
        if len(created) != 1:
            raise RuntimeError('Expected exactly one new complete build report')
        report = created.pop()
        data = json.loads(report.read_text())
        if data.get('complete') is not True:
            raise RuntimeError('Fresh local build did not complete')
        (RECEIPTS / 'build-report-path.txt').write_text(str(report.relative_to(ROOT)) + '\n')
    else:
        report = ROOT / (RECEIPTS / 'build-report-path.txt').read_text().strip()
        if not report.is_file():
            raise RuntimeError('Exact successful build receipt is missing')
        run('scripts/portable_kernel_audit.py', '--build-report', report)
        reports = sorted(report.parent.glob('kernel_audit_*/AUDIT.json'))
        if not reports:
            raise RuntimeError('Kernel audit receipt is missing')
        result = json.loads(reports[-1].read_text())
        if result.get('status') != 'PASS' or result.get('fresh_checker_status') != 'PASS':
            raise RuntimeError('Strict kernel audit failed')
        print(json.dumps({'status': 'PASS', 'audit_report': str(reports[-1].relative_to(ROOT))}))


if __name__ == '__main__':
    main()
