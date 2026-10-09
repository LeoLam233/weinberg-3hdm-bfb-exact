#!/usr/bin/env python3
"""Check the published source identities before execution."""
from pathlib import Path, PurePosixPath
import hashlib

ROOT = Path(__file__).resolve().parents[1]
lines = (ROOT / 'MANIFEST.sha256').read_text().splitlines()
if not lines:
    raise SystemExit('Empty source manifest')
seen = set()
for line in lines:
    digest, name = line.split('  ', 1)
    rel = PurePosixPath(name)
    if rel.is_absolute() or '..' in rel.parts or name in seen:
        raise SystemExit(f'Unsafe or duplicate manifest entry: {name}')
    seen.add(name)
    path = ROOT / name
    if path.is_symlink() or not path.is_file():
        raise SystemExit(f'Missing or non-regular source: {name}')
    if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
        raise SystemExit(f'Source digest mismatch: {name}')
print(f'PASS: {len(seen)} published files match MANIFEST.sha256')

# An extra tracked source must not silently enter the formal build outside the
# publication inventory. Generated CI/runtime files remain untracked.
if (ROOT / '.git').exists():
    import subprocess
    tracked = set(subprocess.check_output(['git', 'ls-files', '-z'], cwd=ROOT).decode().split('\0')) - {''}
    expected = seen | {'MANIFEST.sha256'}
    if tracked != expected:
        raise SystemExit(f'Tracked inventory mismatch: extra={sorted(tracked - expected)}, missing={sorted(expected - tracked)}')
