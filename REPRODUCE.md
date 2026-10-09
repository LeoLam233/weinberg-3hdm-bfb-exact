# Reproduce the formal development

The formal source is in `lean/`. Its root module is `W3`, which imports the final
finite-input endpoint `W3.FiniteInputMain`. The exact-operation primitive boundary
and scientific scope are part of the result; see `README.md` and `docs/SCOPE.md`.

## Pins and resources

- Lean **4.34.1**, upstream commit `5045d0056413266e57c625dcd7c365b10e377c52`.
- Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- All transitive source commits: `lean/lake-manifest.json`.
- Official source archive SHA-256 hashes: `lean/recovery/dependency_source_receipt.json`.
- Official Linux x86-64 runtime URL and SHA-256: `lean/scripts/setup_dependencies.py`.
- CI uses Python 3.12.14; helpers require Python 3.12 or later. Use Linux x86-64
  and enough free disk for Lean plus the Mathlib
  cache. Each compiler invocation is serial, with `-j1 -M4096` and a shared lock.
  This Lean setting is not an operating-system memory limit.

The normal Lake entry point is `cd lean && lake build W3`, with the exact toolchain
and dependency manifest. The explicit, receipt-producing path below is used by
this repository's CI and rebuilds every local W3 module into a new output tree.
It reuses official compiled external dependencies; it does not claim that every
Mathlib dependency is freshly rebuilt from source.

## Fresh setup and complete check

From the repository root:

```sh
python3 scripts/verify_manifest.py
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements-ci.txt
(cd lean && ../.venv/bin/python scripts/setup_dependencies.py --install --runtime)
.venv/bin/python scripts/run_ci.py cache
.venv/bin/python scripts/run_ci.py build
.venv/bin/python scripts/run_ci.py audit
```

The setup helper only restores absent/empty dependency trees and refuses to
overwrite an existing nonempty installation. Every archive is SHA-256-checked
before extraction; the installed source files are checked against their archives.
The default setup-helper invocation without `--install` checks source-manifest
agreement only. That is not a successful installation or build.

`run_ci.py cache` builds the pinned upstream Cache tool, derives external imports
from every local source, and explicitly requests the official upstream master
cache. A Git discovery ceiling prevents an enclosing checkout from being
misidentified as the archived dependency. It does not update a branch or replace
a pinned dependency.

`run_ci.py build` starts with no W3 output, compiles all local sources, verifies
that their hashes do not change, and records exactly which new `BUILD.json`
succeeded. `run_ci.py audit` then:

1. audits declarations, allowed axioms and unsafe markers;
2. records the proof dependency graph and imported artifact hashes;
3. performs the separate trust-zero import check; and
4. explicitly runs the pinned LeanChecker with `--fresh` over the aggregate.

A complete audit requires both `status: PASS` and `fresh_checker_status: PASS`.
A narrower fallback or import-only success does not satisfy this gate. Source
and declaration checks reject custom axioms, sorry/admit, native_decide, unsafe,
partial, compiler-trust bypasses and related escape hatches in the W3 source.

The checker uses **the same Lean kernel**, not an independently implemented
verifier. Its skipping of unsafe/partial runtime declarations is disclosed;
local W3 declarations are separately gated. Standard foundations are
`propext`, `Classical.choice`, and `Quot.sound`.

## Evidence and failed runs

CI retains `ci-receipts/`, compiler logs and strict audit receipts as an Actions
artifact. Failures are retained rather than converted into successful evidence.
`MANIFEST.sha256` identifies the published source and documentation. The historical
validation summary and repaired audit record are under `verification/`; they do
not replace a new run's own result.

The prepublication source validation reused a pinned local external-dependency
tree. A clean network installation is independently established only by an actual
successful CI run, whose status is visible in GitHub Actions. No unexecuted setup
path is presented as tested.
