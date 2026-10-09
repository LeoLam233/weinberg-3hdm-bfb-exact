# Publication provenance and trust boundaries

## Scientific and formal source identities

The supplied analytic research candidate is identified as C001. Its original
THEOREM Markdown has SHA-256
`4f87feffa067e1e82e984998828efcffad68d49c92efe3c536ccf9f0051aec66`.
The paper, synopsis, derivations and selected scientific code/data retain their
original bytes. `verification/research-source-map.json` records identities and
the few documented editorial/path transformations in other files.

The repaired formal revision is F002. Its original frozen-source record has
SHA-256
`7fc34595fdb0a21778cf000dfac1484a4d6dd9c0e9dc3aff7ad0fce5f1af73c5`.
`verification/F002_SOURCE_FILES.json` lists the exact 190 published Lean source
hashes and unchanged portable support-file hashes. Source files are not edited
to accommodate publication. The source-freeze record identity and the public
per-file inventory serve different purposes: a reader can directly rehash every
published source file, while the former identifies the retained validation record.

No original or repaired result is inferred from an old status label. F001's
missing uniform input-to-program bridge and all three earlier literal/diagnostic
corrections remain explicit in [ERRATA.md](ERRATA.md). F002 has its own validation
and renewed three-round audit requirement.

## Public evidence is deliberately curated

The machine validation and source-provenance summaries select factual statuses,
counts, exact hashes and limitations from retained execution records. They omit
development-only absolute paths, host resource dumps and private execution
coordinates. Each summary names its transformation and retains SHA-256 identifiers
for the originating records. A selected summary is not presented as the
byte-identical original receipt.

The repaired-review summary likewise retains source binding, completed
adjudications, unresolved-error counts, review/seal hashes and qualifications.
Private execution/task identifiers and raw working reports are omitted. A-D are
local labels within each round. These are AI-generated reviews; correlated
failure modes remain possible. They are not human peer review or external
attestation.

Private conversation, administrative instructions, unlicensed third-party full-
text copies, credentials, user account metadata, and large compiled/runtime/cache
artifacts are not part of the public repository. The bibliography includes links
to relevant scientific sources. A prospective-reviewer-background section was
removed without changing the scientific source record.

## Dependencies and reproduction

The exact Lean compiler and Mathlib/transitive source revisions are fixed in
`lean/lean-toolchain`, `lean/lakefile.toml`, and `lean/lake-manifest.json`.
Nine immutable official source archives were rechecked, covering 10,119 regular
source files; their URLs/hashes and the verification count are published in
`verification/DEPENDENCY_SOURCE_VERIFICATION.json`.

The local fresh replay reused separately fingerprinted compiled dependencies.
The complete 190-source fresh sequence resumed after a verified infrastructure
interruption. A separate interrupted full checker was restarted in full and
completed with exit zero; interrupted attempts were not counted as passes.
`verification/F002_VALIDATION.json` records that qualification and the exact
successful proof-checking stages.

GitHub CI starts from the public source, restores hash-checked official dependency
archives/runtime, fetches the explicitly selected official Mathlib cache, freshly
compiles every local source serially, and runs the strict same-kernel checker.
The CI adapter is publication-specific; it does not change the frozen proof or
portable audit logic. GitHub Actions are fixed to verified commit hashes and the
CI Python interpreter is 3.12.14. Repository permissions are read-only and checkout
does not persist credentials.

A successful CI run establishes that particular clean network/runtime path; it
must be verified in Actions rather than inferred from these instructions.
Reproduction is independent of any private Library account or original development
path. See [REPRODUCE.md](../REPRODUCE.md).

## Licensing and validation limits

No separate project reuse license or individual authorship is inferred or added.
Upstream dependencies remain under their own licenses and are fetched from their
official repositories. The original research is AI-assisted, without a claim of
human review, absolute priority, or a concrete verified exact-computation backend.
