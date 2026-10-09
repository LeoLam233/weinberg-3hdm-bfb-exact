# Supplied analytic research artifacts

**Read [the errata](../docs/ERRATA.md) before using the paper.** The paper contains
two confirmed non-load-bearing literal corrections; the original replay wrapper
has a separately repaired diagnostic defect. The original bytes of THEOREM,
DERIVATIONS, the specialist synopsis, their supplied PDFs, and the scientific
code/results are preserved here.

These files are the analytic research draft and exploratory/finite evidence.
The repository's current scope and formal verification status are in the root
README and `verification/RELEASE_STATUS.json`. Original internal-status phrases,
archived output labels and successful sample computations do not override that
record or establish external peer review or scientific priority.

The source paper's references to its original REPORT, VERIFICATION or RECOVERY
files refer to the earlier research package. This public edition instead provides
curated reader-facing status, reproduction instructions and corrective history;
those earlier administrative files are not included. `SOURCES.md` retains the
scientific literature record but omits the prospective-reviewer-background
section. Exact source identities and transformations are recorded in
`../verification/research-source-map.json`.

The floating-point prototype is not an exact decision solver. For a fail-closed
replay of the eight named finite suites, use `scripts/hardened_replay.py` from the
repository root, not the historical `code/replay_checks.py`.

No license or individual authorship has been inferred or added to the supplied
research artifacts. Upstream dependencies retain their own licenses and are
restored from their official sources rather than redistributed here.
