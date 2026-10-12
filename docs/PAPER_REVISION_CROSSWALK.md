# F002 integrated manuscript: revision and proof crosswalk

**Base:** `research/THEOREM.md` (preserved, blob `456b55bdc8976d4f6ae0d61757e3d2c0238b7373`).  
**New text:** `manuscript/WEINBERG_3HDM_F002_REVISED.md` (candidate manuscript; not a release).  
**Date:** 2026-10-12. All repository-relative paths refer to the root.

| Location | Original issue | Revised disposition | Primary checks |
|---|---|---|---|
| Header | Historical status points to absent REPORT.md | Replaced with F002-specific scope/status pointers | `research/README.md`; `verification/RELEASE_STATUS.json` |
| §1 effective-operation paragraph | Did not state precise formal program bridge | Exact semantics distinguished from runnable backend | `lean/W3/FiniteInputMain.lean`; `docs/SCOPE.md` §2 |
| §5.1 after (31) | False assertion that R preserves all zero-support rows | Proved only the *vector* component `((RP)z)_i=0` for `z_i=0`, likewise `(RI)z`, and primal L | `docs/ERRATA.md` §1; operator formula (21) |
| §6.1 Eq. (35) | Omitted normalization factor | `Res_u(F,G)=100(1+t²) S_prim(t)`; (35) is primitive normalization | `docs/ERRATA.md` §2; independently recomputed with SymPy Sylvester resultant, exact equality |
| §8.1 (new) | Missing F002 formal construction and input provenance | Finite syntax, input-derived requests, `Code 0`, signs, residues, witnesses, all retained minimizing matrices | `W3.FiniteInput.uniform_finite_input_exact_criterion`; `arbitrary_complex_finite_input_criterion`; `actualCodeProgram`; `every_old_retained_minimizer_coded_execution` |
| §8.1 (new) | G versus G′ could be conflated | Broader undeformed four-chart/gcd G not claimed as formalized on all G; canonical deformation always lies in G′ | `docs/SCOPE.md` §3; `docs/ERRATA.md` |
| §8.2 (new) | Old claim about no proof assistant verification obsolete | Precisely reported 190-source fresh build, same-kernel replay, three four-agent AI audit rounds | `verification/RELEASE_STATUS.json` dated 2026-10-09 |
| §8.2, §9 | Risk of overclaiming computational output and review | No verified root backend/portable serialization/human review/independent checker; external pins reused; local verification distinguished from CI | `docs/SCOPE.md` §§2,4 |
| §9 | Diagnostic replay status omitted | Historical stale-output wrapper distinguished from hardened finite diagnostic | `docs/ERRATA.md` §3 |
| Last reference note | Non-public REPORT.md implied current | Updated to public `research/SOURCES.md` / `docs/PROVENANCE.md` | `research/README.md` |

## Scope of checking in this editorial PR

- Full scientific narrative, numbered equations (1)–(41), stationarity branches, deformation proof and [BPR06], [LRT25], [MN15] references remain present.
- Original files under `research/`, frozen `lean/`, and records under `verification/` are untouched.
- The **specific (35) polynomial identity was independently recalculated** exactly: `resultant(F,G,u)-100(1+t²)*S_prim(t)=0`.
- F002 theorem **statements and immediate implementations** were inspected, but this manuscript edit is **not a newly executed Lean build**, a new multi-agent independent audit, or a new human review.
- No claim is made that all mathematical steps of this revised prose have been independently re-proved. This document is the traceability record for specialist editorial review.

## Distinctions not to erase

1. Analytic center theorem for all 15 real input coordinates vs a stronger *auxiliary* G′ domain on canonically deformed data.
2. Finite input-derived abstract syntax and proved semantic refinement vs concrete computable arithmetic/root backend.
3. Local same-kernel replay vs independently implemented verifier and independent external review.
4. Phase sextic roots vs potentially higher-degree residue annihilators.
5. All-retained-minimizer coverage conditional on membership and minimum-energy premise vs unrestricted statement about all Gram matrices.
