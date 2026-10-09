# W3-BFB-EXACT

## Exact quartic stability for the complex Weinberg three-Higgs-doublet model

AI-assisted analytic research and Lean formalization of the unrestricted
Weinberg-model quartic, with a two-spectrum sextic reduction and an explicit
finite exact-operation input-to-output program.

> **Formal revision F002:** all 190 local Lean sources passed fresh compilation
> and strict same-kernel replay. Three renewed four-reviewer AI audit rounds were
> completed and adjudicated with no remaining load-bearing issue. See
> [the exact status and qualifications](verification/RELEASE_STATUS.json).
> GitHub CI records clean-environment reproduction separately.

**Start here:** [scope](docs/SCOPE.md), [reproduction](REPRODUCE.md),
[errata and corrective history](docs/ERRATA.md), and the
[supplied research paper](research/THEOREM.pdf).
Read the original paper together with the errata; its bytes are preserved.

## Mathematical target

The input comprises nine arbitrary real coefficients and three arbitrary complex
coefficients of the tree-level Weinberg 3HDM quartic. The normalized physical
domain is the set of Hermitian positive-semidefinite 3×3 Gram matrices with trace
one and rank at most two, equivalently three complex doublets with total squared norm one.

A shared weighted phase spectrum is applied to the primal and inverse structured
operators. After physical filtering, at most thirty distinct candidate values determine
the minimum. A proved sixteen-level positive infinitesimal deformation handles
all original inputs, including zero couplings, singularities, degeneracies and
flat boundaries. Successive residues recover the original minimum, and an
explicit pivot construction recovers minimizing doublets with total squared norm one.

The finite-input layer supplies a uniform program using rational constants, the
original fifteen inputs and formal infinitesimal generators, with explicit exact
arithmetic, comparison and root primitives. Final stage-zero (`Code 0`) outputs
contain no infinitesimal generators.
Its refinement theorems connect the computed candidate list, sign decisions,
residues and physical witnesses to the semantic mathematical criterion.

## Principal formal entry points

- `W3.FiniteInput.uniform_finite_input_exact_criterion` in
  [`lean/W3/FiniteInputMain.lean`](lean/W3/FiniteInputMain.lean): integrated
  candidate-list, sign, residue, witness and all-retained-minimizer result.
- `W3.FiniteInput.arbitrary_complex_finite_input_criterion` in the same module:
  direct weak/strict/negative/flat statements for unrestricted complex couplings.
- `W3.full_exact_criterion` in [`lean/W3/Main.lean`](lean/W3/Main.lean) and
  `W3.arbitrary_complex_criterion` in
  [`lean/W3/UniversalCriterion.lean`](lean/W3/UniversalCriterion.lean): the
  underlying semantic criterion.

The root module `W3` imports the finite-input endpoint. Lean is pinned to 4.34.1;
Mathlib is pinned to `d13f23b723b8a846827a245b89c10fc7d3f11612`, with all
transitive source pins retained.

## Important limits

- This is a theorem about the **tree-level quartic**. It does not settle arbitrary
  quadratic-plus-quartic potentials, quantum corrections or phenomenology.
- Exact arithmetic/order/root primitives operate semantically over the tower,
  on finite input-derived requests. There is no verified rational/algebraic
  backend, backend-independent portable root-code serialization, extracted
  runnable exact solver, or algorithm for supplying uncomputable arbitrary real
  inputs to a computer. Some runtime ordering/equality choices can use classical
  choice; those uses are not all proof-only.
- The sextic degree bound is for phase elimination. Residue annihilators and final
  minimal polynomials need not have degree at most six.
- The formal auxiliary affine routine uses a stronger generic open set G′.
  The prescribed deformation is proved to lie there for every original input.
  The paper's separate broader G-domain four-chart/gcd auxiliary procedure is
  not fully formalized as a general-purpose interface.
- LeanChecker replays with the same Lean kernel, not an independently implemented
  verifier. Pinned external dependencies are reused; all local W3 source is
  freshly compiled. Formal checking does not itself establish novelty or correct
  correspondence with a physical model.
- This work is AI-assisted. No human peer review, external endorsement, independent
  verifier implementation, or absolute priority certification is claimed.

## Repository guide

- `lean/`: exact frozen formal source, exact dependency pins and portable helpers
- `research/`: original analytic theorem, synopsis, derivations, code and finite data
- `docs/`: reader-facing scope, errata and provenance
- `verification/`: source identities, actual validation/review summaries and replay evidence
- `scripts/`: fail-closed reproduction adapters
- `.github/workflows/verify.yml`: pinned, read-only, serial Lean CI

The original 156-source formalization had a genuine missing uniform input-to-
program bridge. Its earlier completion wording was corrected. Revision F002
adds that bridge and receives separate validation and renewed review; earlier
passes are not silently transferred. [The history is explicit](docs/ERRATA.md).

No project reuse license or individual authorship has been invented. Upstream
Lean, Mathlib and Python dependencies retain their own licenses and are restored
from official sources rather than bundled into this repository.
