# Errata and corrective history

The supplied research paper is preserved byte-for-byte under `research/`.
**Read it together with this errata document.** Its original status wording does
not replace the final formal-source and verification record of this repository.

## 1. Zero-support rows: a false sentence with a valid required conclusion

In THEOREM §5.1, the statement that the structured inverse operator R preserves
an entire zero support row of a rank-one projector P is literally false.
The diagonal entry `(RP)ii = (G r)i` can be nonzero because G mixes diagonals.

The required statement is that the off-support **vector component**
`((RP)z)i` vanishes when `zi = 0`. Every off-diagonal term has a zero factor,
and the potentially nonzero diagonal term is multiplied by `zi = 0`.
The component `((RI)z)i = gi zi` also vanishes. The same correction applies
to the primal operator L. This proves the off-support components actually
needed for Eq. (31), without changing the selected spectrum or input domain.

Disposition: confirmed wording error, not a counterexample to the central result.

## 2. Eq. (35): primitive normalization of the resultant

For the integer F and G printed in §6.1, their ordinary Sylvester resultant,
divided by `1 + t²`, is **100 times** the displayed Eq. (35) polynomial.
The displayed polynomial is the primitive-normalized resultant quotient.

The nonzero positive factor 100 changes neither roots, gcd, degree nor the
properness witness. The universal recipe still uses the actual resultant
quotient of Eq. (18). The literal equality in the example must nevertheless be
read with this stated normalization correction.

Disposition: confirmed normalization error, with unchanged root/coverage content.

## 3. Original diagnostic replay wrapper accepted stale output

The original `research/code/replay_checks.py` copies expected JSON outputs into
its execution directory before running a suite. A substituted no-op can therefore
appear to pass. Its comparator also confuses some Boolean/numeric values, and
Python optimization removes assertion-based checks.

The separately published `scripts/hardened_replay.py` copies only code and declared
inputs, requires absent-before/newly-created regular outputs and successful
process exits, compares strict JSON types, rejects nonfinite numbers, and rejects
optimized Python. It is a diagnostic wrapper, not a theorem verifier. The original
wrapper remains historical source and must not be used as the assurance gate.

Fresh direct executions and the corrected replay reproduced all eight named
finite scientific suites. No-op, type, NaN, numerical-value, nonzero-exit and
optimization controls rejected. These facts check the finite computations; they
do not by themselves prove universal stationarity, genericity or residue coverage.

## 4. Formal revision F001 to F002: missing uniform input-to-program bridge

The first 156-source formal development proved the unrestricted mathematical
criterion and semantic residue/witness results, but the third adversarial round
identified a real formalization gap in the full algorithm claim. Existence of
algebraic expressions over a semantic carrier did not yet establish a uniform
finite construction whose scalar leaves have the required input provenance.
The repair explicitly permits rational constants, original inputs and formal
infinitesimal generators at intermediate stages; final `Code 0` outputs contain
no infinitesimal generators.

This was not a disproof of the unchanged analytic theorem. It was also more than
the absence of a concrete executable solver: the abstract input-to-program
composition/provenance theorem itself was missing. Earlier complete-formalization
wording was withdrawn on that precise point.

Revision F002 adds explicit finite input syntax, code-producing construction,
scalar/matrix/witness refinement and all-retained-minimizer provenance. It has its
own frozen source identity and must pass fresh build, kernel and renewed review
gates; earlier passes cannot be transferred to it. The final completion status is
recorded in `../verification/RELEASE_STATUS.json`, not inferred from this history.

## Additional scope boundary

The formal auxiliary affine spectrum routine uses a stronger generic open set
G′ than the paper's broader four-projective-chart/gcd auxiliary domain G. The
canonical deformation is proved to land in G′ for every original coefficient
vector, so this is not a restriction of the central all-input criterion.
The full auxiliary procedure on every weaker undeformed G input is not separately
formalized. See `SCOPE.md` for the exact public claim.
