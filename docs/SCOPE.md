# Exact public scope

This document describes the intended F002 theorem statements. Their release
acceptance status is recorded separately in `../verification/RELEASE_STATUS.json`.

## 1. Physical and coefficient domain

The central quartic is

\[
 f(K)=\frac12\sum_i a_i K_{ii}^2+
 \sum_{i<j}\bigl(b_{ij}K_{ii}K_{jj}+c_{ij}|K_{ij}|^2+
 \operatorname{Re}(d_{ij}K_{ij}^2)\bigr).
\]

The nine `a,b,c` coefficients are arbitrary real numbers and the three `d`
coefficients are arbitrary complex numbers. Pair order is 12,13,23. The
normalized physical Gram domain has Hermiticity, positive semidefiniteness,
trace one and rank at most two. It is proved equivalent to three complex doublets with total squared norm one. Neutral rank-one, charged rank-two and missing-
doublet support faces are included.

No genericity, reality, nonzero-coupling, nonsingularity or nondegeneracy condition
is imposed on the original fifteen-real-coordinate input. The quartic is
homogeneous, so weak nonnegativity on all fields and strict positivity on
nonzero fields are linked to the normalized minimum. Negative and flat cases
include recovered normalized physical field witnesses.

This scope is tree-level quartic stability. It is not a result about unrestricted
mass terms or a loop-corrected potential.

## 2. Two spectra and the finite exact-operation program

The common weighted spectrum has singleton, pair and full-support branches.
The full-support phase equations are reduced to degree at most six. Applying
the common mechanism to the primal operator and the inverse structured operator,
then retaining physically admissible entries, yields at most thirty distinct values.
The selected minimum is independently proved equal to the actual physical
minimum of the deformed model.

Sixteen algebraically independent ordered positive infinitesimals implement a
canonical deformation for every original input. The proof establishes the
necessary generic exclusions for both spectra; these exclusions are not an
input promise. Sixteen successive bounded residues return the original minimum
and minimizing Gram matrices. A literal pivoted square-root construction returns
complex doublets with total squared norm one.

The F002 endpoint is stronger than mere algebraicity or existence of semantic
expressions. Intermediate finite syntax uses rational constants, the original fifteen
inputs and formal infinitesimal generators; final stage-zero (`Code 0`) outputs
contain no infinitesimal generators. A uniform code-producing construction has refinement theorems for the
candidate values, selected minimum, sign programs, residue execution, physical
witness and every retained minimizing matrix.

Arithmetic, equality/order and finite real-root operations remain exact semantic
interfaces over the tower, acting on finite input-derived requests. Their concrete
representation-level implementations are not part of this repository. Neither a
verified rational/algebraic backend nor backend-independent portable root-code
serialization is claimed. Some finite runtime ordering/equality choices can use classical choice; these
uses are not all proof-only. Classical reasoning also appears in the mathematics; the
artifact is not an extracted executable solver, a concrete root isolator, or a
computability assertion for uncomputable real data. The root/phase sextic bound
must not be applied to all later annihilators.

## 3. Auxiliary generic domains must remain distinct

The paper's auxiliary four-projective-chart/gcd procedure admits a broader
regular domain G. The formal affine candidate API uses stronger polynomial
exclusions, denoted here by G′: in particular, it excludes projective-boundary
roots and nonunique linear recovery fibers for that one affine chart.

The formal proof does establish projective-root equivalence on G′ and proves
that the canonical primal and inverse-dual deformations belong to G′ for every
original coefficient vector. Consequently the **central original-input domain
is unrestricted**. It is nevertheless incorrect to describe the formal affine
API as a full formalization of the broader undeformed G-domain auxiliary
four-chart algorithm. That broader interface and its general intersection-
multiplicity count are not separately packaged in full. The optional paper
Eq. (28) coefficient-evaluation variant is also not a separate literal endpoint;
the formal physical filter uses the proved exact purity identity.

## 4. What verification establishes

A fresh local-source build checks the precise Lean statements in the release.
The source/declaration gate rejects custom scientific axioms, sorry/admit,
unsafe/partial W3 declarations, native-decide shortcuts and compiler-trust
bypasses. Allowed foundational axioms are `propext`, `Classical.choice` and
`Quot.sound`.

The explicit LeanChecker replay uses the same Lean kernel. Runtime declaration
skipping is disclosed separately from the stricter local W3 gate. Pinned
external dependency artifacts are fingerprinted/reused, not all rebuilt from
source in the prepublication run. Source hashes and actual run statuses identify
what was checked; an old PASS label is not evidence for a revised source.

Independent adversarial review is separate from kernel compilation and is
recorded by source-bound round. Finite symbolic/numerical diagnostics have their
own narrower claims; sample agreement is not promoted to a universal theorem.
No human peer review, external endorsement, absolute firstness or practical
runtime advantage is established by these checks.
