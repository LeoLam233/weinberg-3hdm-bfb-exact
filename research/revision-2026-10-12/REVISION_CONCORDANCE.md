# Integrated manuscript revision: change and theorem concordance

Review draft dated 12 October 2026. Base: `5485acb93e9a6dc0631573c07a10e1666b23ca99`, analytic C001 / formal F002. No new formal revision, release, priority certification or human peer-review claim is made.

## Itemized changes

| Original location | Revised treatment | Checkable basis |
| --- | --- | --- |
| Opening status paragraph | Separate review manuscript; replaces reference to absent `REPORT.md` with actual repository evidence | `docs/SCOPE.md`; `verification/RELEASE_STATUS.json` |
| §1 geometry | Replaces text diagram with equivalent branch description | Rank-one primal and rank-two kernel branches remain unchanged |
| §1 theorem | Preserves all five Eq. (3) statements; clarifies thirty is a distinct-value bound | `FiniteInputMain.lean`, `uniform_finite_input_exact_criterion` |
| §1 algorithm scope | Exact semantic primitives, input provenance and backend implementation distinguished | `docs/SCOPE.md` §2; `FiniteInputSyntax.lean`; `InfinitesimalResidueExecution.lean` |
| §5.1 zero-support sentence | Deletes false row-preservation assertion; adds Eq. (31a) and proof: off-diagonal entries vanish and the possibly nonzero diagonal is multiplied by the zero vector component | `docs/ERRATA.md` §1; `OperatorConcrete.lean`, `inverse_projector_zero_component` |
| §6.1 Eq. (35) | Keeps the printed sextic unchanged, calls it primitive-normalized; adds Eq. (35a), ordinary resultant = 100(1+t²) times displayed sextic | `docs/ERRATA.md` §2; exact recomputation in `check_revision.py` |
| §8 | Preserves midpoint residue proof and pivoted Gram-factor proof, including higher-degree residue annihilator warning | Original §§8 and Eq. (41) retained |
| New §8.1 | Adds finite-input proposition and refinement proof: code leaves, literal candidate construction, minimum, sign tests, emitted annihilators, residue execution, pivot witnesses and every retained minimizer | Declaration concordance below |
| New §8.1 root selection | Distinguishes manuscript midpoint description from formal finite nearest-root selection; explains why both recover the residue | `FiniteInputResidueExecution.lean`, `codedResidueStageProgram_correct` |
| New §9.1 | Explicitly separates G from G′; canonical deformed primal/dual inputs lie in G′ for every original input | `docs/SCOPE.md` §3; `ActualGenericity.lean`, `actualParameters_generic` |
| New §9.1 optional variant | Eq. (28) retained as analytic formula, not a separately literal formal endpoint | `docs/SCOPE.md` §3 |
| §9.2 validation | Updates obsolete “no independent agent” wording to source-bound F002 local validation and three four-report AI rounds; discloses same kernel, foundational axioms, reused dependencies and remote-CI distinction | `verification/RELEASE_STATUS.json`; `docs/SCOPE.md` §4 |
| §9.2 finite diagnostics | Discloses stale-output historical wrapper and narrower hardened replay scope | `docs/ERRATA.md` §3; `verification/PUBLIC_SCIENTIFIC_REPLAY.json` |
| References | Retains all three original references and their stated scopes; no new claim of literature-search completeness | Original reference block; `research/SOURCES.md` |

The original equations (1)--(41), all original mathematical sections, the genericity and minimum-coverage arguments, singular completion, residue argument and references are retained. Added equation labels are (31a) and (35a). This is an integrated revision of the existing paper, not a replacement of its proofs by validation claims.

## F002 declaration concordance

Paths below are relative to `lean/W3/`. Namespace is `W3.FiniteInput` except where stated otherwise. Exact source hashes and declaration line locations are in `REVISION_CHECKS.json`; these identify the frozen source, not proof certificates for the revised prose.

| Declaration / file | Hypotheses and literal coverage | Manuscript |
| --- | --- | --- |
| `W3.Operator.inverse_projector_zero_component` / `OperatorConcrete.lean` | Structured inverse, complex vector z, coordinate i with zᵢ=0; corresponding component of inverse-projector matrix times z equals zero | §5.1 |
| `W3.Infinitesimal.actualParameters_generic` / `ActualGenericity.lean` | Any fifteen real original coordinates; complete primal exclusion, inverse denominator and complete dual exclusion are nonzero for canonical deformation | §§7, 9.1 |
| `actualCodeProgram_values` / `FiniteInputActualProgram.lean` | `ResidueOracles`, arbitrary input; interpreted finite-list scalar set equals semantic candidate values | §8.1 |
| `actualCodeProgram_physical` / same file | Membership in literal retained candidate list; normalized field Gram realization and record energy | §8.1 |
| `actualSelectedRecord_value` / same file | Literal finite minimum selection has actual deformed candidate minimum value | §8.1 |
| `signPrograms_spec` / `FiniteInputMain.lean` | Weak/strict physical-Gram positivity, negative minimum, and zero minimum equivalences; no original-input genericity hypothesis | §§1, 8.1 |
| `codedResidueStageProgram_correct` / `FiniteInputResidueExecution.lean` | Finite source code and relative boundedness; succeeds with preceding-stage root code and correct relative residue | §8.1; boundedness is discharged by central construction |
| `actualValueCode_success` / `FiniteInputActualProgram.lean` | Sixteen-stage Option execution succeeds and stage-zero scalar equals original real minimum | §8.1 |
| `actualMatrixCode_spec` / same file | Computed stage-zero Gram is physical and its original-model energy is the original minimum | §8.1 |
| `actualFields_spec` / same file | Returned fields have norm one, correct computed Gram and scalar energy | §8.1 |
| `every_old_retained_minimizer_coded_execution` / `FiniteInputRetainedExecution.lean` | Any matrix in semantic retained set attaining deformed minimum; same matrix has finite-list code provenance, successful coordinate residue execution and normalized minimizing fields | §8.1; no claim every covering-list entry is physical or all original real minimizers are enumerated |
| `uniform_finite_input_exact_criterion` / `FiniteInputMain.lean` | `ResidueOracles` and arbitrary fifteen real coordinates; packages candidate values, ≤30 distinct values, successful minimum selection, sign tests, scalar residue, field witness and all retained minimizing matrices | §8.1 proposition |
| `arbitrary_complex_finite_input_criterion` / same file | Arbitrary `W3.Couplings`; field-domain weak/strict/negative/flat tests | §8.1 |

`ResidueOracles` supplies exact coefficient equality and finite real-root lists. Ordered-field arithmetic/comparisons remain semantic; classical choice occurs in some runtime choices. The theorem does not supply an extracted backend or portable root-code format. The finite syntax prevents arbitrary scalar leaves; it does not make a root index independent of the supplied primitive enumeration.

## Editorial validation and preservation

- Exact integer symbolic recomputation checks Eq. (35a), gcd(F,G)=1 and primitive content one.
- The support correction is checked against the literal Lean declaration and explicit component calculation; the accompanying small symbolic zero check is only diagnostic.
- All referenced endpoint declarations were read at the anchored commit. All 257 tracked files under the original research, Lean, verification and docs directories are byte-compared with that commit. They remain unchanged.
- The revised PDF is rendered and visually inspected, including corrected formula pages and the added formalization section.
- No fresh Lean build, kernel replay, new independent adversarial audit, human peer review or updated priority survey is claimed in this editorial task.

The repository-wide `MANIFEST.sha256` requires every tracked file to appear. The proposed PR therefore only appends inventory entries for the independent revision files; all original manifest lines and all frozen source/validation bytes are preserved. No F002 source identity or validation record is rewritten.

## Reproduction

From the repository root, with Python and SymPy installed:

```bash
python3 research/revision-2026-10-12/check_revision.py
```

The command reproduces exact algebra and frozen-file checks and regenerates `REVISION_CHECKS.json`. It does not build Lean or regenerate the PDF.

PDF generation, with Pandoc, XeLaTeX and DejaVu fonts:

```bash
pandoc research/revision-2026-10-12/THEOREM_REVISED.md \
  -f markdown+tex_math_single_backslash -s \
  --pdf-engine=xelatex \
  --lua-filter=research/revision-2026-10-12/pdf-code.lua \
  -H research/revision-2026-10-12/pdf-header.tex \
  -V geometry:margin=22mm -V papersize=a4 -V fontsize=10pt \
  -V colorlinks=true -V mainfont='DejaVu Serif' \
  -V monofont='DejaVu Sans Mono' \
  -o research/revision-2026-10-12/THEOREM_REVISED.pdf
```

PDF bytes may vary with tool versions and creation timestamps; the mathematical source and exact check are the reproducible content.
