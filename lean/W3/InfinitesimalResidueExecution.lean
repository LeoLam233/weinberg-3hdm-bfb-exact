import W3.InfinitesimalExpressionCompiler
import W3.InfinitesimalCoefficientResidueProgram
import W3.InfinitesimalSuccessiveResidue

/-! # Exact execution of the finite successive residue procedure
The inputs explicitly supply exact coefficient equality and finite real-root
enumeration. An expression is compiled to a finite multiplication matrix;
its determinant annihilator is cleared and normalized, and finite comparisons
select the residue. The output carries the next selected-root expression.
-/
noncomputable section
namespace W3.Infinitesimal
open Polynomial
attribute [local instance] rationalTowerAlgebra
set_option backward.isDefEq.respectTransparency false

/-- Exact equality in each rational presentation and exact real-root lists in
each ordered stage are the only additional oracle inputs of residue execution. -/
structure ResidueOracles where
  coefficientEquality : (n : ℕ) → DecidableEq (RationalTower n)
  roots : (n : ℕ) → RealRootEnumeration (Tower realModel n)

/-- A mathematical instance exists; effective implementations provide their
rational/algebraic equality and Thom/root-list implementations of this interface. -/
def mathematicalResidueOracles : ResidueOracles where
  coefficientEquality _ := Classical.decEq _
  roots n := polynomialRootsEnumeration (Tower realModel n)

/-- One-step program before its success proof is used to unwrap the option. -/
def expressionResidueProgram (O : ResidueOracles) (n : ℕ) {x : Tower realModel (n + 1)}
    (e : RootExpression (RationalTower (n + 1)) (Tower realModel (n + 1)) x) :
    Option (Tower realModel n) := by
  letI := O.coefficientEquality n
  letI := O.coefficientEquality (n + 1)
  exact coefficientResidueProgram (rationalTowerHom n) (O.roots n)
    (clearedBivariate e.annihilator) x

/-- This proof exposes the actual computed polynomial used for the output root. -/
theorem expressionResidueProgram_spec (O : ResidueOracles) (n : ℕ)
    {x : Tower realModel (n + 1)}
    (e : RootExpression (RationalTower (n + 1)) (Tower realModel (n + 1)) x)
    (hx : BaseBounded (Tower realModel n) x) :
    letI := O.coefficientEquality n
    letI := O.coefficientEquality (n + 1)
    ∃ q : Tower realModel n, expressionResidueProgram O n e = some q ∧
      HasRelativeResidue (Tower realModel n) x q ∧
      Polynomial.aeval q ((normalizeInitial (clearedBivariate e.annihilator)).2.coeff 0) = 0 := by
  letI := O.coefficientEquality n
  letI := O.coefficientEquality (n + 1)
  have hp := e.annihilator_spec.1.ne_zero
  exact coefficientResidueProgram_correct n (rationalTowerHom n) (O.roots n)
    (clearedBivariate e.annihilator) (clearedBivariate_ne_zero hp) hx
    (clearedBivariate_root (rationalTowerHom n) e.annihilator e.annihilator_spec.2)

structure ResidueStageOutput (n : ℕ) (x : Tower realModel (n + 1)) where
  value : Tower realModel n
  expression : RootExpression (RationalTower n) (Tower realModel n) value
  relativeResidue : HasRelativeResidue (Tower realModel n) x value

/-- Total execution unwraps the proven-successful finite Option result. It does
not choose a residue from an existential algebraicity statement. -/
def executeResidueStage (O : ResidueOracles) (n : ℕ) {x : Tower realModel (n + 1)}
    (e : RootExpression (RationalTower (n + 1)) (Tower realModel (n + 1)) x)
    (hx : BaseBounded (Tower realModel n) x) : ResidueStageOutput n x := by
  letI := O.coefficientEquality n
  letI := O.coefficientEquality (n + 1)
  let out := expressionResidueProgram O n e
  have hs : out.isSome := by
    obtain ⟨q, hq, _, _⟩ := expressionResidueProgram_spec O n e hx
    simp only [out, hq, Option.isSome_some]
  let q := out.get hs
  have hprops : HasRelativeResidue (Tower realModel n) x q ∧
      Polynomial.aeval q ((normalizeInitial (clearedBivariate e.annihilator)).2.coeff 0) = 0 := by
    obtain ⟨r, hr, hres, hroot⟩ := expressionResidueProgram_spec O n e hx
    have heq : q = r := by simp only [q, out, hr, Option.get_some]
    simpa only [heq] using And.intro hres hroot
  exact ⟨q, .selectedRoot _
    (normalizeInitial_correct _ (clearedBivariate_ne_zero e.annihilator_spec.1.ne_zero)).1
    q hprops.2, hprops.1⟩

lemma real_interval_baseBounded (n : ℕ) {x : Tower realModel (n + 1)} {a b : ℝ}
    (ha : baseEmbed realModel (n + 1) a ≤ x) (hb : x ≤ baseEmbed realModel (n + 1) b) :
    BaseBounded (Tower realModel n) x := by
  change Extension (Tower realModel n) at x
  refine ⟨baseEmbed realModel n ((|a| + |b| + 1) : ℝ), ?_, ?_⟩
  · have h : 0 < (|a| + |b| + 1 : ℝ) := by positivity
    simpa only [map_zero] using (orderedFieldHom_strictMono (baseEmbed realModel n)) h
  · apply abs_le.mpr
    constructor
    · have hr : -(|a| + |b| + 1) ≤ a := by linarith [neg_abs_le a, abs_nonneg b]
      have h : baseEmbed realModel (n + 1) (-(|a| + |b| + 1) : ℝ) ≤
          baseEmbed realModel (n + 1) a := (baseEmbed realModel (n + 1)).monotone' hr
      rw [map_neg] at h
      exact h.trans ha
    · have hr : b ≤ |a| + |b| + 1 := by linarith [le_abs_self b, abs_nonneg a]
      exact hb.trans ((baseEmbed realModel (n + 1)).monotone' hr)

/-- Structural recursion executes exactly n preceding-stage residue operations.
All intermediate values remain in the original real interval, and each is
represented by the actual normalized root equation from the preceding step. -/
def executeSuccessiveResidues (O : ResidueOracles) :
    (n : ℕ) → (x : Tower realModel n) →
    RootExpression (RationalTower n) (Tower realModel n) x →
    (a b : ℝ) → baseEmbed realModel n a ≤ x → x ≤ baseEmbed realModel n b →
    {r : ℝ // SuccessiveResidue n x r}
  | 0, x, _, _, _, _, _ => ⟨x, rfl⟩
  | n + 1, x, e, a, b, ha, hb => by
    let step := executeResidueStage O n e (real_interval_baseBounded n ha hb)
    have hbounds := relativeResidue_interval (Tower realModel n) step.relativeResidue ha hb
    let rest := executeSuccessiveResidues O n step.value step.expression a b hbounds.1 hbounds.2
    exact ⟨rest.val, step.value, step.relativeResidue, rest.property⟩

/-- Correctness of the complete finite execution, including all sixteen levels. -/
theorem executeSuccessiveResidues_eq_stdPart (O : ResidueOracles) (n : ℕ)
    (x : Tower realModel n) (e : RootExpression (RationalTower n) (Tower realModel n) x)
    (a b : ℝ) (ha : baseEmbed realModel n a ≤ x) (hb : x ≤ baseEmbed realModel n b) :
    (executeSuccessiveResidues O n x e a b ha hb).val = ArchimedeanClass.stdPart x :=
  (successiveResidue_eq_stdPart n (executeSuccessiveResidues O n x e a b ha hb).property).symm

#print axioms executeResidueStage
#print axioms executeSuccessiveResidues_eq_stdPart
end W3.Infinitesimal
