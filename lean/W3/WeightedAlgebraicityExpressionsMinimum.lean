import W3.WeightedAlgebraicityExpressionsCanonical
import W3.OperatorFieldTwoSpectrum

/-! The literal selected minimum has a finite arithmetic/selected-root syntax,
constructed directly from the spectrum equations rather than an arbitrary
polynomial or a new finite-dimensional-basis oracle. -/
noncomputable section
namespace W3.Weighted.Expression
open W3.Elimination W3.Infinitesimal W3.OperatorField W3.RealModel

theorem actual_deformedMinimum_presented (κ : Parameters ℝ) :
    letI := rationalTowerAlgebra 16
    Presented (RationalTower 16) (deformedMinimum κ) :=
  actual_twoSpectrum_value_presented κ (actualParameters_generic κ).2.2 _
    (deformedMinimum_mem_actualCandidateValues κ)

theorem actual_candidateMinimum_presented (κ : Parameters ℝ) :
    letI := rationalTowerAlgebra 16
    Presented (RationalTower 16) (actualCandidateMinimum κ) := by
  rw [actualCandidateMinimum_eq]
  exact actual_deformedMinimum_presented κ

#print axioms actual_candidateMinimum_presented
end W3.Weighted.Expression
