import W3.WeightedAlgebraicityExpressions

noncomputable section
namespace W3.Weighted.Expression
open W3.Elimination W3.Infinitesimal

/-- Actual original-plus-infinitesimal coefficients are in the coefficient
presentation itself, hence presented there without any extra premise. -/
theorem actual_parameter_presented (κ : Fin 15 → ℝ) (i : Fin 15) :
    letI := rationalTowerAlgebra 16
    Presented (RationalTower 16) (actualParameters κ i) := by
  letI := rationalTowerAlgebra 16
  rw [← rationalActualParameters_map]
  exact expr_algebraMap (R:=RationalTower 16) (A:=SixteenLevelField) (rationalActualParameters κ i)

/-- Actual selected neutral values have finite root-expression presentations
over the sixteen-variable rational coefficient field. -/
theorem actual_primal_value_presented (κ : Fin 15 → ℝ) (ν : SixteenLevelField)
    (hm : ν ∈ exactCommonSpectrum (originalPrimal (actualParameters κ))) :
    letI := rationalTowerAlgebra 16
    Presented (RationalTower 16) ν := by
  letI := rationalTowerAlgebra 16
  have hp : mapWeighted (algebraMap (RationalTower 16) SixteenLevelField)
      (originalPrimal (rationalActualParameters κ)) = originalPrimal (actualParameters κ) :=
    actualPrimal_presentation κ
  have he : weightedExceptional (mapWeighted (algebraMap (RationalTower 16) SixteenLevelField)
      (originalPrimal (rationalActualParameters κ))) ≠ 0 := by
    rw [hp]
    exact (mul_ne_zero_iff.mp (actualParameters_generic κ).1).1
  apply exactCommonSpectrum_presented (originalPrimal (rationalActualParameters κ)) he ν
  rwa [hp]

/-- Actual selected inverse-operator values are presented over the identical
presentation; all inverse matrix and off-diagonal denominators are represented. -/
theorem actual_dual_value_presented (κ : Fin 15 → ℝ) (ν : SixteenLevelField)
    (hm : ν ∈ exactCommonSpectrum (originalDual (actualParameters κ))) :
    letI := rationalTowerAlgebra 16
    Presented (RationalTower 16) ν := by
  letI := rationalTowerAlgebra 16
  have hp : mapWeighted (algebraMap (RationalTower 16) SixteenLevelField)
      (originalDual (rationalActualParameters κ)) = originalDual (actualParameters κ) :=
    actualDual_presentation κ
  have he : weightedExceptional (mapWeighted (algebraMap (RationalTower 16) SixteenLevelField)
      (originalDual (rationalActualParameters κ))) ≠ 0 := by
    rw [hp]
    exact (mul_ne_zero_iff.mp (actualParameters_generic κ).2.2).1
  apply exactCommonSpectrum_presented (originalDual (rationalActualParameters κ)) he ν
  rwa [hp]

/-- An actual presented candidate has presented normalized radii and phases. -/
theorem actual_presented_point_presented
    (w : WeightedData (RationalTower 16)) (v : WeightedData SixteenLevelField)
    (hp : mapWeighted (rationalTowerHom 16) w = v)
    (he : weightedExceptional v ≠ 0) (x : SpectrumPoint SixteenLevelField)
    (hm : x ∈ spectrumCandidates v (canonicalMagnitudes v)) :
    letI := rationalTowerAlgebra 16
    PresentedPoint (RationalTower 16) x := by
  letI := rationalTowerAlgebra 16
  rw [← hp] at he hm
  exact spectrumCandidates_presented w (base_sextic_ne_zero_of_mapped_generic w he)
    _ (fun i => (canonicalMagnitudes_spec _ i).2) x hm

theorem actual_primal_point_presented (κ : Fin 15 → ℝ) (x : SpectrumPoint SixteenLevelField)
    (hm : x ∈ spectrumCandidates (originalPrimal (actualParameters κ))
      (canonicalMagnitudes (originalPrimal (actualParameters κ)))) :
    letI := rationalTowerAlgebra 16
    PresentedPoint (RationalTower 16) x :=
  actual_presented_point_presented _ _ (actualPrimal_presentation κ)
    (mul_ne_zero_iff.mp (actualParameters_generic κ).1).1 x hm

theorem actual_dual_point_presented (κ : Fin 15 → ℝ) (x : SpectrumPoint SixteenLevelField)
    (hm : x ∈ spectrumCandidates (originalDual (actualParameters κ))
      (canonicalMagnitudes (originalDual (actualParameters κ)))) :
    letI := rationalTowerAlgebra 16
    PresentedPoint (RationalTower 16) x :=
  actual_presented_point_presented _ _ (actualDual_presentation κ)
    (mul_ne_zero_iff.mp (actualParameters_generic κ).2.2).1 x hm

#print axioms actual_primal_value_presented
#print axioms actual_dual_value_presented
#print axioms rationalActualParameters_map

end W3.Weighted.Expression
