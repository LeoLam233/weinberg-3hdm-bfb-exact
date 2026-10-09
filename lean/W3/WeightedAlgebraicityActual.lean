import W3.WeightedAlgebraicitySelected
import W3.InfinitesimalRationalTower
import W3.ActualGenericity
import W3.InfinitesimalRealBase

/-! The actual fifteen-coordinate deformation has a finite iterated-rational
coefficient presentation. Selected primal and dual outputs are algebraic over
that presentation, not just over the full ultrapower. -/
noncomputable section
namespace W3.Weighted
open W3.Elimination W3.Infinitesimal

/-- Exact coefficient presentation, with all six trace-square shifts and all
fifteen independent higher infinitesimals retained in source order. -/
def rationalActualParameters (κ : Fin 15 → ℝ) (i : Fin 15) : RationalTower 16 :=
  rationalBase 16 (κ i) + (if i.val < 6 then 2*rationalChronologicalEpsilon 0 else 0) +
    rationalChronologicalEpsilon i.succ

@[simp] theorem rationalActualParameters_map (κ : Fin 15 → ℝ) (i : Fin 15) :
    rationalTowerHom 16 (rationalActualParameters κ i) = actualParameters κ i := by
  unfold rationalActualParameters actualParameters W3.RealModel.deformedParameters coefficientEpsilon
  split_ifs <;> simp only [map_add,map_mul,map_ofNat,map_zero,
    rationalTowerHom_base,rationalTowerHom_chronologicalEpsilon] <;> rfl

/-- Rational inversion commutes with any coefficient-field embedding. -/
theorem originalDual_map {F L : Type*} [Field F] [Field L] (f : F →+* L) (x : Fin 15 → F) :
    mapWeighted f (originalDual x) = originalDual (fun i => f (x i)) := by
  simp [mapWeighted,originalDual,originalAdj,originalMatrixDet,originalDelta12,
    originalDelta13,originalDelta23,map_div₀,map_ofNat]

@[simp] theorem actualPrimal_presentation (κ : Fin 15 → ℝ) :
    mapWeighted (rationalTowerHom 16) (originalPrimal (rationalActualParameters κ)) =
      originalPrimal (actualParameters κ) := by
  rw [map_originalPrimal]
  simp only [rationalActualParameters_map]

@[simp] theorem actualDual_presentation (κ : Fin 15 → ℝ) :
    mapWeighted (rationalTowerHom 16) (originalDual (rationalActualParameters κ)) =
      originalDual (actualParameters κ) := by
  rw [originalDual_map]
  simp only [rationalActualParameters_map]

/-- Actual original-plus-infinitesimal coefficients are in the coefficient
presentation itself, hence algebraic there without any extra premise. -/
theorem actual_parameter_algebraic (κ : Fin 15 → ℝ) (i : Fin 15) :
    letI := rationalTowerAlgebra 16
    IsAlgebraic (RationalTower 16) (actualParameters κ i) := by
  letI := rationalTowerAlgebra 16
  rw [← rationalActualParameters_map]
  exact isAlgebraic_algebraMap (R:=RationalTower 16) (A:=SixteenLevelField) (rationalActualParameters κ i)

/-- Actual selected neutral values have a non-assumed algebraic annihilator
over the finite sixteen-variable rational coefficient presentation. -/
theorem actual_primal_value_algebraic (κ : Fin 15 → ℝ) (ν : SixteenLevelField)
    (hm : ν ∈ exactCommonSpectrum (originalPrimal (actualParameters κ))) :
    letI := rationalTowerAlgebra 16
    IsAlgebraic (RationalTower 16) ν := by
  letI := rationalTowerAlgebra 16
  have hp : mapWeighted (algebraMap (RationalTower 16) SixteenLevelField)
      (originalPrimal (rationalActualParameters κ)) = originalPrimal (actualParameters κ) :=
    actualPrimal_presentation κ
  have he : weightedExceptional (mapWeighted (algebraMap (RationalTower 16) SixteenLevelField)
      (originalPrimal (rationalActualParameters κ))) ≠ 0 := by
    rw [hp]
    exact (mul_ne_zero_iff.mp (actualParameters_generic κ).1).1
  apply exactCommonSpectrum_algebraic (originalPrimal (rationalActualParameters κ)) he ν
  rwa [hp]

/-- Actual selected inverse-operator values are algebraic over the identical
presentation; all inverse matrix and off-diagonal denominators are represented. -/
theorem actual_dual_value_algebraic (κ : Fin 15 → ℝ) (ν : SixteenLevelField)
    (hm : ν ∈ exactCommonSpectrum (originalDual (actualParameters κ))) :
    letI := rationalTowerAlgebra 16
    IsAlgebraic (RationalTower 16) ν := by
  letI := rationalTowerAlgebra 16
  have hp : mapWeighted (algebraMap (RationalTower 16) SixteenLevelField)
      (originalDual (rationalActualParameters κ)) = originalDual (actualParameters κ) :=
    actualDual_presentation κ
  have he : weightedExceptional (mapWeighted (algebraMap (RationalTower 16) SixteenLevelField)
      (originalDual (rationalActualParameters κ))) ≠ 0 := by
    rw [hp]
    exact (mul_ne_zero_iff.mp (actualParameters_generic κ).2.2).1
  apply exactCommonSpectrum_algebraic (originalDual (rationalActualParameters κ)) he ν
  rwa [hp]

/-- An actual presented candidate has algebraic normalized radii and phases. -/
theorem actual_presented_point_algebraic
    (w : WeightedData (RationalTower 16)) (v : WeightedData SixteenLevelField)
    (hp : mapWeighted (rationalTowerHom 16) w = v)
    (he : weightedExceptional v ≠ 0) (x : SpectrumPoint SixteenLevelField)
    (hm : x ∈ spectrumCandidates v (canonicalMagnitudes v)) :
    letI := rationalTowerAlgebra 16
    AlgebraicPoint (RationalTower 16) x := by
  letI := rationalTowerAlgebra 16
  rw [← hp] at he hm
  exact spectrumCandidates_algebraic w (base_sextic_ne_zero_of_mapped_generic w he)
    _ (fun i => (canonicalMagnitudes_spec _ i).2) x hm

theorem actual_primal_point_algebraic (κ : Fin 15 → ℝ) (x : SpectrumPoint SixteenLevelField)
    (hm : x ∈ spectrumCandidates (originalPrimal (actualParameters κ))
      (canonicalMagnitudes (originalPrimal (actualParameters κ)))) :
    letI := rationalTowerAlgebra 16
    AlgebraicPoint (RationalTower 16) x :=
  actual_presented_point_algebraic _ _ (actualPrimal_presentation κ)
    (mul_ne_zero_iff.mp (actualParameters_generic κ).1).1 x hm

theorem actual_dual_point_algebraic (κ : Fin 15 → ℝ) (x : SpectrumPoint SixteenLevelField)
    (hm : x ∈ spectrumCandidates (originalDual (actualParameters κ))
      (canonicalMagnitudes (originalDual (actualParameters κ)))) :
    letI := rationalTowerAlgebra 16
    AlgebraicPoint (RationalTower 16) x :=
  actual_presented_point_algebraic _ _ (actualDual_presentation κ)
    (mul_ne_zero_iff.mp (actualParameters_generic κ).2.2).1 x hm

#print axioms actual_primal_value_algebraic
#print axioms actual_dual_value_algebraic
#print axioms rationalActualParameters_map
end W3.Weighted
