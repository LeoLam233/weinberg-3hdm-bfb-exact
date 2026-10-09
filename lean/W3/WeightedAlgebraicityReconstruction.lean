import W3.WeightedAlgebraicityOperator

/-! Actual selected primal and dual matrix entries over the finite rational
presentation of the prescribed sixteen infinitesimals. -/
noncomputable section
namespace W3.Weighted
open W3.Elimination W3.Infinitesimal W3.OperatorField W3.TransferOperator
open W3.RealModel W3.StrataTransfer W3.PrimalFieldBridge

theorem actual_primal_projector_algebraic (κ : Fin 15 → ℝ) (x : SpectrumPoint SixteenLevelField)
    (hm : x ∈ spectrumCandidates (originalPrimal (actualParameters κ))
      (canonicalMagnitudes (originalPrimal (actualParameters κ))))
    (z : RealVector SixteenLevelField)
    (hz : PointMatches x (pairVector z 0) (pairVector z 1) (pairVector z 2)) :
    letI := rationalTowerAlgebra 16
    ∀ i, IsAlgebraic (RationalTower 16) (hermitianProjector z i) := by
  letI := rationalTowerAlgebra 16
  exact matched_hermitianProjector_algebraic x (actual_primal_point_algebraic κ x hm) z hz

theorem actual_dual_projector_algebraic (κ : Fin 15 → ℝ) (x : SpectrumPoint SixteenLevelField)
    (hm : x ∈ spectrumCandidates (originalDual (actualParameters κ))
      (canonicalMagnitudes (originalDual (actualParameters κ))))
    (z : RealVector SixteenLevelField)
    (hz : PointMatches x (pairVector z 0) (pairVector z 1) (pairVector z 2)) :
    letI := rationalTowerAlgebra 16
    ∀ i, IsAlgebraic (RationalTower 16) (hermitianProjector z i) := by
  letI := rationalTowerAlgebra 16
  exact matched_hermitianProjector_algebraic x (actual_dual_point_algebraic κ x hm) z hz

/-- Every actual selected charged representative has algebraic reconstructed
matrix entries and algebraic energy. There is no assumed annihilator and no
choice of common amplitude phase in this statement. -/
theorem actual_dual_reconstruction_algebraic (κ : Fin 15 → ℝ) (x : SpectrumPoint SixteenLevelField)
    (hm : x ∈ spectrumCandidates (originalDual (actualParameters κ))
      (canonicalMagnitudes (originalDual (actualParameters κ))))
    (z : RealVector SixteenLevelField)
    (hz : PointMatches x (pairVector z 0) (pairVector z 1) (pairVector z 2)) :
    letI := rationalTowerAlgebra 16
    (∀ i, IsAlgebraic (RationalTower 16) (dualCoordinates (actualParameters κ) z i)) ∧
    IsAlgebraic (RationalTower 16) (dualEnergy (actualParameters κ) z) := by
  letI := rationalTowerAlgebra 16
  have hP := actual_dual_projector_algebraic κ x hm z hz
  have hk := actual_parameter_algebraic κ
  exact ⟨dualCoordinates_algebraic _ _ hk hP,dualEnergy_algebraic _ _ hk hP⟩

/-- The physical purity filter is evaluated on an algebraic scalar over the
same coefficient presentation. -/
theorem actual_dual_purity_algebraic (κ : Fin 15 → ℝ) (x : SpectrumPoint SixteenLevelField)
    (hm : x ∈ spectrumCandidates (originalDual (actualParameters κ))
      (canonicalMagnitudes (originalDual (actualParameters κ))))
    (z : RealVector SixteenLevelField)
    (hz : PointMatches x (pairVector z 0) (pairVector z 1) (pairVector z 2)) :
    letI := rationalTowerAlgebra 16
    IsAlgebraic (RationalTower 16) (dualPurity (actualParameters κ) z) := by
  letI := rationalTowerAlgebra 16
  have hK := (actual_dual_reconstruction_algebraic κ x hm z hz).1
  unfold dualPurity hermitianPurity
  exact (((hK 0).pow 2).add ((hK 1).pow 2)).add ((hK 2).pow 2) |>.add
    ((isAlgebraic_natCast 2).mul ((((((hK 3).pow 2).add ((hK 4).pow 2)).add
      ((hK 5).pow 2)).add ((hK 6).pow 2)).add ((hK 7).pow 2) |>.add ((hK 8).pow 2)))

#print axioms actual_primal_projector_algebraic
#print axioms actual_dual_reconstruction_algebraic
#print axioms actual_dual_purity_algebraic
end W3.Weighted
