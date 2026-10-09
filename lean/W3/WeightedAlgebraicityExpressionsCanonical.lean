import W3.WeightedAlgebraicityExpressionsReconstruction
import W3.OperatorFieldCandidates

noncomputable section
namespace W3.Weighted.Expression
open W3.Elimination W3.Infinitesimal W3.OperatorField W3.TransferOperator
open W3.RealModel W3.StrataTransfer W3.PrimalFieldBridge

theorem actual_primal_candidate_presented (κ : Fin 15 → ℝ)
    (hp : completeWeightedExceptional (originalPrimal (actualParameters κ)) ≠ 0)
    (j : CandidateIndex (originalPrimal (actualParameters κ))) :
    letI := rationalTowerAlgebra 16
    ∀ i, Presented (RationalTower 16)
      (hermitianProjector (candidateVector _ hp j) i) :=
  actual_primal_projector_presented κ j.val j.property _ (candidateVector_spec _ hp j).1

theorem actual_dual_candidate_presented (κ : Fin 15 → ℝ)
    (hd : completeWeightedExceptional (originalDual (actualParameters κ)) ≠ 0)
    (j : CandidateIndex (originalDual (actualParameters κ))) :
    letI := rationalTowerAlgebra 16
    (∀ i, Presented (RationalTower 16)
      (dualCoordinates (actualParameters κ) (candidateVector _ hd j) i)) ∧
    Presented (RationalTower 16)
      (dualEnergy (actualParameters κ) (candidateVector _ hd j)) :=
  actual_dual_reconstruction_presented κ j.val j.property _ (candidateVector_spec _ hd j).1

/-- Every value in the actual retained list of at most thirty values is
presented over the sixteen-variable rational coefficient presentation. -/
theorem actual_twoSpectrum_value_presented (κ : Fin 15 → ℝ)
    (hd : completeWeightedExceptional (originalDual (actualParameters κ)) ≠ 0)
    (v : SixteenLevelField) (hv : v ∈ twoSpectrumValues (actualParameters κ) hd) :
    letI := rationalTowerAlgebra 16
    Presented (RationalTower 16) v := by
  letI := rationalTowerAlgebra 16
  classical
  rcases Finset.mem_union.mp hv with hp | hdual
  · exact actual_primal_value_presented κ v hp
  · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hdual
    exact (actual_dual_candidate_presented κ hd j).2

#print axioms actual_primal_candidate_presented
#print axioms actual_dual_candidate_presented
#print axioms actual_twoSpectrum_value_presented

end W3.Weighted.Expression
