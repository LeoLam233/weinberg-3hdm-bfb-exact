import W3.UniversalCriterion
import W3.WeightedAlgebraicityMinimum
import W3.InfinitesimalAlgebraicTower
import W3.TransferOperatorRetainedResidue

/-! The exact selected list and signs in the actual algebraic real-closed
sixteen-stage field, rather than identifying the larger ambient ultrapower
with an algebraic Puiseux field. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace W3
open W3.RealModel W3.Infinitesimal W3.OperatorField W3.TransferOperator W3.Weighted
attribute [local instance] rationalTowerAlgebra

/-- Every literal retained value belongs to the algebraic field. -/
theorem candidateValue_mem_algebraicTower (κ : Parameters ℝ) (v : SixteenLevelField)
    (hv : v ∈ actualCandidateValues κ) :
    v ∈ algebraicClosure (RationalTower 16) SixteenLevelField :=
  mem_algebraicClosure_iff.mpr (actual_twoSpectrum_value_algebraic κ _ v hv)

/-- The minimum and all selected physical matrix entries lie in the same field. -/
theorem candidateMinimum_mem_algebraicTower (κ : Parameters ℝ) :
    actualCandidateMinimum κ ∈ algebraicClosure (RationalTower 16) SixteenLevelField :=
  mem_algebraicClosure_iff.mpr (actual_candidateMinimum_algebraic κ)

theorem retainedMatrix_mem_algebraicTower (κ : Parameters ℝ) (y : Matrix16)
    (hy : y ∈ actualRetainedMatrices κ) (i : Fin 9) :
    y i ∈ algebraicClosure (RationalTower 16) SixteenLevelField :=
  mem_algebraicClosure_iff.mpr (actualRetainedMatrices_algebraic κ y hy i)

def algebraicCandidate (κ : Parameters ℝ)
    (v : {x : SixteenLevelField // x ∈ actualCandidateValues κ}) : AlgebraicTower 16 :=
  ⟨v.val,candidateValue_mem_algebraicTower κ v.val v.property⟩

def algebraicCandidateValues (κ : Parameters ℝ) : Finset (AlgebraicTower 16) := by
  classical
  exact (actualCandidateValues κ).attach.image (algebraicCandidate κ)

def algebraicCandidateMinimum (κ : Parameters ℝ) : AlgebraicTower 16 :=
  ⟨actualCandidateMinimum κ,candidateMinimum_mem_algebraicTower κ⟩

def algebraicEpsilon (i : Fin 16) : AlgebraicTower 16 :=
  ⟨chronologicalEpsilon i,mem_algebraicClosure_iff.mpr (by
    rw [← rationalTowerHom_chronologicalEpsilon]
    exact isAlgebraic_algebraMap (R := RationalTower 16) (A := SixteenLevelField) (rationalChronologicalEpsilon i))⟩

/-- The lifted list has exactly the same ordered scalar values. -/
theorem algebraicCandidateValues_image (κ : Parameters ℝ) :
    (algebraicCandidateValues κ).image (fun v : AlgebraicTower 16 => (v : SixteenLevelField)) = actualCandidateValues κ := by
  classical
  ext v
  simp only [algebraicCandidateValues,Finset.mem_image,Finset.mem_attach,true_and]
  constructor
  · rintro ⟨r,⟨s,rfl⟩,h⟩
    change s.val=v at h
    exact h ▸ s.property
  · intro h
    exact ⟨algebraicCandidate κ ⟨v,h⟩,⟨⟨v,h⟩,rfl⟩,rfl⟩

theorem algebraicCandidateValues_card_le_thirty (κ : Parameters ℝ) :
    (algebraicCandidateValues κ).card≤30 := by
  classical
  exact Finset.card_image_le.trans (by simpa using actualCandidateValues_card_le_thirty κ)

/-- This is the actual minimum of the same finite list in the restricted field. -/
theorem algebraicCandidateMinimum_spec (κ : Parameters ℝ) :
    algebraicCandidateMinimum κ ∈ algebraicCandidateValues κ ∧
      ∀ v ∈ algebraicCandidateValues κ,algebraicCandidateMinimum κ≤v := by
  classical
  constructor
  · apply Finset.mem_image.mpr
    refine ⟨⟨actualCandidateMinimum κ,Finset.min'_mem _ _⟩,Finset.mem_attach _ _,?_⟩
    rfl
  · intro v hv
    have hval : (v : SixteenLevelField) ∈ actualCandidateValues κ := by
      rw [← algebraicCandidateValues_image κ]
      exact Finset.mem_image.mpr ⟨v,hv,rfl⟩
    exact Finset.min'_le _ _ hval

/-- Equation (3)'s weak and strict signs, now typed in the actual algebraic
real-closed field containing the finite root computation. -/
theorem algebraic_field_sign_tests (κ : Parameters ℝ) :
    ((∀ K,PhysicalGram K→0≤gramQuartic (couplings κ) K) ↔ 0<algebraicCandidateMinimum κ) ∧
    ((∀ K,PhysicalGram K→0<gramQuartic (couplings κ) K) ↔
      2*algebraicEpsilon 0<algebraicCandidateMinimum κ) := by
  have h := universal_exact_criterion κ
  exact ⟨h.2.2.1,h.2.2.2.1⟩

#print axioms candidateValue_mem_algebraicTower
#print axioms algebraicCandidateMinimum_spec
#print axioms algebraic_field_sign_tests
end W3
