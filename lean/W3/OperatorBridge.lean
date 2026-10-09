import W3.OperatorModel
import W3.OperatorPhysical

/-! Concrete charged reconstruction certificates in the actual Hermitian matrix model. -/
noncomputable section
namespace W3.Operator
open ComplexConjugate Matrix
open scoped BigOperators ComplexOrder

lemma coordinate_trace (X : Coordinates) :
    (coordinateMatrix X).trace = (coordinatePair identityCoordinates X : ℂ) := by
  simp [coordinateMatrix, coordinatePair, identityCoordinates, Matrix.trace, Fin.sum_univ_three]

def coordinateAction (z : Fin 3 → ℂ) : Coordinates →ₗ[ℝ] (Fin 3 → ℂ) :=
  ((Matrix.mulVecBilin ℝ ℂ).flip z).comp coordinateMatrixLinear

@[simp] lemma coordinateAction_apply (z : Fin 3 → ℂ) (X : Coordinates) :
    coordinateAction z X = coordinateMatrix X *ᵥ z := rfl

lemma pair_projector_of_kernel (X : Coordinates) (z : Fin 3 → ℂ)
    (hker : coordinateMatrix X *ᵥ z = 0) :
    coordinatePair X (projectorCoordinates z) = 0 := by
  rw [coordinatePair_eq_trace, coordinateMatrix_projector]
  change ((coordinateMatrix X * Matrix.vecMulVec z (fun i => conj (z i))).trace).re = 0
  rw [Matrix.mul_vecMulVec, hker]
  simp

/-- The inverse of a self-adjoint equivalence is self-adjoint, with no definiteness requirement. -/
lemma inverse_selfadjoint (L : Coordinates ≃ₗ[ℝ] Coordinates)
    (hL : ∀ x y, coordinatePair x (L y) = coordinatePair (L x) y) (x y : Coordinates) :
    coordinatePair x (L.symm y) = coordinatePair (L.symm x) y := by
  have h := hL (L.symm x) (L.symm y)
  simpa using h.symm

def couplingEquiv (κ : W3.Couplings) (hA : (couplingMatrix κ).det ≠ 0)
    (hΔ : ∀ i, blockDet (κ.c i) (κ.d i) ≠ 0) : Coordinates ≃ₗ[ℝ] Coordinates :=
  structuredEquiv (couplingMatrix κ) κ.c κ.d hA hΔ

lemma couplingEquiv_selfadjoint (κ : W3.Couplings) (hA : (couplingMatrix κ).det ≠ 0)
    (hΔ : ∀ i, blockDet (κ.c i) (κ.d i) ≠ 0) (x y : Coordinates) :
    coordinatePair x (couplingEquiv κ hA hΔ y) =
      coordinatePair (couplingEquiv κ hA hΔ x) y := couplingOperator_selfadjoint κ x y

lemma couplingInverse_selfadjoint (κ : W3.Couplings) (hA : (couplingMatrix κ).det ≠ 0)
    (hΔ : ∀ i, blockDet (κ.c i) (κ.d i) ≠ 0) (x y : Coordinates) :
    coordinatePair x ((couplingEquiv κ hA hΔ).symm y) =
      coordinatePair ((couplingEquiv κ hA hΔ).symm x) y :=
  inverse_selfadjoint _ (couplingEquiv_selfadjoint κ hA hΔ) x y

def dualBeta (R : Coordinates ≃ₗ[ℝ] Coordinates) : ℝ :=
  coordinatePair identityCoordinates (R identityCoordinates)

def dualA (R : Coordinates ≃ₗ[ℝ] Coordinates) (z : Fin 3 → ℂ) : ℝ :=
  coordinatePair (projectorCoordinates z) (R identityCoordinates)

def dualP (R : Coordinates ≃ₗ[ℝ] Coordinates) (z : Fin 3 → ℂ) : ℝ :=
  coordinatePair (projectorCoordinates z) (R (projectorCoordinates z))

def dualCoordinates (R : Coordinates ≃ₗ[ℝ] Coordinates) (z : Fin 3 → ℂ) : Coordinates :=
  reconstruction (dualBeta R) (dualA R z) (dualP R z)
    (R identityCoordinates) (R (projectorCoordinates z))

def dualPurity (R : Coordinates ≃ₗ[ℝ] Coordinates) (z : Fin 3 → ℂ) : ℝ :=
  ((dualP R z) ^ 2 * coordinatePair (R identityCoordinates) (R identityCoordinates) -
    2 * dualP R z * dualA R z * coordinatePair (R identityCoordinates) (R (projectorCoordinates z)) +
    (dualA R z) ^ 2 * coordinatePair (R (projectorCoordinates z)) (R (projectorCoordinates z))) /
      denominator (dualBeta R) (dualA R z) (dualP R z) ^ 2

lemma dual_trace_pair (R : Coordinates ≃ₗ[ℝ] Coordinates)
    (hR : ∀ x y, coordinatePair x (R y) = coordinatePair (R x) y)
    (z : Fin 3 → ℂ) : coordinatePair identityCoordinates (R (projectorCoordinates z)) = dualA R z := by
  rw [hR, coordinatePair_symmetric]
  rfl

lemma dual_trace (R : Coordinates ≃ₗ[ℝ] Coordinates)
    (hR : ∀ x y, coordinatePair x (R y) = coordinatePair (R x) y)
    (z : Fin 3 → ℂ) (hD : denominator (dualBeta R) (dualA R z) (dualP R z) ≠ 0) :
    (coordinateMatrix (dualCoordinates R z)).trace = 1 := by
  rw [coordinate_trace]
  have h := reconstruction_trace (dualBeta R) (dualA R z) (dualP R z)
    (R identityCoordinates) (R (projectorCoordinates z))
    (coordinateBilinear identityCoordinates) rfl (dual_trace_pair R hR z) hD
  change coordinatePair identityCoordinates (dualCoordinates R z) = 1 at h
  rw [h]
  norm_num

/-- Exact charged-to-projective kernel equivalence, valid also when p=0. -/
lemma dual_kernel_iff (R : Coordinates ≃ₗ[ℝ] Coordinates) (z : Fin 3 → ℂ)
    (hD : denominator (dualBeta R) (dualA R z) (dualP R z) ≠ 0) :
    coordinateMatrix (dualCoordinates R z) *ᵥ z = 0 ↔
      coordinateMatrix ((dualA R z) • R (projectorCoordinates z) -
        (dualP R z) • R identityCoordinates) *ᵥ z = 0 :=
  reconstruction_kernel_iff _ _ _ _ _ (coordinateAction z) hD

lemma dual_purity_eq_trace (R : Coordinates ≃ₗ[ℝ] Coordinates) (z : Fin 3 → ℂ) :
    dualPurity R z =
      (coordinateMatrix (dualCoordinates R z) * coordinateMatrix (dualCoordinates R z)).trace.re := by
  rw [← coordinatePair_eq_trace]
  exact (reconstruction_purity _ _ _ _ _ coordinateBilinear
    (coordinatePair_symmetric _ _)).symm

/-- All physical filtering hypotheses are now discharged by concrete matrix identities. -/
theorem dual_physical_filter (R : Coordinates ≃ₗ[ℝ] Coordinates)
    (hR : ∀ x y, coordinatePair x (R y) = coordinatePair (R x) y)
    (z : Fin 3 → ℂ) (hz : z ≠ 0)
    (hD : denominator (dualBeta R) (dualA R z) (dualP R z) ≠ 0)
    (hstat : coordinateMatrix ((dualA R z) • R (projectorCoordinates z) -
      (dualP R z) • R identityCoordinates) *ᵥ z = 0) :
    (coordinateMatrix (dualCoordinates R z)).PosSemidef ↔ dualPurity R z ≤ 1 := by
  rw [dual_purity_eq_trace]
  exact physical_filter_of_kernel _ (coordinateMatrix_hermitian _)
    (dual_trace R hR z hD) z hz ((dual_kernel_iff R z hD).mpr hstat)

/-- Exact reconstructed energy, with no division by p or by the dual quotient. -/
theorem dual_energy (R : Coordinates ≃ₗ[ℝ] Coordinates)
    (hR : ∀ x y, coordinatePair x (R y) = coordinatePair (R x) y)
    (z : Fin 3 → ℂ) (hD : denominator (dualBeta R) (dualA R z) (dualP R z) ≠ 0)
    (hstat : coordinateMatrix ((dualA R z) • R (projectorCoordinates z) -
      (dualP R z) • R identityCoordinates) *ᵥ z = 0) :
    coordinatePair (dualCoordinates R z) (R.symm (dualCoordinates R z)) / 2 =
      dualP R z / (2 * denominator (dualBeta R) (dualA R z) (dualP R z)) := by
  apply reconstruction_energy _ _ _ _ _ identityCoordinates (projectorCoordinates z)
    R.symm.toLinearMap coordinateBilinear (R.symm_apply_apply _) (R.symm_apply_apply _)
  · change coordinatePair (dualCoordinates R z) identityCoordinates = 1
    rw [coordinatePair_symmetric]
    exact reconstruction_trace _ _ _ _ _ (coordinateBilinear identityCoordinates)
      rfl (dual_trace_pair R hR z) hD
  · exact pair_projector_of_kernel _ z ((dual_kernel_iff R z hD).mpr hstat)

#print axioms dual_physical_filter
#print axioms dual_energy
end W3.Operator
