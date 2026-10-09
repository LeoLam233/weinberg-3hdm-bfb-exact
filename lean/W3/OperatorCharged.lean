import W3.OperatorBridge
import W3.OperatorStrata

/-! From the proved rank-two normal equation to the exact charged system,
reconstruction, and complete exceptional alternatives. -/
noncomputable section
namespace W3.Operator
open Matrix
open scoped BigOperators ComplexOrder

lemma normal_equation_coordinates (L : Coordinates ≃ₗ[ℝ] Coordinates)
    (K : Coordinates) (z : Fin 3 → ℂ) (lam μ : ℝ)
    (h : coordinateMatrix (L K) = lam • 1 + μ • projector z) :
    L K = lam • identityCoordinates + μ • projectorCoordinates z := by
  apply coordinateMatrix_injective
  change coordinateMatrix (L K) = coordinateMatrixLinear (lam • identityCoordinates + μ • projectorCoordinates z)
  simp only [map_add, map_smul, coordinateMatrixLinear_apply, coordinateMatrix_identity,
    coordinateMatrix_projector]
  exact h

lemma inverse_normal_equation (L : Coordinates ≃ₗ[ℝ] Coordinates)
    (K : Coordinates) (z : Fin 3 → ℂ) (lam μ : ℝ)
    (h : coordinateMatrix (L K) = lam • 1 + μ • projector z) :
    K = lam • L.symm identityCoordinates + μ • L.symm (projectorCoordinates z) := by
  have h' := congrArg L.symm (normal_equation_coordinates L K z lam μ h)
  simpa using h'

/-- Equation (30) is derived from actual trace one and the actual matrix kernel. -/
theorem normal_charged_equations (L : Coordinates ≃ₗ[ℝ] Coordinates)
    (hL : ∀ x y, coordinatePair x (L y) = coordinatePair (L x) y)
    (K : Coordinates) (z : Fin 3 → ℂ) (lam μ : ℝ)
    (htr : (coordinateMatrix K).trace = 1) (hker : coordinateMatrix K *ᵥ z = 0)
    (hnormal : coordinateMatrix (L K) = lam • 1 + μ • projector z) :
    ChargedEquations (dualBeta L.symm) (dualA L.symm z) (dualP L.symm z) lam μ := by
  have hrep := inverse_normal_equation L K z lam μ hnormal
  have hTrK : coordinatePair identityCoordinates K = 1 := by
    rw [coordinate_trace] at htr
    exact_mod_cast htr
  have hTrV := dual_trace_pair L.symm (inverse_selfadjoint L hL) z
  have h₁ := congrArg (coordinateBilinear identityCoordinates) hrep
  simp only [map_add, map_smul, smul_eq_mul, coordinateBilinear_apply] at h₁
  rw [hTrK,hTrV] at h₁
  have hPK : coordinatePair (projectorCoordinates z) K = 0 := by
    rw [coordinatePair_symmetric]
    exact pair_projector_of_kernel K z hker
  have h₂ := congrArg (coordinateBilinear (projectorCoordinates z)) hrep
  simp only [map_add, map_smul, smul_eq_mul, coordinateBilinear_apply] at h₂
  rw [hPK] at h₂
  constructor
  · dsimp [dualBeta] at *
    nlinarith [h₁]
  · dsimp [dualA, dualP] at *
    nlinarith [h₂]

/-- Equation (25) is the unique charged point whenever its determinant is nonzero. -/
theorem normal_charged_reconstruction (L : Coordinates ≃ₗ[ℝ] Coordinates)
    (hL : ∀ x y, coordinatePair x (L y) = coordinatePair (L x) y)
    (K : Coordinates) (z : Fin 3 → ℂ) (lam μ : ℝ)
    (htr : (coordinateMatrix K).trace = 1) (hker : coordinateMatrix K *ᵥ z = 0)
    (hnormal : coordinateMatrix (L K) = lam • 1 + μ • projector z)
    (hD : denominator (dualBeta L.symm) (dualA L.symm z) (dualP L.symm z) ≠ 0) :
    K = dualCoordinates L.symm z :=
  charged_reconstruction_unique L identityCoordinates (projectorCoordinates z) K _ _ _ lam μ hD
    (normal_charged_equations L hL K z lam μ htr hker hnormal)
    (normal_equation_coordinates L K z lam μ hnormal)

/-- The dual projective vector equation follows from the physical charged minimum. -/
theorem normal_charged_projective (L : Coordinates ≃ₗ[ℝ] Coordinates)
    (hL : ∀ x y, coordinatePair x (L y) = coordinatePair (L x) y)
    (K : Coordinates) (z : Fin 3 → ℂ) (lam μ : ℝ)
    (htr : (coordinateMatrix K).trace = 1) (hker : coordinateMatrix K *ᵥ z = 0)
    (hnormal : coordinateMatrix (L K) = lam • 1 + μ • projector z)
    (hD : denominator (dualBeta L.symm) (dualA L.symm z) (dualP L.symm z) ≠ 0) :
    coordinateMatrix ((dualA L.symm z) • L.symm (projectorCoordinates z) -
      (dualP L.symm z) • L.symm identityCoordinates) *ᵥ z = 0 := by
  apply (dual_kernel_iff L.symm z hD).mp
  rw [← normal_charged_reconstruction L hL K z lam μ htr hker hnormal hD]
  exact hker

/-- Exhaustive determinant alternatives, including every singular linear-system case. -/
theorem normal_charged_cases (L : Coordinates ≃ₗ[ℝ] Coordinates)
    (hL : ∀ x y, coordinatePair x (L y) = coordinatePair (L x) y)
    (K : Coordinates) (z : Fin 3 → ℂ) (lam μ : ℝ)
    (htr : (coordinateMatrix K).trace = 1) (hker : coordinateMatrix K *ᵥ z = 0)
    (hnormal : coordinateMatrix (L K) = lam • 1 + μ • projector z) :
    (denominator (dualBeta L.symm) (dualA L.symm z) (dualP L.symm z) ≠ 0 ∧
      K = dualCoordinates L.symm z) ∨
    (dualA L.symm z = 0 ∧ dualP L.symm z = 0 ∧ dualBeta L.symm ≠ 0 ∧
      lam = 1 / dualBeta L.symm) := by
  by_cases hD : denominator (dualBeta L.symm) (dualA L.symm z) (dualP L.symm z) = 0
  · exact Or.inr ((charged_equations_singular_iff _ _ _ _ _ hD).mp
      (normal_charged_equations L hL K z lam μ htr hker hnormal))
  · exact Or.inl ⟨hD,normal_charged_reconstruction L hL K z lam μ htr hker hnormal hD⟩

/-- The singular branch's constrained-projective equation is also retained. -/
theorem normal_charged_singular (L : Coordinates ≃ₗ[ℝ] Coordinates)
    (hL : ∀ x y, coordinatePair x (L y) = coordinatePair (L x) y)
    (K : Coordinates) (z : Fin 3 → ℂ) (lam μ : ℝ)
    (htr : (coordinateMatrix K).trace = 1) (hker : coordinateMatrix K *ᵥ z = 0)
    (hnormal : coordinateMatrix (L K) = lam • 1 + μ • projector z)
    (hD : denominator (dualBeta L.symm) (dualA L.symm z) (dualP L.symm z) = 0)
    (hU : coordinateMatrix (L.symm identityCoordinates) *ᵥ z ≠ 0) :
    μ ≠ 0 ∧ coordinateMatrix (L.symm (projectorCoordinates z)) *ᵥ z =
      (-lam / μ) • (coordinateMatrix (L.symm identityCoordinates) *ᵥ z) := by
  have hEq := normal_charged_equations L hL K z lam μ htr hker hnormal
  have hrep := inverse_normal_equation L K z lam μ hnormal
  have hμ := singular_mu_ne_zero _ _ _ lam μ _ _ K (coordinateAction z) hD hEq hrep hker hU
  exact ⟨hμ,kernel_proportional lam μ _ _ K (coordinateAction z) hμ hrep hker⟩

#print axioms normal_charged_reconstruction
#print axioms normal_charged_projective
#print axioms normal_charged_singular
end W3.Operator
