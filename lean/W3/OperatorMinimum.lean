import W3.OperatorGenericCharged

/-! Actual normalized charged minima enter the reconstructed physical dual list. -/
noncomputable section
namespace W3.Operator
open Matrix W3.Weighted W3.Elimination
open scoped BigOperators ComplexOrder

/-- The complete charged/operator bridge for the real generic model. Every
hypothesis is an explicit physical, invertibility, or polynomial-genericity condition. -/
theorem generic_minimum_rank_two_candidate (κ : W3.Couplings)
    (hA : (couplingMatrix κ).det ≠ 0) (hΔ : ∀ i, blockDet (κ.c i) (κ.d i) ≠ 0)
    (hex : completeWeightedExceptional (operatorDualData (couplingMatrix κ) κ.c κ.d) ≠ 0)
    (φ : W3.Fields) (hφ : ‖φ‖ = 1)
    (hmin : ∀ ψ : W3.Fields, ‖ψ‖ = 1 → W3.quartic κ φ ≤ W3.quartic κ ψ)
    (hrank : (W3.gram φ).rank = 2) :
    ∃ z : Fin 3 → ℂ,
      (∑ i, Complex.normSq (z i)) = 1 ∧
      dualA (couplingEquiv κ hA hΔ).symm z ≠ 0 ∧
      denominator (dualBeta (couplingEquiv κ hA hΔ).symm)
        (dualA (couplingEquiv κ hA hΔ).symm z) (dualP (couplingEquiv κ hA hΔ).symm z) ≠ 0 ∧
      fieldCoordinates φ = dualCoordinates (couplingEquiv κ hA hΔ).symm z ∧
      coordinateMatrix ((dualA (couplingEquiv κ hA hΔ).symm z) •
        (couplingEquiv κ hA hΔ).symm (projectorCoordinates z) -
        (dualP (couplingEquiv κ hA hΔ).symm z) • (couplingEquiv κ hA hΔ).symm identityCoordinates) *ᵥ z = 0 ∧
      dualPurity (couplingEquiv κ hA hΔ).symm z ≤ 1 ∧
      W3.quartic κ φ = dualP (couplingEquiv κ hA hΔ).symm z /
        (2 * denominator (dualBeta (couplingEquiv κ hA hΔ).symm)
          (dualA (couplingEquiv κ hA hΔ).symm z) (dualP (couplingEquiv κ hA hΔ).symm z)) := by
  obtain ⟨z,μ,hunit,hker,hnormal⟩ := normalized_minimum_rank_two κ φ hφ hmin hrank
  let L := couplingEquiv κ hA hΔ
  have hself := couplingEquiv_selfadjoint κ hA hΔ
  have htr : (coordinateMatrix (fieldCoordinates φ)).trace = 1 := by
    rw [coordinateMatrix_fieldCoordinates, W3.gram_trace, hφ]
    norm_num
  have hker' : coordinateMatrix (fieldCoordinates φ) *ᵥ z = 0 := by
    rwa [coordinateMatrix_fieldCoordinates]
  have hD := generic_normal_denominator_ne_zero κ hA hΔ hex (fieldCoordinates φ) z
    (2 * W3.quartic κ φ) μ hunit htr hker' hnormal
  have ha := generic_normal_a_ne_zero κ hA hΔ hex (fieldCoordinates φ) z
    (2 * W3.quartic κ φ) μ hunit htr hker' hnormal
  have hrec := normal_charged_reconstruction L hself (fieldCoordinates φ) z
    (2 * W3.quartic κ φ) μ htr hker' hnormal hD
  have hstat := normal_charged_projective L hself (fieldCoordinates φ) z
    (2 * W3.quartic κ φ) μ htr hker' hnormal hD
  refine ⟨z,hunit,ha,hD,hrec,hstat,?_,?_⟩
  · have hz : z ≠ 0 := by intro hz; simp [hz] at hunit
    apply (dual_physical_filter L.symm (inverse_selfadjoint L hself) z hz hD hstat).mp
    rw [← hrec, coordinateMatrix_fieldCoordinates]
    exact W3.gram_posSemidef φ
  · have heq := normal_charged_equations L hself (fieldCoordinates φ) z
      (2 * W3.quartic κ φ) μ htr hker' hnormal
    have hlam := (charged_equations_unique _ _ _ _ _ hD heq).1
    apply (eq_div_iff (mul_ne_zero (by norm_num) hD)).mpr
    have h := (eq_div_iff hD).mp hlam
    linear_combination h

#print axioms generic_minimum_rank_two_candidate
end W3.Operator
