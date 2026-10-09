import W3.OperatorSpectrumBridge
import W3.GramFactor

/-! Physical doublet witnesses for the concrete primal/dual candidate matrices. -/
noncomputable section
namespace W3.Operator
open Matrix ComplexConjugate
open scoped BigOperators ComplexOrder

def projectorFields (z : Fin 3 → ℂ) : W3.Fields :=
  WithLp.toLp 2 (fun ki => if ki.1 = 0 then conj (z ki.2) else 0)

lemma projectorFields_coordinates (z : Fin 3 → ℂ) :
    fieldCoordinates (projectorFields z) = projectorCoordinates z := by
  apply Prod.ext
  · funext i
    simp [fieldCoordinates,projectorFields,projectorCoordinates,W3.radius,Fin.sum_univ_two]
  · funext i
    fin_cases i <;>
      simp [fieldCoordinates,projectorFields,projectorCoordinates,W3.gram,Fin.sum_univ_two]

lemma projectorFields_normalized (z : Fin 3 → ℂ) (hz : ∑ i, Complex.normSq (z i) = 1) :
    ‖projectorFields z‖ = 1 := by
  have hr : ∑ i, W3.radius (projectorFields z) i = 1 := by
    simpa [W3.radius,projectorFields,Fin.sum_univ_two] using hz
  rw [W3.total_radius] at hr
  nlinarith [norm_nonneg (projectorFields z)]

lemma coordinates_realizable (X : Coordinates) (hpos : (coordinateMatrix X).PosSemidef)
    (hdet : (coordinateMatrix X).det = 0) (htr : (coordinateMatrix X).trace = 1) :
    ∃ φ : W3.Fields, ‖φ‖ = 1 ∧ fieldCoordinates φ = X := by
  obtain ⟨φ,hgram,hnorm⟩ := W3.exists_normalized_gram_factor (coordinateMatrix X) hpos hdet htr
  refine ⟨φ,hnorm,?_⟩
  apply coordinateMatrix_injective
  rw [coordinateMatrix_fieldCoordinates,hgram]

lemma quotient_energy_identity (β a p : ℝ) (ha : a ≠ 0) :
    p / (2 * denominator β a p) =
      (p / a ^ 2) / (2 * (β * (p / a ^ 2) - 1)) := by
  have hden : β * (p / a ^ 2) - 1 = denominator β a p / a ^ 2 := by
    unfold denominator
    field_simp [ha]
  rw [hden, ← mul_div_assoc, div_div]
  field_simp [ha]

/-- Every dual candidate passing the exact scalar filter has an original
normalized complex-doublet witness with exactly its advertised energy. -/
theorem dual_candidate_physical_witness (κ : W3.Couplings)
    (hA : (couplingMatrix κ).det ≠ 0) (hΔ : ∀ i, blockDet (κ.c i) (κ.d i) ≠ 0)
    (z : Fin 3 → ℂ) (hz : ∑ i, Complex.normSq (z i) = 1)
    (hD : denominator (dualBeta (couplingEquiv κ hA hΔ).symm)
      (dualA (couplingEquiv κ hA hΔ).symm z) (dualP (couplingEquiv κ hA hΔ).symm z) ≠ 0)
    (hstat : coordinateMatrix ((dualA (couplingEquiv κ hA hΔ).symm z) •
      (couplingEquiv κ hA hΔ).symm (projectorCoordinates z) -
      (dualP (couplingEquiv κ hA hΔ).symm z) • (couplingEquiv κ hA hΔ).symm identityCoordinates) *ᵥ z = 0)
    (hchi : dualPurity (couplingEquiv κ hA hΔ).symm z ≤ 1) :
    ∃ φ : W3.Fields, ‖φ‖ = 1 ∧
      fieldCoordinates φ = dualCoordinates (couplingEquiv κ hA hΔ).symm z ∧
      W3.quartic κ φ = dualP (couplingEquiv κ hA hΔ).symm z /
        (2 * denominator (dualBeta (couplingEquiv κ hA hΔ).symm)
          (dualA (couplingEquiv κ hA hΔ).symm z) (dualP (couplingEquiv κ hA hΔ).symm z)) := by
  let L := couplingEquiv κ hA hΔ
  let R := L.symm
  have hself := couplingEquiv_selfadjoint κ hA hΔ
  have hR := inverse_selfadjoint L hself
  have hz0 : z ≠ 0 := by intro hz0; simp [hz0] at hz
  have hker := (dual_kernel_iff R z hD).mpr hstat
  have hpos := (dual_physical_filter R hR z hz0 hD hstat).mpr hchi
  have hdet : (coordinateMatrix (dualCoordinates R z)).det = 0 := by
    by_contra hdet
    apply hz0
    exact (Matrix.mulVec_injective_of_det_ne_zero hdet) (by simpa using hker)
  obtain ⟨φ,hφ,hX⟩ := coordinates_realizable (dualCoordinates R z) hpos hdet (dual_trace R hR z hD)
  refine ⟨φ,hφ,hX,?_⟩
  rw [quartic_eq_coordinateEnergy,hX,coordinateEnergy_eq_half_pair]
  exact dual_energy R hR z hD hstat

#print axioms dual_candidate_physical_witness
end W3.Operator
