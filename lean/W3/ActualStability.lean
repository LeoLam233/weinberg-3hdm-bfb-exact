import W3.ActualMinimum
import W3.EliminationOperator

/-! Physical interpretation of the actual infinitesimal sign tests, with every
complex doublet and every original complex coupling included. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace W3.Infinitesimal
open W3.RealModel

lemma quarticReal_coordinates (κ : Parameters ℝ) (φ : W3.Fields) :
    quarticReal κ (coordinates φ) = W3.quartic (couplings κ) φ := by
  rw [quarticReal, twiceQuartic_coordinates]
  ring
lemma quarticReal_fields (κ : Parameters ℝ) (x : RealFields ℝ) :
    quarticReal κ x = W3.quartic (couplings κ) (fields x) := by
  rw [quarticReal, twiceQuartic_fields]
  ring

lemma realMinimum_field_norm (κ : Parameters ℝ) : ‖fields (realMinimumPoint κ)‖ = 1 := by
  have h := (realMinimumPoint_spec κ).1
  rw [mass_fields] at h
  nlinarith [norm_nonneg (fields (realMinimumPoint κ))]

lemma realMinimum_field_value (κ : Parameters ℝ) :
    W3.quartic (couplings κ) (fields (realMinimumPoint κ)) = realMinimum κ :=
  (quarticReal_fields κ _).symm

lemma realMinimum_le_field (κ : Parameters ℝ) (φ : W3.Fields) (hφ : ‖φ‖ = 1) :
    realMinimum κ ≤ W3.quartic (couplings κ) φ := by
  rw [← quarticReal_coordinates]
  exact (realMinimumPoint_spec κ).2 (coordinates φ) (by rw [mass_coordinates,hφ]; norm_num)

/-- Weak stability means nonnegativity on all original complex doublets. -/
theorem weak_stability_iff_realMinimum (κ : Parameters ℝ) :
    (∀ φ : W3.Fields, 0 ≤ W3.quartic (couplings κ) φ) ↔ 0 ≤ realMinimum κ := by
  rw [W3.nonnegative_iff_normalized]
  constructor
  · intro h
    simpa only [realMinimum_field_value] using h _ (realMinimum_field_norm κ)
  · intro h φ hφ
    exact h.trans (realMinimum_le_field κ φ hφ)

/-- Strict stability includes every nonzero complex field configuration. -/
theorem strict_stability_iff_realMinimum (κ : Parameters ℝ) :
    (∀ φ : W3.Fields, φ ≠ 0 → 0 < W3.quartic (couplings κ) φ) ↔ 0 < realMinimum κ := by
  rw [W3.positive_iff_normalized]
  constructor
  · intro h
    simpa only [realMinimum_field_value] using h _ (realMinimum_field_norm κ)
  · intro h φ hφ
    exact h.trans_le (realMinimum_le_field κ φ hφ)

/-- The exact negative witness is normalized and genuinely physical. -/
theorem negative_direction_iff_realMinimum (κ : Parameters ℝ) :
    (∃ φ : W3.Fields, ‖φ‖ = 1 ∧ W3.quartic (couplings κ) φ < 0) ↔ realMinimum κ < 0 := by
  constructor
  · rintro ⟨φ,hφ,hn⟩
    exact lt_of_le_of_lt (realMinimum_le_field κ φ hφ) hn
  · intro h
    exact ⟨fields (realMinimumPoint κ), realMinimum_field_norm κ,
      by rwa [realMinimum_field_value]⟩

/-- A stable flat direction is exactly the zero-minimum case. -/
theorem flat_direction_iff_realMinimum (κ : Parameters ℝ) :
    ((∀ φ : W3.Fields, 0 ≤ W3.quartic (couplings κ) φ) ∧
      ∃ φ : W3.Fields, ‖φ‖ = 1 ∧ W3.quartic (couplings κ) φ = 0) ↔ realMinimum κ = 0 := by
  rw [weak_stability_iff_realMinimum]
  constructor
  · rintro ⟨h,φ,hφ,hzero⟩
    have hle := realMinimum_le_field κ φ hφ
    linarith
  · intro h
    refine ⟨h.ge, fields (realMinimumPoint κ), realMinimum_field_norm κ, ?_⟩
    rwa [realMinimum_field_value]

/-- Equation (3) in physical semantics. The value here is the actual attained
perturbed minimum; its identification with the finite two-spectrum algorithm is
an additional theorem, not built into this definition. -/
theorem actual_physical_sign_tests (κ : Parameters ℝ) :
    ((∀ φ : W3.Fields, 0 ≤ W3.quartic (couplings κ) φ) ↔ 0 < deformedMinimum κ) ∧
    ((∀ φ : W3.Fields, φ ≠ 0 → 0 < W3.quartic (couplings κ) φ) ↔
      2*chronologicalEpsilon 0 < deformedMinimum κ) ∧
    ((∃ φ : W3.Fields, ‖φ‖ = 1 ∧ W3.quartic (couplings κ) φ < 0) ↔ deformedMinimum κ < 0) ∧
    (((∀ φ : W3.Fields, 0 ≤ W3.quartic (couplings κ) φ) ∧
      ∃ φ : W3.Fields, ‖φ‖ = 1 ∧ W3.quartic (couplings κ) φ = 0) ↔
      0 < deformedMinimum κ ∧ deformedMinimum κ < 2*chronologicalEpsilon 0) := by
  obtain ⟨hw,hs,hn,hz,_⟩ := actual_minimum_signs_and_residue κ
  exact ⟨(weak_stability_iff_realMinimum κ).trans hw,
    (strict_stability_iff_realMinimum κ).trans hs,
    (negative_direction_iff_realMinimum κ).trans hn,
    (flat_direction_iff_realMinimum κ).trans hz⟩

/-- The canonical real-coordinate encoding is surjective onto all complex
couplings, including zero and arbitrary degenerate inputs. -/
theorem all_complex_couplings (k : W3.Couplings) :
    couplings (W3.Elimination.originalOfCouplings k) = k :=
  W3.Elimination.couplings_original_roundtrip k

#print axioms actual_physical_sign_tests
#print axioms all_complex_couplings
end W3.Infinitesimal
