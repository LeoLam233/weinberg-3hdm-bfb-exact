import W3.OperatorFieldTwoSpectrum
import W3.GramSemantics
import W3.ActualWitness

/-! The unrestricted two-spectrum sextic criterion. The candidate set is the
literal singleton/pair/sextic construction with exact physical filtering.
Every genericity, minimizer, stationarity and perturbation premise is discharged.
Finite successive residue-program correctness is packaged separately. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace W3
open W3.RealModel W3.Infinitesimal W3.OperatorField

/-- Equation (3), on precisely the normalized physical Gram domain of the
original statement, for arbitrary fifteen real coordinates. -/
theorem universal_exact_criterion (κ : Parameters ℝ) :
    (actualCandidateValues κ).card ≤ 30 ∧
    (actualCandidateValues κ).Nonempty ∧
    ((∀ K,PhysicalGram K → 0 ≤ gramQuartic (couplings κ) K) ↔ 0 < actualCandidateMinimum κ) ∧
    ((∀ K,PhysicalGram K → 0 < gramQuartic (couplings κ) K) ↔
      2*chronologicalEpsilon 0 < actualCandidateMinimum κ) ∧
    (realMinimum κ < 0 ↔ actualCandidateMinimum κ < 0) ∧
    (realMinimum κ = 0 ↔ 0 < actualCandidateMinimum κ ∧
      actualCandidateMinimum κ < 2*chronologicalEpsilon 0) ∧
    ArchimedeanClass.stdPart (actualCandidateMinimum κ) = realMinimum κ := by
  obtain ⟨hw,hs,hn,hz,hr⟩ := actual_minimum_signs_and_residue κ
  obtain ⟨hgweak,hgstrict⟩ := gram_stability_equivalences κ
  refine ⟨actualCandidateValues_card_le_thirty κ,actualCandidateValues_nonempty κ,?_⟩
  rw [actualCandidateMinimum_eq]
  exact ⟨hgweak.trans hw,hgstrict.trans hs,hn,hz,hr⟩

/-- The claimed minimum is truly the minimum over all physical Gram matrices. -/
theorem universal_minimum_identification (κ : Parameters ℝ) :
    actualCandidateMinimum κ = deformedMinimum κ ∧
    (∀ K,PhysicalGram K → realMinimum κ ≤ gramQuartic (couplings κ) K) ∧
    ∃ K,PhysicalGram K ∧ gramQuartic (couplings κ) K=realMinimum κ :=
  ⟨actualCandidateMinimum_eq κ,realMinimum_gram κ⟩

/-- Every retained value is physically realizable in the actual ordered field;
there are no extraneous complex-resultant roots in the retained list. -/
theorem universal_candidates_physical (κ : Parameters ℝ) (v : SixteenLevelField)
    (hv : v ∈ actualCandidateValues κ) :
    ∃ x : RealFields SixteenLevelField,mass x=1 ∧ quarticReal (actualParameters κ) x=v :=
  actualCandidateValues_physical κ v hv

/-- Original unrestricted complex-coupling formulation: the coordinate encoding
is an exact round trip, with no reality, nonzero or generic-input premise. -/
theorem arbitrary_complex_criterion (k : Couplings) :
    let κ := Elimination.originalOfCouplings k
    ((∀ φ : Fields,0≤quartic k φ) ↔ 0<actualCandidateMinimum κ) ∧
    ((∀ φ : Fields,φ≠0→0<quartic k φ) ↔ 2*chronologicalEpsilon 0<actualCandidateMinimum κ) ∧
    ((∃ φ : Fields,‖φ‖=1 ∧ quartic k φ<0) ↔ actualCandidateMinimum κ<0) ∧
    (((∀ φ : Fields,0≤quartic k φ) ∧ ∃ φ : Fields,‖φ‖=1 ∧ quartic k φ=0) ↔
      0<actualCandidateMinimum κ ∧ actualCandidateMinimum κ<2*chronologicalEpsilon 0) := by
  dsimp only
  rw [actualCandidateMinimum_eq]
  have h := actual_physical_sign_tests (Elimination.originalOfCouplings k)
  rwa [all_complex_couplings] at h

/-- A real minimizing direction exists, with the exact energy recovered from
the selected infinitesimal minimum. Negative and flat cases use the same witness. -/
theorem universal_original_field_witness (κ : Parameters ℝ) :
    ∃ φ : Fields, ‖φ‖=1 ∧ quartic (couplings κ) φ =
      ArchimedeanClass.stdPart (actualCandidateMinimum κ) := by
  rw [actualCandidateMinimum_eq,(actual_minimum_signs_and_residue κ).2.2.2.2]
  exact ⟨fields (realMinimumPoint κ),realMinimum_field_norm κ,realMinimum_field_value κ⟩

#print axioms universal_exact_criterion
#print axioms universal_minimum_identification
#print axioms arbitrary_complex_criterion
end W3
