import W3.OperatorFieldCandidates
import W3.OperatorFieldSoundness
import W3.ActualMinimum

/-! The actual nonarchimedean two-spectrum theorem for every fifteen real
input coefficients. The finite list is literal, bounded by thirty, physically
sound, and its minimum is the attained physical minimum. -/
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace W3.OperatorField
open W3.TransferOperator W3.Elimination W3.RealModel W3.StrataTransfer W3.PrimalFieldBridge W3.Weighted W3.Infinitesimal
open scoped BigOperators

lemma dual_value_physical (k : Parameters SixteenLevelField) (hk : originalInverseDen k ≠ 0)
    (hd : completeWeightedExceptional (originalDual k) ≠ 0)
    (v : SixteenLevelField) (hv : v ∈ dualValues k hd) :
    ∃ x : RealFields SixteenLevelField,mass x=1 ∧ quarticReal k x=v := by
  classical
  obtain ⟨q,hfilter,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨hD,hchi⟩ := (Finset.mem_filter.mp hfilter).2
  have hs := candidateVector_spec _ hd q
  obtain ⟨lam,hamp⟩ := hs.2.2.2
  obtain ⟨x,hx,hG,hE⟩ := dual_candidate_physical k hk (candidateVector _ hd q) lam hs.2.1 hamp hD hchi
  exact ⟨x,hx,hE⟩

/-- Every retained finite-list value has an actual normalized twelve-coordinate field. -/
theorem twoSpectrumValues_physical (k : Parameters SixteenLevelField) (hk : originalInverseDen k ≠ 0)
    (hp : completeWeightedExceptional (originalPrimal k) ≠ 0)
    (hd : completeWeightedExceptional (originalDual k) ≠ 0)
    (v : SixteenLevelField) (hv : v ∈ twoSpectrumValues k hd) :
    ∃ x : RealFields SixteenLevelField,mass x=1 ∧ quarticReal k x=v := by
  classical
  rcases Finset.mem_union.mp hv with h | h
  · exact primal_value_physical k hp v h
  · exact dual_value_physical k hk hd v h

/-- Actual universal physical minimization implies membership in the literal list. -/
theorem normalized_minimum_mem_twoSpectrum (k : Parameters SixteenLevelField) (hk : originalInverseDen k ≠ 0)
    (hp : completeWeightedExceptional (originalPrimal k) ≠ 0)
    (hd : completeWeightedExceptional (originalDual k) ≠ 0)
    (x : RealFields SixteenLevelField) (hx : mass x=1)
    (hmin : ∀ y,mass y=1 → quarticReal k x≤quarticReal k y) :
    quarticReal k x ∈ twoSpectrumValues k hd := by
  classical
  have hmin2 : ∀ y,mass y=1 → twiceQuartic k x≤twiceQuartic k y := by
    intro y hy
    have h := hmin y hy
    dsimp only [quarticReal] at h
    linarith
  obtain ⟨z,hunit,hneutral | hcharged⟩ := sixteen_minimum_neutral_or_charged k x hx hmin2
  · exact Finset.mem_union_left _ (neutral_stratum_mem_primal k hp x z hunit hneutral.1 hneutral.2)
  · obtain ⟨hnker,hchi,mu,hn⟩ := hcharged
    apply Finset.mem_union_right
    rw [quarticReal,← hermitianEnergy_gramCoordinates k x]
    exact charged_stratum_mem_dual k hk hd (gramCoordinates x) z (twiceQuartic k x) mu hunit hnker.1
      ((actionLinear_zero_iff z _).mpr hnker.2.2) hn hchi

def twoSpectrumMinimum (k : Parameters SixteenLevelField)
    (hd : completeWeightedExceptional (originalDual k) ≠ 0) : SixteenLevelField :=
  (twoSpectrumValues k hd).min' (twoSpectrumValues_nonempty k hd)

theorem twoSpectrumMinimum_eq (k : Parameters SixteenLevelField) (hk : originalInverseDen k ≠ 0)
    (hp : completeWeightedExceptional (originalPrimal k) ≠ 0)
    (hd : completeWeightedExceptional (originalDual k) ≠ 0)
    (x : RealFields SixteenLevelField) (hx : mass x=1)
    (hmin : ∀ y,mass y=1 → quarticReal k x≤quarticReal k y) :
    twoSpectrumMinimum k hd = quarticReal k x := by
  apply le_antisymm
  · exact Finset.min'_le _ _ (normalized_minimum_mem_twoSpectrum k hk hp hd x hx hmin)
  · have hm : twoSpectrumMinimum k hd ∈ twoSpectrumValues k hd :=
      Finset.min'_mem _ _
    obtain ⟨y,hy,hE⟩ := twoSpectrumValues_physical k hk hp hd _ hm
    rw [← hE]
    exact hmin y hy

/-- Unconditional literal retained list for the canonical sixteen-level deformation. -/
def actualCandidateValues (k : Parameters ℝ) : Finset SixteenLevelField :=
  twoSpectrumValues (actualParameters k) (actualParameters_generic k).2.2

theorem actualCandidateValues_card_le_thirty (k : Parameters ℝ) : (actualCandidateValues k).card≤30 :=
  twoSpectrumValues_card_le_thirty _ _

theorem actualCandidateValues_nonempty (k : Parameters ℝ) : (actualCandidateValues k).Nonempty :=
  twoSpectrumValues_nonempty _ _

theorem actualCandidateValues_physical (k : Parameters ℝ) (v : SixteenLevelField)
    (hv : v ∈ actualCandidateValues k) :
    ∃ x : RealFields SixteenLevelField,mass x=1 ∧ quarticReal (actualParameters k) x=v :=
  twoSpectrumValues_physical _ (actualParameters_generic k).2.1 (actualParameters_generic k).1
    (actualParameters_generic k).2.2 v hv

theorem deformedMinimum_mem_actualCandidateValues (k : Parameters ℝ) :
    deformedMinimum k ∈ actualCandidateValues k :=
  normalized_minimum_mem_twoSpectrum _ (actualParameters_generic k).2.1 (actualParameters_generic k).1
    (actualParameters_generic k).2.2 (deformedMinimumPoint k)
    (deformedMinimumPoint_spec k).1 (deformedMinimumPoint_spec k).2

def actualCandidateMinimum (k : Parameters ℝ) : SixteenLevelField :=
  (actualCandidateValues k).min' (actualCandidateValues_nonempty k)

/-- The central finite-spectrum identity, with every genericity and coverage
condition discharged for arbitrary original fifteen real coefficients. -/
theorem actualCandidateMinimum_eq (k : Parameters ℝ) :
    actualCandidateMinimum k = deformedMinimum k :=
  twoSpectrumMinimum_eq _ (actualParameters_generic k).2.1 (actualParameters_generic k).1
    (actualParameters_generic k).2.2 (deformedMinimumPoint k)
    (deformedMinimumPoint_spec k).1 (deformedMinimumPoint_spec k).2

#print axioms actualCandidateValues_card_le_thirty
#print axioms actualCandidateValues_physical
#print axioms deformedMinimum_mem_actualCandidateValues
#print axioms actualCandidateMinimum_eq
end W3.OperatorField
