import W3.OperatorCorrespondence
import W3.OperatorRealization
import W3.OperatorMinimum
import W3.WeightedRepresentatives
import W3.InfinitesimalRealClosedReal

/-! The concrete real two-spectrum criterion. All candidates are the actual
finite singleton/pair/sextic points; dual filtering uses their reconstructed matrices. -/
noncomputable section
namespace W3.Operator
open Matrix ComplexConjugate
open W3.Weighted W3.Elimination
open scoped BigOperators ComplexOrder

lemma normSq_complexOfPair (z : ComplexPair ℝ) : Complex.normSq (complexOfPair z) = z.normSq := by
  rw [← normSq_ofComplex,ofComplex_complexOfPair]

abbrev CandidateIndex (w : WeightedData ℝ) :=
  {x : SpectrumPoint ℝ // x ∈ spectrumCandidates w (canonicalMagnitudes w)}

def candidateIndices (w : WeightedData ℝ) : Finset (CandidateIndex w) :=
  (spectrumCandidates w (canonicalMagnitudes w)).attach

def VectorRepresentation (w : WeightedData ℝ) (x : SpectrumPoint ℝ) (z : Fin 3 → ℂ) : Prop :=
  VectorMatches x z ∧ (∑ i, Complex.normSq (z i)) = 1 ∧
    w.g1*Complex.normSq (z 0)+w.g2*Complex.normSq (z 1)+w.g3*Complex.normSq (z 2) ≠ 0 ∧
    ∃ lam : ℝ, AmplitudeEquations (toSpectrum w) (ofComplex (z 0)) (ofComplex (z 1)) (ofComplex (z 2))
      w.g1 w.g2 w.g3 lam

lemma candidate_vector_exists (w : WeightedData ℝ) (hex : completeWeightedExceptional w ≠ 0)
    (x : CandidateIndex w) : ∃ z : Fin 3 → ℂ, VectorRepresentation w x.val z := by
  obtain ⟨hp,he⟩ := mul_ne_zero_iff.mp hex
  have hg := (elementaryExceptional_properties w he).2.1
  obtain ⟨z₁,z₂,z₃,lam,hm,hn,hG,hamp⟩ := spectrumCandidates_representable w (canonicalMagnitudes w)
    (fun i => (canonicalMagnitudes_spec w i).2) hp hg x.val x.property
  refine ⟨![complexOfPair z₁,complexOfPair z₂,complexOfPair z₃],?_,?_,?_,lam,?_⟩
  · simpa [VectorMatches] using hm
  · simpa [Fin.sum_univ_three,normSq_complexOfPair] using hn
  · simpa [normSq_complexOfPair] using hG
  · simpa using hamp

def candidateVector (w : WeightedData ℝ) (hex : completeWeightedExceptional w ≠ 0)
    (x : CandidateIndex w) : Fin 3 → ℂ := Classical.choose (candidate_vector_exists w hex x)

lemma candidateVector_spec (w : WeightedData ℝ) (hex : completeWeightedExceptional w ≠ 0)
    (x : CandidateIndex w) : VectorRepresentation w x.val (candidateVector w hex x) :=
  Classical.choose_spec (candidate_vector_exists w hex x)

def primalValues (κ : W3.Couplings) : Finset ℝ :=
  spectrumValues (operatorPrimalData κ) (canonicalMagnitudes (operatorPrimalData κ))

def dualChosenEnergy (κ : W3.Couplings)
    (hA : (couplingMatrix κ).det ≠ 0) (hΔ : ∀ i, blockDet (κ.c i) (κ.d i) ≠ 0)
    (hex : completeWeightedExceptional (operatorDualData (couplingMatrix κ) κ.c κ.d) ≠ 0)
    (x : CandidateIndex (operatorDualData (couplingMatrix κ) κ.c κ.d)) : ℝ :=
  let R := (couplingEquiv κ hA hΔ).symm
  let z := candidateVector _ hex x
  dualP R z / (2 * denominator (dualBeta R) (dualA R z) (dualP R z))

def DualRetained (κ : W3.Couplings)
    (hA : (couplingMatrix κ).det ≠ 0) (hΔ : ∀ i, blockDet (κ.c i) (κ.d i) ≠ 0)
    (hex : completeWeightedExceptional (operatorDualData (couplingMatrix κ) κ.c κ.d) ≠ 0)
    (x : CandidateIndex (operatorDualData (couplingMatrix κ) κ.c κ.d)) : Prop :=
  let R := (couplingEquiv κ hA hΔ).symm
  let z := candidateVector _ hex x
  denominator (dualBeta R) (dualA R z) (dualP R z) ≠ 0 ∧ dualPurity R z ≤ 1

def dualValues (κ : W3.Couplings)
    (hA : (couplingMatrix κ).det ≠ 0) (hΔ : ∀ i, blockDet (κ.c i) (κ.d i) ≠ 0)
    (hex : completeWeightedExceptional (operatorDualData (couplingMatrix κ) κ.c κ.d) ≠ 0) : Finset ℝ := by
  classical
  exact ((candidateIndices (operatorDualData (couplingMatrix κ) κ.c κ.d)).filter
    (DualRetained κ hA hΔ hex)).image (dualChosenEnergy κ hA hΔ hex)

def twoSpectrumValues (κ : W3.Couplings)
    (hA : (couplingMatrix κ).det ≠ 0) (hΔ : ∀ i, blockDet (κ.c i) (κ.d i) ≠ 0)
    (hex : completeWeightedExceptional (operatorDualData (couplingMatrix κ) κ.c κ.d) ≠ 0) : Finset ℝ := by
  classical
  exact primalValues κ ∪ dualValues κ hA hΔ hex

lemma primalValues_card (κ : W3.Couplings) : (primalValues κ).card ≤ 15 :=
  spectrumValues_card_le_fifteen _ _

lemma dualValues_card (κ : W3.Couplings)
    (hA : (couplingMatrix κ).det ≠ 0) (hΔ : ∀ i, blockDet (κ.c i) (κ.d i) ≠ 0)
    (hex : completeWeightedExceptional (operatorDualData (couplingMatrix κ) κ.c κ.d) ≠ 0) :
    (dualValues κ hA hΔ hex).card ≤ 15 := by
  classical
  apply Finset.card_image_le.trans
  apply (Finset.card_filter_le _ _).trans
  simpa [candidateIndices] using spectrumCandidates_card_le_fifteen
    (operatorDualData (couplingMatrix κ) κ.c κ.d) (canonicalMagnitudes _)

lemma twoSpectrumValues_card_le_thirty (κ : W3.Couplings)
    (hA : (couplingMatrix κ).det ≠ 0) (hΔ : ∀ i, blockDet (κ.c i) (κ.d i) ≠ 0)
    (hex : completeWeightedExceptional (operatorDualData (couplingMatrix κ) κ.c κ.d) ≠ 0) :
    (twoSpectrumValues κ hA hΔ hex).card ≤ 30 := by
  classical
  exact (Finset.card_union_le _ _).trans (by
    have hp := primalValues_card κ
    have hd := dualValues_card κ hA hΔ hex
    omega)

lemma twoSpectrumValues_nonempty (κ : W3.Couplings)
    (hA : (couplingMatrix κ).det ≠ 0) (hΔ : ∀ i, blockDet (κ.c i) (κ.d i) ≠ 0)
    (hex : completeWeightedExceptional (operatorDualData (couplingMatrix κ) κ.c κ.d) ≠ 0) :
    (twoSpectrumValues κ hA hΔ hex).Nonempty := by
  classical
  obtain ⟨v,hv⟩ := spectrumValues_nonempty (operatorPrimalData κ) (canonicalMagnitudes _) (by norm_num [operatorPrimalData,weightedDataOf])
  exact ⟨v,Finset.mem_union_left _ hv⟩

lemma primal_value_physical (κ : W3.Couplings)
    (hex : completeWeightedExceptional (operatorPrimalData κ) ≠ 0) (v : ℝ) (hv : v ∈ primalValues κ) :
    ∃ φ : W3.Fields, ‖φ‖ = 1 ∧ W3.quartic κ φ = v := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
  let i : CandidateIndex (operatorPrimalData κ) := ⟨x,hx⟩
  let z := candidateVector _ hex i
  have hs := candidateVector_spec _ hex i
  refine ⟨projectorFields z,projectorFields_normalized z hs.2.1,?_⟩
  rw [quartic_eq_coordinateEnergy,projectorFields_coordinates]
  exact (vectorMatches_primal_value κ x z hs.1 hs.2.1).symm

lemma dual_value_physical (κ : W3.Couplings)
    (hA : (couplingMatrix κ).det ≠ 0) (hΔ : ∀ i, blockDet (κ.c i) (κ.d i) ≠ 0)
    (hex : completeWeightedExceptional (operatorDualData (couplingMatrix κ) κ.c κ.d) ≠ 0)
    (v : ℝ) (hv : v ∈ dualValues κ hA hΔ hex) :
    ∃ φ : W3.Fields, ‖φ‖ = 1 ∧ W3.quartic κ φ = v := by
  classical
  obtain ⟨x,hfilter,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨hD,hchi⟩ := (Finset.mem_filter.mp hfilter).2
  have hs := candidateVector_spec _ hex x
  obtain ⟨lam,hamp⟩ := hs.2.2.2
  have hamp' : AmplitudeEquations (dualSpectrum (couplingMatrix κ) κ.c κ.d)
      (ofComplex (candidateVector _ hex x 0)) (ofComplex (candidateVector _ hex x 1))
      (ofComplex (candidateVector _ hex x 2))
      (dualWeights (couplingMatrix κ) 0) (dualWeights (couplingMatrix κ) 1)
      (dualWeights (couplingMatrix κ) 2) lam := by
    rw [show toSpectrum (operatorDualData (couplingMatrix κ) κ.c κ.d) =
      dualSpectrum (couplingMatrix κ) κ.c κ.d from toSpectrum_weightedDataOf _ _] at hamp
    exact hamp
  have hstat := dual_amplitudes_imply_kernel (couplingMatrix κ) κ.c κ.d (candidateVector _ hex x)
    hA hΔ (couplingMatrix_isSymm κ) lam hamp'
  obtain ⟨φ,hφ,hX,hE⟩ := dual_candidate_physical_witness κ hA hΔ (candidateVector _ hex x) hs.2.1 hD hstat hchi
  exact ⟨φ,hφ,hE⟩

theorem twoSpectrumValues_physical (κ : W3.Couplings)
    (hA : (couplingMatrix κ).det ≠ 0) (hΔ : ∀ i, blockDet (κ.c i) (κ.d i) ≠ 0)
    (hp : completeWeightedExceptional (operatorPrimalData κ) ≠ 0)
    (hd : completeWeightedExceptional (operatorDualData (couplingMatrix κ) κ.c κ.d) ≠ 0)
    (v : ℝ) (hv : v ∈ twoSpectrumValues κ hA hΔ hd) :
    ∃ φ : W3.Fields, ‖φ‖ = 1 ∧ W3.quartic κ φ = v := by
  classical
  rcases Finset.mem_union.mp hv with h | h
  · exact primal_value_physical κ hp v h
  · exact dual_value_physical κ hA hΔ hd v h

lemma minimum_rank_one_mem_primal (κ : W3.Couplings)
    (hp : completeWeightedExceptional (operatorPrimalData κ) ≠ 0)
    (φ : W3.Fields) (hφ : ‖φ‖ = 1)
    (hmin : ∀ ψ : W3.Fields, ‖ψ‖ = 1 → W3.quartic κ φ ≤ W3.quartic κ ψ)
    (hrank : (W3.gram φ).rank = 1) : W3.quartic κ φ ∈ primalValues κ := by
  classical
  obtain ⟨z,hunit,hgram,heigen⟩ := normalized_minimum_rank_one κ φ hφ hmin hrank
  have hcoords : fieldCoordinates φ = projectorCoordinates z := by
    apply coordinateMatrix_injective
    rw [coordinateMatrix_fieldCoordinates,coordinateMatrix_projector,hgram]
  rw [hcoords] at heigen
  have hamp := structured_eigen_implies_amplitudes (couplingMatrix κ) κ.c κ.d z
    (fun _ => 1) (2*W3.quartic κ φ) (by rfl) (by rfl) (by rfl) (by
      funext i
      have h := congrFun heigen i
      simpa only [couplingOperator,Pi.smul_apply,Complex.real_smul,mul_one] using h)
  have hn : (ofComplex (z 0)).normSq+(ofComplex (z 1)).normSq+(ofComplex (z 2)).normSq = 1 := by
    simpa [Fin.sum_univ_three] using hunit
  have hamp' : AmplitudeEquations (toSpectrum (operatorPrimalData κ))
      (ofComplex (z 0)) (ofComplex (z 1)) (ofComplex (z 2))
      (operatorPrimalData κ).g1 (operatorPrimalData κ).g2 (operatorPrimalData κ).g3
      (2*W3.quartic κ φ) := by
    rw [show toSpectrum (operatorPrimalData κ) = structuredSpectrum (couplingMatrix κ) κ.c κ.d from toSpectrum_weightedDataOf _ _]
    exact hamp
  obtain ⟨x,hx,hm⟩ := amplitude_matches_candidate (operatorPrimalData κ) hp (canonicalMagnitudes _)
    (fun i => (canonicalMagnitudes_spec _ i).2) _ _ _ _ hn hamp'
  apply Finset.mem_image.mpr
  refine ⟨x,hx,?_⟩
  rw [vectorMatches_primal_value κ x z hm hunit,quartic_eq_coordinateEnergy,hcoords]

lemma minimum_rank_two_mem_dual (κ : W3.Couplings)
    (hA : (couplingMatrix κ).det ≠ 0) (hΔ : ∀ i, blockDet (κ.c i) (κ.d i) ≠ 0)
    (hd : completeWeightedExceptional (operatorDualData (couplingMatrix κ) κ.c κ.d) ≠ 0)
    (φ : W3.Fields) (hφ : ‖φ‖ = 1)
    (hmin : ∀ ψ : W3.Fields, ‖ψ‖ = 1 → W3.quartic κ φ ≤ W3.quartic κ ψ)
    (hrank : (W3.gram φ).rank = 2) : W3.quartic κ φ ∈ dualValues κ hA hΔ hd := by
  classical
  obtain ⟨z,hunit,ha,hD,hrec,hstat,hchi,hE⟩ :=
    generic_minimum_rank_two_candidate κ hA hΔ hd φ hφ hmin hrank
  let R := (couplingEquiv κ hA hΔ).symm
  have hamp := inverse_kernel_implies_amplitudes (couplingMatrix κ) κ.c κ.d z
    (dualA R z) (dualP R z) ha (couplingMatrix_isSymm κ) hstat
  have hn : (ofComplex (z 0)).normSq+(ofComplex (z 1)).normSq+(ofComplex (z 2)).normSq = 1 := by
    simpa [Fin.sum_univ_three] using hunit
  have hamp' : AmplitudeEquations (toSpectrum (operatorDualData (couplingMatrix κ) κ.c κ.d))
      (ofComplex (z 0)) (ofComplex (z 1)) (ofComplex (z 2))
      (operatorDualData (couplingMatrix κ) κ.c κ.d).g1
      (operatorDualData (couplingMatrix κ) κ.c κ.d).g2
      (operatorDualData (couplingMatrix κ) κ.c κ.d).g3 (2*(dualP R z/dualA R z)) := by
    rw [show toSpectrum (operatorDualData (couplingMatrix κ) κ.c κ.d) = dualSpectrum (couplingMatrix κ) κ.c κ.d from toSpectrum_weightedDataOf _ _]
    exact hamp
  obtain ⟨x,hx,hm⟩ := amplitude_matches_candidate (operatorDualData (couplingMatrix κ) κ.c κ.d) hd
    (canonicalMagnitudes _) (fun i => (canonicalMagnitudes_spec _ i).2) _ _ _ _ hn hamp'
  let i : CandidateIndex (operatorDualData (couplingMatrix κ) κ.c κ.d) := ⟨x,hx⟩
  let y := candidateVector _ hd i
  have hy := candidateVector_spec _ hd i
  obtain ⟨haeq,hpeq,hchieq⟩ := dual_scalars_invariant (couplingMatrix κ) κ.c κ.d hA hΔ z y
    (vectorMatches_quadratic_eq x z y hm hy.1)
  change dualA R z = dualA R y at haeq
  change dualP R z = dualP R y at hpeq
  change dualPurity R z = dualPurity R y at hchieq
  have hret : DualRetained κ hA hΔ hd i := by
    constructor
    · change denominator (dualBeta R) (dualA R y) (dualP R y) ≠ 0
      rw [← haeq,← hpeq]
      exact hD
    · change dualPurity R y ≤ 1
      rw [← hchieq]
      exact hchi
  apply Finset.mem_image.mpr
  refine ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_attach _ _,hret⟩,?_⟩
  change dualP R y/(2*denominator (dualBeta R) (dualA R y) (dualP R y)) = W3.quartic κ φ
  rw [← haeq,← hpeq]
  exact hE.symm

/-- Every actual global normalized minimum occurs in the explicit retained
finite list. This theorem has no assumed stationarity or coverage premise. -/
theorem normalized_minimum_mem_twoSpectrum (κ : W3.Couplings)
    (hA : (couplingMatrix κ).det ≠ 0) (hΔ : ∀ i, blockDet (κ.c i) (κ.d i) ≠ 0)
    (hp : completeWeightedExceptional (operatorPrimalData κ) ≠ 0)
    (hd : completeWeightedExceptional (operatorDualData (couplingMatrix κ) κ.c κ.d) ≠ 0)
    (φ : W3.Fields) (hφ : ‖φ‖ = 1)
    (hmin : ∀ ψ : W3.Fields, ‖ψ‖ = 1 → W3.quartic κ φ ≤ W3.quartic κ ψ) :
    W3.quartic κ φ ∈ twoSpectrumValues κ hA hΔ hd := by
  classical
  rcases normalized_gram_rank_cases φ hφ with h1 | h2
  · exact Finset.mem_union_left _ (minimum_rank_one_mem_primal κ hp φ hφ hmin h1)
  · exact Finset.mem_union_right _ (minimum_rank_two_mem_dual κ hA hΔ hd φ hφ hmin h2)

def twoSpectrumMinimum (κ : W3.Couplings)
    (hA : (couplingMatrix κ).det ≠ 0) (hΔ : ∀ i, blockDet (κ.c i) (κ.d i) ≠ 0)
    (hd : completeWeightedExceptional (operatorDualData (couplingMatrix κ) κ.c κ.d) ≠ 0) : ℝ :=
  (twoSpectrumValues κ hA hΔ hd).min' (twoSpectrumValues_nonempty κ hA hΔ hd)

/-- Exact equality of the physical minimum and the at-most-thirty retained
values, for every real input satisfying the explicit proper-polynomial exclusions. -/
theorem twoSpectrumMinimum_eq (κ : W3.Couplings)
    (hA : (couplingMatrix κ).det ≠ 0) (hΔ : ∀ i, blockDet (κ.c i) (κ.d i) ≠ 0)
    (hp : completeWeightedExceptional (operatorPrimalData κ) ≠ 0)
    (hd : completeWeightedExceptional (operatorDualData (couplingMatrix κ) κ.c κ.d) ≠ 0)
    (φ : W3.Fields) (hφ : ‖φ‖ = 1)
    (hmin : ∀ ψ : W3.Fields, ‖ψ‖ = 1 → W3.quartic κ φ ≤ W3.quartic κ ψ) :
    twoSpectrumMinimum κ hA hΔ hd = W3.quartic κ φ := by
  apply le_antisymm
  · exact Finset.min'_le _ _ (normalized_minimum_mem_twoSpectrum κ hA hΔ hp hd φ hφ hmin)
  · obtain ⟨ψ,hψ,hE⟩ := twoSpectrumValues_physical κ hA hΔ hp hd _
      (Finset.min'_mem _ (twoSpectrumValues_nonempty κ hA hΔ hd))
    change W3.quartic κ φ ≤ (twoSpectrumValues κ hA hΔ hd).min' _
    rw [← hE]
    exact hmin ψ hψ

/-- Both weak and strict BFB follow from the same explicit generic two-spectrum minimum. -/
theorem generic_twoSpectrum_stability (κ : W3.Couplings)
    (hA : (couplingMatrix κ).det ≠ 0) (hΔ : ∀ i, blockDet (κ.c i) (κ.d i) ≠ 0)
    (hp : completeWeightedExceptional (operatorPrimalData κ) ≠ 0)
    (hd : completeWeightedExceptional (operatorDualData (couplingMatrix κ) κ.c κ.d) ≠ 0) :
    ((∀ φ : W3.Fields, 0 ≤ W3.quartic κ φ) ↔ 0 ≤ twoSpectrumMinimum κ hA hΔ hd) ∧
    ((∀ φ : W3.Fields, φ ≠ 0 → 0 < W3.quartic κ φ) ↔ 0 < twoSpectrumMinimum κ hA hΔ hd) := by
  obtain ⟨φ,hφ,hmin,hweak,hstrict⟩ := W3.exists_minimum_with_stability κ
  rw [twoSpectrumMinimum_eq κ hA hΔ hp hd φ hφ hmin]
  exact ⟨hweak,hstrict⟩

#print axioms twoSpectrumValues_physical
#print axioms twoSpectrumValues_card_le_thirty
#print axioms normalized_minimum_mem_twoSpectrum
#print axioms twoSpectrumMinimum_eq
#print axioms generic_twoSpectrum_stability
end W3.Operator
