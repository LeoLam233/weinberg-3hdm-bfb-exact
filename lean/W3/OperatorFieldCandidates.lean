import W3.OperatorFieldGeneric
import W3.OperatorFieldInvariance
import W3.WeightedRepresentatives

/-! The literal finite two-spectrum list over any ordered real-closed field. -/
noncomputable section
namespace W3.OperatorField
open W3.TransferOperator W3.Elimination W3.RealModel W3.StrataTransfer W3.PrimalFieldBridge W3.Weighted
open ComplexPair
open scoped BigOperators
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]

def vectorOfPairs (z1 z2 z3 : ComplexPair K) : RealVector K :=
  ![z1.re,z1.im,z2.re,z2.im,z3.re,z3.im]

@[simp] lemma pairVector_vectorOfPairs (z1 z2 z3 : ComplexPair K) :
    pairVector (vectorOfPairs z1 z2 z3) = ![z1,z2,z3] := by
  funext i; fin_cases i <;> apply complexPair_ext <;> simp [pairVector,vectorOfPairs,zRe,zIm]

abbrev CandidateIndex (w : WeightedData K) :=
  {x : SpectrumPoint K // x ∈ spectrumCandidates w (canonicalMagnitudes w)}

def candidateIndices (w : WeightedData K) : Finset (CandidateIndex w) :=
  (spectrumCandidates w (canonicalMagnitudes w)).attach

def VectorRepresentation (w : WeightedData K) (x : SpectrumPoint K) (z : RealVector K) : Prop :=
  PointMatches x (pairVector z 0) (pairVector z 1) (pairVector z 2) ∧ zMass z = 1 ∧
    w.g1*normSq (pairVector z 0)+w.g2*normSq (pairVector z 1)+w.g3*normSq (pairVector z 2) ≠ 0 ∧
    ∃ lam : K, AmplitudeEquations (toSpectrum w) (pairVector z 0) (pairVector z 1) (pairVector z 2)
      w.g1 w.g2 w.g3 lam

lemma candidate_vector_exists (w : WeightedData K) (hex : completeWeightedExceptional w ≠ 0)
    (x : CandidateIndex w) : ∃ z : RealVector K, VectorRepresentation w x.val z := by
  obtain ⟨hp,he⟩ := mul_ne_zero_iff.mp hex
  have hg := (elementaryExceptional_properties w he).2.1
  obtain ⟨z1,z2,z3,lam,hm,hn,hG,hamp⟩ := spectrumCandidates_representable w (canonicalMagnitudes w)
    (fun i => (canonicalMagnitudes_spec w i).2) hp hg x.val x.property
  refine ⟨vectorOfPairs z1 z2 z3,?_,?_,?_,lam,?_⟩
  · simpa using hm
  · rw [← pairVector_norm_sum]; simpa using hn
  · simpa using hG
  · simpa using hamp

def candidateVector (w : WeightedData K) (hex : completeWeightedExceptional w ≠ 0)
    (x : CandidateIndex w) : RealVector K := Classical.choose (candidate_vector_exists w hex x)

lemma candidateVector_spec (w : WeightedData K) (hex : completeWeightedExceptional w ≠ 0)
    (x : CandidateIndex w) : VectorRepresentation w x.val (candidateVector w hex x) :=
  Classical.choose_spec (candidate_vector_exists w hex x)

def primalValues (k : Parameters K) : Finset K :=
  spectrumValues (originalPrimal k) (canonicalMagnitudes (originalPrimal k))

def DualRetained (k : Parameters K) (hd : completeWeightedExceptional (originalDual k) ≠ 0)
    (x : CandidateIndex (originalDual k)) : Prop :=
  let z := candidateVector _ hd x
  dualDen k z ≠ 0 ∧ dualPurity k z ≤ 1

def dualValues (k : Parameters K) (hd : completeWeightedExceptional (originalDual k) ≠ 0) : Finset K := by
  classical
  exact ((candidateIndices (originalDual k)).filter (DualRetained k hd)).image
    (fun x => dualEnergy k (candidateVector _ hd x))

def twoSpectrumValues (k : Parameters K) (hd : completeWeightedExceptional (originalDual k) ≠ 0) : Finset K := by
  classical
  exact primalValues k ∪ dualValues k hd

lemma primalValues_card (k : Parameters K) : (primalValues k).card ≤ 15 := spectrumValues_card_le_fifteen _ _
lemma dualValues_card (k : Parameters K) (hd : completeWeightedExceptional (originalDual k) ≠ 0) :
    (dualValues k hd).card ≤ 15 := by
  classical
  apply Finset.card_image_le.trans
  apply (Finset.card_filter_le _ _).trans
  simpa [candidateIndices] using spectrumCandidates_card_le_fifteen (originalDual k) (canonicalMagnitudes _)

lemma twoSpectrumValues_card_le_thirty (k : Parameters K) (hd : completeWeightedExceptional (originalDual k) ≠ 0) :
    (twoSpectrumValues k hd).card ≤ 30 := by
  classical
  exact (Finset.card_union_le _ _).trans (by
    have hp := primalValues_card k
    have hd := dualValues_card k hd
    omega)

lemma twoSpectrumValues_nonempty (k : Parameters K) (hd : completeWeightedExceptional (originalDual k) ≠ 0) :
    (twoSpectrumValues k hd).Nonempty := by
  classical
  obtain ⟨v,hv⟩ := spectrumValues_nonempty (originalPrimal k) (canonicalMagnitudes _) (by norm_num [originalPrimal])
  exact ⟨v,Finset.mem_union_left _ hv⟩

lemma pointMatches_primal_value (k : Parameters K) (x : SpectrumPoint K) (z : RealVector K)
    (hm : PointMatches x (pairVector z 0) (pairVector z 1) (pairVector z 2)) (hu : zMass z = 1) :
    spectrumValue (originalPrimal k) x = quarticReal k (neutralFields z) := by
  rw [pointMatches_value (originalPrimal k) x _ _ _ hm,← neutralFields_energy]
  have hn := (pairVector_norm_sum z).trans hu
  simpa only [originalPrimal,one_mul,hn,one_pow,div_one]

lemma pointMatches_dual_value (k : Parameters K) (x : SpectrumPoint K) (z : RealVector K)
    (hm : PointMatches x (pairVector z 0) (pairVector z 1) (pairVector z 2)) :
    spectrumValue (originalDual k) x = dualP k z/(dualA k z)^2 := by
  rw [pointMatches_value (originalDual k) x _ _ _ hm,dual_amplitude_energy,← dualA_eq_weight]

lemma primal_value_physical (k : Parameters K) (hp : completeWeightedExceptional (originalPrimal k) ≠ 0)
    (v : K) (hv : v ∈ primalValues k) :
    ∃ x : RealFields K,mass x=1 ∧ quarticReal k x=v := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
  let j : CandidateIndex (originalPrimal k) := ⟨q,hq⟩
  let z := candidateVector _ hp j
  have hs := candidateVector_spec _ hp j
  exact ⟨neutralFields z,(neutralFields_mass z).trans hs.2.1,
    (pointMatches_primal_value k q z hs.1 hs.2.1).symm⟩

lemma neutral_stratum_mem_primal (k : Parameters K) (hp : completeWeightedExceptional (originalPrimal k) ≠ 0)
    (x : RealFields K) (z : RealVector K) (hu : zMass z=1)
    (hG : gramCoordinates x=hermitianProjector z)
    (hE : ∀ i,actionRe (hermitianRe (hermitianOperator k (hermitianProjector z)))
      (hermitianIm (hermitianOperator k (hermitianProjector z))) z i=twiceQuartic k x*zRe z i ∧
      actionIm (hermitianRe (hermitianOperator k (hermitianProjector z)))
      (hermitianIm (hermitianOperator k (hermitianProjector z))) z i=twiceQuartic k x*zIm z i) :
    quarticReal k x ∈ primalValues k := by
  classical
  have hg := (projector_coordinates_iff x z).mpr hG
  have he' : ∀ i,actionRe (operatorRe k x) (operatorIm k x) z i=twiceQuartic k x*zRe z i ∧
      actionIm (operatorRe k x) (operatorIm k x) z i=twiceQuartic k x*zIm z i := by
    simpa only [← hG,hermitianRe_operator_gramCoordinates,hermitianIm_operator_gramCoordinates] using hE
  have hamp := neutral_stratum_amplitudes k x z hg he'
  obtain ⟨q,hq,hmatch⟩ := amplitude_matches_candidate (originalPrimal k) hp (canonicalMagnitudes _)
    (fun i => (canonicalMagnitudes_spec _ i).2) (pairVector z 0) (pairVector z 1) (pairVector z 2)
    (twiceQuartic k x) ((pairVector_norm_sum z).trans hu) hamp
  apply Finset.mem_image.mpr
  refine ⟨q,hq,?_⟩
  rw [pointMatches_primal_value k q z hmatch hu,neutralFields_energy,← neutral_stratum_energy k x z hg]

lemma charged_stratum_mem_dual (k : Parameters K) (hk : originalInverseDen k ≠ 0)
    (hd : completeWeightedExceptional (originalDual k) ≠ 0)
    (y : HermitianCoordinates K) (z : RealVector K) (lam mu : K)
    (hu : zMass z=1) (ht : hermitianTrace y=1) (hz : actionLinear z y=0)
    (hn : hermitianOperator k y=lam • hermitianIdentity+mu • hermitianProjector z)
    (hchi : hermitianPurity y≤1) : hermitianEnergy k y/2 ∈ dualValues k hd := by
  classical
  obtain ⟨ha,hD,hy,hamp,henergy⟩ := generic_charged_stratum k hk hd y z lam mu hu ht hz hn
  obtain ⟨q,hq,hmatch⟩ := amplitude_matches_candidate (originalDual k) hd (canonicalMagnitudes _)
    (fun i => (canonicalMagnitudes_spec _ i).2) (pairVector z 0) (pairVector z 1) (pairVector z 2)
    (2*(dualP k z/dualA k z)) ((pairVector_norm_sum z).trans hu) hamp
  let j : CandidateIndex (originalDual k) := ⟨q,hq⟩
  let w := candidateVector _ hd j
  have hw := candidateVector_spec _ hd j
  obtain ⟨_,_,hDeq,hchieq,hEeq⟩ := matched_dual_scalars_invariant k q z w hmatch hw.1
  apply Finset.mem_image.mpr
  refine ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_attach _ j,?_,?_⟩,?_⟩
  · change dualDen k w ≠ 0
    rwa [← hDeq]
  · change dualPurity k w≤1
    rw [← hchieq]
    simpa only [dualPurity,← hy] using hchi
  · exact hEeq.symm.trans henergy.symm

end W3.OperatorField
