import W3.OperatorFieldTwoSpectrum
import W3.TransferOperatorResidue

/-! The actual finite retained matrix list, with exact value projection and physical witnesses. -/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace W3.TransferOperator
open W3.RealModel W3.StrataTransfer W3.PrimalFieldBridge W3.Infinitesimal
open W3.OperatorField W3.Elimination W3.Weighted

abbrev Matrix16 := HermitianCoordinates SixteenLevelField

def primalMatrices (k : Parameters SixteenLevelField)
    (hp : completeWeightedExceptional (originalPrimal k) ≠ 0) : Finset Matrix16 := by
  classical
  exact (candidateIndices (originalPrimal k)).image (fun q=>hermitianProjector (candidateVector _ hp q))

def dualMatrices (k : Parameters SixteenLevelField)
    (hd : completeWeightedExceptional (originalDual k) ≠ 0) : Finset Matrix16 := by
  classical
  exact ((candidateIndices (originalDual k)).filter (DualRetained k hd)).image
    (fun q=>dualCoordinates k (candidateVector _ hd q))

def retainedMatrices (k : Parameters SixteenLevelField)
    (hp : completeWeightedExceptional (originalPrimal k) ≠ 0)
    (hd : completeWeightedExceptional (originalDual k) ≠ 0) : Finset Matrix16 := by
  classical
  exact primalMatrices k hp ∪ dualMatrices k hd

lemma primal_matrix_energy (k : Parameters SixteenLevelField)
    (hp : completeWeightedExceptional (originalPrimal k) ≠ 0) (q : CandidateIndex (originalPrimal k)) :
    hermitianEnergy k (hermitianProjector (candidateVector _ hp q))/2=
      spectrumValue (originalPrimal k) q.val := by
  have hs := candidateVector_spec _ hp q
  rw [projector_eq_neutral_gram,hermitianEnergy_gramCoordinates]
  exact (pointMatches_primal_value k q.val _ hs.1 hs.2.1).symm

lemma primal_matrix_physical (k : Parameters SixteenLevelField)
    (hp : completeWeightedExceptional (originalPrimal k) ≠ 0) (q : CandidateIndex (originalPrimal k)) :
    ∃ x : RealFields SixteenLevelField,mass x=1 ∧
      GramMatches x (hermitianProjector (candidateVector _ hp q)) := by
  have hs := candidateVector_spec _ hp q
  exact ⟨neutralFields (candidateVector _ hp q),(neutralFields_mass _).trans hs.2.1,
    (gramMatches_iff _ _).mpr (projector_eq_neutral_gram _).symm⟩

lemma dual_matrix_physical_value (k : Parameters SixteenLevelField) (hk : originalInverseDen k ≠ 0)
    (hd : completeWeightedExceptional (originalDual k) ≠ 0)
    (q : CandidateIndex (originalDual k)) (hq : DualRetained k hd q) :
    (∃ x : RealFields SixteenLevelField,mass x=1 ∧ GramMatches x (dualCoordinates k (candidateVector _ hd q))) ∧
      hermitianEnergy k (dualCoordinates k (candidateVector _ hd q))/2=dualEnergy k (candidateVector _ hd q) := by
  obtain ⟨hD,hchi⟩ := hq
  have hs := candidateVector_spec _ hd q
  obtain ⟨lam,hamp⟩ := hs.2.2.2
  obtain ⟨x,hx,hG,hE⟩ := dual_candidate_physical k hk _ lam hs.2.1 hamp hD hchi
  have hg := (gramMatches_iff x _).mpr hG
  refine ⟨⟨x,hx,hg⟩,?_⟩
  rw [← gramMatches_energy k hg]
  exact hE

theorem retainedMatrices_card_le_thirty (k : Parameters SixteenLevelField)
    (hp : completeWeightedExceptional (originalPrimal k) ≠ 0)
    (hd : completeWeightedExceptional (originalDual k) ≠ 0) :
    (retainedMatrices k hp hd).card≤30 := by
  classical
  have hpr : (primalMatrices k hp).card≤15 := by
    apply Finset.card_image_le.trans
    simpa [candidateIndices] using spectrumCandidates_card_le_fifteen (originalPrimal k) (canonicalMagnitudes _)
  have hdu : (dualMatrices k hd).card≤15 := by
    apply Finset.card_image_le.trans
    apply (Finset.card_filter_le _ _).trans
    simpa [candidateIndices] using spectrumCandidates_card_le_fifteen (originalDual k) (canonicalMagnitudes _)
  exact (Finset.card_union_le _ _).trans (by omega)

theorem retainedMatrices_physical (k : Parameters SixteenLevelField) (hk : originalInverseDen k ≠ 0)
    (hp : completeWeightedExceptional (originalPrimal k) ≠ 0)
    (hd : completeWeightedExceptional (originalDual k) ≠ 0)
    (y : Matrix16) (hy : y ∈ retainedMatrices k hp hd) :
    ∃ x : RealFields SixteenLevelField,mass x=1 ∧ GramMatches x y := by
  classical
  rcases Finset.mem_union.mp hy with hy | hy
  · obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hy
    exact primal_matrix_physical k hp q
  · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hy
    exact (dual_matrix_physical_value k hk hd q (Finset.mem_filter.mp hq).2).1

theorem retainedMatrix_value_mem (k : Parameters SixteenLevelField) (hk : originalInverseDen k ≠ 0)
    (hp : completeWeightedExceptional (originalPrimal k) ≠ 0)
    (hd : completeWeightedExceptional (originalDual k) ≠ 0)
    (y : Matrix16) (hy : y ∈ retainedMatrices k hp hd) :
    hermitianEnergy k y/2 ∈ twoSpectrumValues k hd := by
  classical
  rcases Finset.mem_union.mp hy with hy | hy
  · obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hy
    apply Finset.mem_union_left
    rw [primal_matrix_energy]
    exact Finset.mem_image.mpr ⟨q.val,q.property,rfl⟩
  · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hy
    apply Finset.mem_union_right
    rw [(dual_matrix_physical_value k hk hd q (Finset.mem_filter.mp hq).2).2]
    exact Finset.mem_image.mpr ⟨q,hq,rfl⟩

theorem value_has_retainedMatrix (k : Parameters SixteenLevelField) (hk : originalInverseDen k ≠ 0)
    (hp : completeWeightedExceptional (originalPrimal k) ≠ 0)
    (hd : completeWeightedExceptional (originalDual k) ≠ 0)
    (v : SixteenLevelField) (hv : v ∈ twoSpectrumValues k hd) :
    ∃ y ∈ retainedMatrices k hp hd,hermitianEnergy k y/2=v := by
  classical
  rcases Finset.mem_union.mp hv with hv | hv
  · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
    let j : CandidateIndex (originalPrimal k) := ⟨q,hq⟩
    refine ⟨hermitianProjector (candidateVector _ hp j),Finset.mem_union_left _ ?_,?_⟩
    · exact Finset.mem_image.mpr ⟨j,Finset.mem_attach _ j,rfl⟩
    · exact primal_matrix_energy k hp j
  · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
    refine ⟨dualCoordinates k (candidateVector _ hd q),Finset.mem_union_right _ ?_,?_⟩
    · exact Finset.mem_image.mpr ⟨q,hq,rfl⟩
    · exact (dual_matrix_physical_value k hk hd q (Finset.mem_filter.mp hq).2).2

/-- The literal retained matrices have exactly the previously proved finite-spectrum values. -/
theorem retainedMatrices_values (k : Parameters SixteenLevelField) (hk : originalInverseDen k ≠ 0)
    (hp : completeWeightedExceptional (originalPrimal k) ≠ 0)
    (hd : completeWeightedExceptional (originalDual k) ≠ 0) :
    (retainedMatrices k hp hd).image (fun y=>hermitianEnergy k y/2)=twoSpectrumValues k hd := by
  classical
  ext v
  constructor
  · rintro h
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp h
    exact retainedMatrix_value_mem k hk hp hd y hy
  · intro hv
    obtain ⟨y,hy,hE⟩ := value_has_retainedMatrix k hk hp hd v hv
    exact Finset.mem_image.mpr ⟨y,hy,hE⟩

def actualRetainedMatrices (k : Parameters ℝ) : Finset Matrix16 :=
  retainedMatrices (actualParameters k) (actualParameters_generic k).1 (actualParameters_generic k).2.2

theorem actualRetainedMatrices_card_le_thirty (k : Parameters ℝ) : (actualRetainedMatrices k).card≤30 :=
  retainedMatrices_card_le_thirty _ _ _

theorem actualRetainedMatrices_physical (k : Parameters ℝ) (y : Matrix16) (hy : y ∈ actualRetainedMatrices k) :
    ∃ x : RealFields SixteenLevelField,mass x=1 ∧ GramMatches x y :=
  retainedMatrices_physical _ (actualParameters_generic k).2.1 _ _ y hy

theorem actualRetainedMatrices_values (k : Parameters ℝ) :
    (actualRetainedMatrices k).image (fun y=>hermitianEnergy (actualParameters k) y/2)=actualCandidateValues k :=
  retainedMatrices_values _ (actualParameters_generic k).2.1 _ _

theorem actualMinimum_has_retainedMatrix (k : Parameters ℝ) :
    ∃ y ∈ actualRetainedMatrices k,hermitianEnergy (actualParameters k) y/2=deformedMinimum k :=
  value_has_retainedMatrix _ (actualParameters_generic k).2.1 _ _ _
    (deformedMinimum_mem_actualCandidateValues k)

theorem actualRetainedMatrices_nonempty (k : Parameters ℝ) : (actualRetainedMatrices k).Nonempty := by
  obtain ⟨y,hy,_⟩ := actualMinimum_has_retainedMatrix k
  exact ⟨y,hy⟩

theorem actualRetainedMatrices_bounded (k : Parameters ℝ) (y : Matrix16) (hy : y ∈ actualRetainedMatrices k) :
    MatrixBounded y := by
  obtain ⟨x,hx,hG⟩ := actualRetainedMatrices_physical k y hy
  exact gramMatches_bounded hx hG

/-- Every minimizing retained matrix, not merely a selected one, has the exact real Gram residue. -/
theorem actualRetainedMatrix_minimizing_residue (k : Parameters ℝ) (y : Matrix16)
    (hy : y ∈ actualRetainedMatrices k)
    (hv : hermitianEnergy (actualParameters k) y/2=actualCandidateMinimum k) :
    let hb := actualRetainedMatrices_bounded k y hy
    hermitianTrace (residueMatrix9 y hb)=1 ∧
      hermitianEnergy k (residueMatrix9 y hb)/2=realMinimum k ∧
      ∃ phi : W3.Fields, ‖phi‖=1 ∧
        complexMatrix (hermitianRe (residueMatrix9 y hb)) (hermitianIm (residueMatrix9 y hb))=W3.gram phi ∧
        W3.quartic (couplings k) phi=realMinimum k := by
  rw [actualCandidateMinimum_eq] at hv
  exact minimizing_matrix_residue k y _ (actualRetainedMatrices_physical k y hy) hv

#print axioms actualRetainedMatrices_values
#print axioms actualMinimum_has_retainedMatrix
#print axioms actualRetainedMatrix_minimizing_residue
end W3.TransferOperator
