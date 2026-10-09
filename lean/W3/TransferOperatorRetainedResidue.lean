import W3.TransferOperatorRetained
import W3.WeightedAlgebraicityCanonical

/-! Unconditional finite successive residues of the literal retained matrices. -/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace W3.TransferOperator
open W3.RealModel W3.StrataTransfer W3.Infinitesimal W3.OperatorField W3.Elimination W3.Weighted

/-- Algebraicity is derived from the actual sextic/pair/vertex selections and explicit inverse map. -/
theorem actualRetainedMatrices_algebraic (k : Parameters ℝ) (y : Matrix16)
    (hy : y ∈ actualRetainedMatrices k) :
    letI := rationalTowerAlgebra 16
    ∀ i,IsAlgebraic (RationalTower 16) (y i) := by
  letI := rationalTowerAlgebra 16
  classical
  rcases Finset.mem_union.mp hy with hp | hd
  · obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hp
    exact actual_primal_candidate_algebraic k _ q
  · obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hd
    exact (actual_dual_candidate_algebraic k _ q).1

/-- Every retained matrix has a genuine sequence of sixteen preceding-field residues. -/
theorem actualRetainedMatrix_successive_residue (k : Parameters ℝ) (y : Matrix16)
    (hy : y ∈ actualRetainedMatrices k) :
    let hb := actualRetainedMatrices_bounded k y hy
    ∀ i,SuccessiveResidue 16 (y i) (residueMatrix9 y hb i) :=
  matrix_successiveResidue y (actualRetainedMatrices_bounded k y hy)
    (actualRetainedMatrices_algebraic k y hy)

/-- Every minimizing retained matrix yields the exact original physical minimum.
All genericity, algebraicity, boundedness, transfer, and compatibility conditions are discharged. -/
theorem actualRetainedMatrix_minimizing_successive_residue (k : Parameters ℝ) (y : Matrix16)
    (hy : y ∈ actualRetainedMatrices k)
    (hv : hermitianEnergy (actualParameters k) y/2=actualCandidateMinimum k) :
    let hb := actualRetainedMatrices_bounded k y hy
    (∀ i,SuccessiveResidue 16 (y i) (residueMatrix9 y hb i)) ∧
      hermitianTrace (residueMatrix9 y hb)=1 ∧
      hermitianEnergy k (residueMatrix9 y hb)/2=realMinimum k ∧
      ∃ phi : W3.Fields, ‖phi‖=1 ∧
        complexMatrix (hermitianRe (residueMatrix9 y hb)) (hermitianIm (residueMatrix9 y hb))=W3.gram phi ∧
        W3.quartic (couplings k) phi=realMinimum k :=
  ⟨actualRetainedMatrix_successive_residue k y hy,
    actualRetainedMatrix_minimizing_residue k y hy hv⟩

/-- A minimizing matrix and its physical successive residue exist for every original input. -/
theorem exists_actualRetained_minimizing_successive_residue (k : Parameters ℝ) :
    ∃ y ∈ actualRetainedMatrices k,∃ r : HermitianCoordinates ℝ,
      hermitianEnergy (actualParameters k) y/2=actualCandidateMinimum k ∧
      (∀ i,SuccessiveResidue 16 (y i) (r i)) ∧ hermitianTrace r=1 ∧
      hermitianEnergy k r/2=realMinimum k ∧
      ∃ phi : W3.Fields, ‖phi‖=1 ∧ complexMatrix (hermitianRe r) (hermitianIm r)=W3.gram phi ∧
        W3.quartic (couplings k) phi=realMinimum k := by
  obtain ⟨y,hy,hE⟩ := actualMinimum_has_retainedMatrix k
  have hv : hermitianEnergy (actualParameters k) y/2=actualCandidateMinimum k := by
    rw [actualCandidateMinimum_eq]
    exact hE
  exact ⟨y,hy,residueMatrix9 y (actualRetainedMatrices_bounded k y hy),hv,
    actualRetainedMatrix_minimizing_successive_residue k y hy hv⟩

#print axioms actualRetainedMatrices_algebraic
#print axioms actualRetainedMatrix_successive_residue
#print axioms actualRetainedMatrix_minimizing_successive_residue
#print axioms exists_actualRetained_minimizing_successive_residue
end W3.TransferOperator
