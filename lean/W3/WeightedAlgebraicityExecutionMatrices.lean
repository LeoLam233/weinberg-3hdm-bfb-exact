import W3.WeightedAlgebraicityExecution
import W3.TransferOperatorRetained

/-! Executable finite residue extraction for every actual retained matrix, with
all expression and boundedness premises discharged from list membership. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace W3.Weighted.Expression
open W3.Elimination W3.Infinitesimal W3.OperatorField W3.TransferOperator W3.RealModel W3.StrataTransfer
local instance : Algebra (RationalTower 16) SixteenLevelField := rationalTowerAlgebra 16

theorem actual_retained_coordinates_presented (κ : Parameters ℝ) (y : Matrix16)
    (hy : y ∈ actualRetainedMatrices κ) : ∀ i, Presented (RationalTower 16) (y i) := by
  classical
  rcases Finset.mem_union.mp hy with hp | hd
  · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hp
    exact actual_primal_candidate_presented κ _ j
  · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hd
    exact (actual_dual_candidate_presented κ _ j).1

def actualRetainedCoordinateExpression (κ : Parameters ℝ) (y : Matrix16)
    (hy : y ∈ actualRetainedMatrices κ) (i : Fin 9) :
    RootExpression (RationalTower 16) SixteenLevelField (y i) :=
  Classical.choice (actual_retained_coordinates_presented κ y hy i)

/-- Nine coordinate programs, each executing exactly sixteen finite residue
steps with the source-compatible arithmetic/equality/root-enumeration oracles. -/
def executeActualRetainedMatrix (O : ResidueOracles) (κ : Parameters ℝ) (y : Matrix16)
    (hy : y ∈ actualRetainedMatrices κ) : HermitianCoordinates ℝ := fun i =>
  (executeSuccessiveResidues O 16 (y i) (actualRetainedCoordinateExpression κ y hy i) (-1) 1
    (by simpa only [map_neg,map_one] using (actualRetainedMatrices_bounded κ y hy i).1)
    (by simpa only [map_one] using (actualRetainedMatrices_bounded κ y hy i).2)).val

/-- The executed matrix is exactly the previously verified physical Gram residue. -/
theorem executeActualRetainedMatrix_eq (O : ResidueOracles) (κ : Parameters ℝ) (y : Matrix16)
    (hy : y ∈ actualRetainedMatrices κ) :
    executeActualRetainedMatrix O κ y hy = residueMatrix9 y (actualRetainedMatrices_bounded κ y hy) := by
  funext i
  rw [executeActualRetainedMatrix,executeSuccessiveResidues_eq_stdPart,residueMatrix9_eq_stdPart]

/-- Every minimizing retained matrix produces an exact normalized original
Gram minimizer through this finite executed extraction. -/
theorem executeActualRetainedMatrix_minimizing (O : ResidueOracles) (κ : Parameters ℝ) (y : Matrix16)
    (hy : y ∈ actualRetainedMatrices κ)
    (hv : hermitianEnergy (actualParameters κ) y/2 = actualCandidateMinimum κ) :
    hermitianTrace (executeActualRetainedMatrix O κ y hy)=1 ∧
      hermitianEnergy κ (executeActualRetainedMatrix O κ y hy)/2=realMinimum κ ∧
      ∃ phi : W3.Fields, ‖phi‖=1 ∧
        complexMatrix (hermitianRe (executeActualRetainedMatrix O κ y hy))
          (hermitianIm (executeActualRetainedMatrix O κ y hy))=W3.gram phi ∧
        W3.quartic (couplings κ) phi=realMinimum κ := by
  rw [executeActualRetainedMatrix_eq]
  exact actualRetainedMatrix_minimizing_residue κ y hy hv

/-- Unconditional exact witness production from the literal finite candidate
list and the finite residue executor. -/
theorem execute_actual_minimizing_witness (O : ResidueOracles) (κ : Parameters ℝ) :
    ∃ y : Matrix16, ∃ hy : y ∈ actualRetainedMatrices κ,
      hermitianEnergy (actualParameters κ) y/2 = actualCandidateMinimum κ ∧
      ∃ phi : W3.Fields, ‖phi‖=1 ∧
        complexMatrix (hermitianRe (executeActualRetainedMatrix O κ y hy))
          (hermitianIm (executeActualRetainedMatrix O κ y hy))=W3.gram phi ∧
        W3.quartic (couplings κ) phi=executeActualMinimum O κ := by
  obtain ⟨y,hy,hv⟩ := actualMinimum_has_retainedMatrix κ
  have hv' : hermitianEnergy (actualParameters κ) y/2 = actualCandidateMinimum κ := by
    rwa [actualCandidateMinimum_eq]
  refine ⟨y,hy,hv',?_⟩
  rw [executeActualMinimum_eq]
  exact (executeActualRetainedMatrix_minimizing O κ y hy hv').2.2

#print axioms executeActualRetainedMatrix_eq
#print axioms executeActualRetainedMatrix_minimizing
#print axioms execute_actual_minimizing_witness
end W3.Weighted.Expression
