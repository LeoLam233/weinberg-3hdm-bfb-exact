import W3.FiniteInputRetainedCoverage
import W3.FiniteInputMatrixResidues

/-! Every old retained minimizer, with its original matrix unchanged, has a
finite-list code witness whose literal sixteen-stage residue execution and
literal pivot reconstruction attain the original real minimum. No code is
created by an arbitrary semantic coefficient or existential choice. -/
noncomputable section
namespace W3.FiniteInput
open W3.Infinitesimal W3.OperatorField W3.RealModel W3.TransferOperator W3.StrataTransfer
attribute [local instance] rationalTowerAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The complete covering list under precisely the residue executor's root
and coefficient-equality primitive interfaces. -/
def actualRetainedStageProgram (O : ResidueOracles) (κ : Parameters ℝ) : List (Fin 9 → Code 16) := by
  letI := O.coefficientEquality 16
  exact actualRetainedProvenanceProgram κ (O.roots 16)

theorem actualRetainedStageProgram_covers (O : ResidueOracles) (κ : Parameters ℝ)
    (y : Matrix16) (hy : y ∈ actualRetainedMatrices κ) :
    ∃ p ∈ actualRetainedStageProgram O κ, stageMatrixValues O κ 16 p = y := by
  letI := O.coefficientEquality 16
  obtain ⟨p,hp,hv⟩ := actualRetainedProvenanceProgram_covers κ (O.roots 16) y hy
  exact ⟨p,hp,hv⟩

/-- Every code representing an old retained matrix executes all sixteen
residue stages successfully, with the same nine real residues as the source. -/
theorem oldRetainedMatrixCode_residue (O : ResidueOracles) (κ : Parameters ℝ)
    (y : Matrix16) (hy : y ∈ actualRetainedMatrices κ) (p : Fin 9 → Code 16)
    (hp : stageMatrixValues O κ 16 p = y) :
    (∀ i, successiveResidueCodeProgram O κ 16 (p i) = some (residueMatrixCode O κ p i) ∧
      SuccessiveResidue 16 (y i) (stageMatrixValues O κ 0 (residueMatrixCode O κ p) i)) ∧
    stageMatrixValues O κ 0 (residueMatrixCode O κ p) =
      residueMatrix9 y (actualRetainedMatrices_bounded κ y hy) := by
  subst y
  have hb := actualRetainedMatrices_bounded κ (stageMatrixValues O κ 16 p) hy
  exact ⟨fun i => residueMatrixCode_success O κ p hb i, residueMatrixCode_values O κ p hb⟩

/-- Physicality and the minimum value are inherited from the original
minimizer, not asserted for the possibly nonphysical covering-list extras. -/
theorem oldRetainedMinimizerCode_physical (O : ResidueOracles) (κ : Parameters ℝ)
    (y : Matrix16) (hy : y ∈ actualRetainedMatrices κ)
    (hv : hermitianEnergy (actualParameters κ) y/2=actualCandidateMinimum κ)
    (p : Fin 9 → Code 16) (hp : stageMatrixValues O κ 16 p = y) :
    W3.PhysicalGram (realCodeGram O κ (residueMatrixCode O κ p)) ∧
      W3.gramQuartic (couplings κ) (realCodeGram O κ (residueMatrixCode O κ p)) = realMinimum κ := by
  apply residueMatrixCode_minimizing O κ p
  · rw [hp]
    exact actualRetainedMatrices_physical κ y hy
  · rwa [hp]

/-- The literal pivot algorithm yields normalized doublets with exactly the
old matrix's residue Gram and exactly the original real minimum. -/
theorem oldRetainedMinimizerCode_fields (O : ResidueOracles) (κ : Parameters ℝ)
    (y : Matrix16) (hy : y ∈ actualRetainedMatrices κ)
    (hv : hermitianEnergy (actualParameters κ) y/2=actualCandidateMinimum κ)
    (p : Fin 9 → Code 16) (hp : stageMatrixValues O κ 16 p = y) :
    let hphys := (oldRetainedMinimizerCode_physical O κ y hy hv p hp).1
    let phi := finalMatrixFields O κ (residueMatrixCode O κ p) hphys
    ‖phi‖=1 ∧
      W3.gram phi = complexMatrix
        (hermitianRe (residueMatrix9 y (actualRetainedMatrices_bounded κ y hy)))
        (hermitianIm (residueMatrix9 y (actualRetainedMatrices_bounded κ y hy))) ∧
      W3.quartic (couplings κ) phi=realMinimum κ := by
  have hphys := oldRetainedMinimizerCode_physical O κ y hy hv p hp
  have hf := finalMatrixFields_spec O κ (residueMatrixCode O κ p) hphys.1
  have hr := (oldRetainedMatrixCode_residue O κ y hy p hp).2
  refine ⟨hf.1,?_,hf.2.2.trans hphys.2⟩
  rw [hf.2.1]
  change complexMatrix (hermitianRe (stageMatrixValues O κ 0 (residueMatrixCode O κ p)))
    (hermitianIm (stageMatrixValues O κ 0 (residueMatrixCode O κ p))) = _
  rw [hr]

/-- End-to-end universal old-list statement. The witness is drawn from one
uniform finite list; execution consumes that very witness. No preferred
representative replaces y, and no additional physicality/algebraicity or
boundedness hypotheses are left to the caller. -/
theorem every_old_retained_minimizer_coded_execution (O : ResidueOracles) (κ : Parameters ℝ)
    (y : Matrix16) (hy : y ∈ actualRetainedMatrices κ)
    (hv : hermitianEnergy (actualParameters κ) y/2=actualCandidateMinimum κ) :
    ∃ p ∈ actualRetainedStageProgram O κ,
      ∃ hp : stageMatrixValues O κ 16 p = y,
        (∀ i, successiveResidueCodeProgram O κ 16 (p i) = some (residueMatrixCode O κ p i) ∧
          SuccessiveResidue 16 (y i) (stageMatrixValues O κ 0 (residueMatrixCode O κ p) i)) ∧
        stageMatrixValues O κ 0 (residueMatrixCode O κ p) =
          residueMatrix9 y (actualRetainedMatrices_bounded κ y hy) ∧
        let hphys := (oldRetainedMinimizerCode_physical O κ y hy hv p hp).1
        let phi := finalMatrixFields O κ (residueMatrixCode O κ p) hphys
        ‖phi‖=1 ∧
          W3.gram phi = complexMatrix
            (hermitianRe (residueMatrix9 y (actualRetainedMatrices_bounded κ y hy)))
            (hermitianIm (residueMatrix9 y (actualRetainedMatrices_bounded κ y hy))) ∧
          W3.quartic (couplings κ) phi=realMinimum κ := by
  obtain ⟨p,hp,hpy⟩ := actualRetainedStageProgram_covers O κ y hy
  have hr := oldRetainedMatrixCode_residue O κ y hy p hpy
  exact ⟨p,hp,hpy,hr.1,hr.2,oldRetainedMinimizerCode_fields O κ y hy hv p hpy⟩

#print axioms actualRetainedStageProgram_covers
#print axioms oldRetainedMatrixCode_residue
#print axioms oldRetainedMinimizerCode_fields
#print axioms every_old_retained_minimizer_coded_execution
end W3.FiniteInput
