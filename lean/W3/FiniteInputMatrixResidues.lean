import W3.FiniteInputResidueProgram
import W3.FiniteInputOperator
import W3.FiniteInputPivotTrace
import W3.TransferOperatorRetained

/-! Literal code-to-code execution on all nine matrix coordinates, followed by
the original two-pivot reconstruction. No selected ambient coordinate is used
as a new coefficient leaf. -/
noncomputable section
namespace W3.FiniteInput
open W3.Infinitesimal W3.OperatorField W3.RealModel W3.TransferOperator W3.StrataTransfer
attribute [local instance] rationalTowerAlgebra
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
local instance : Algebra (RationalTower 0) ℝ := rationalTowerAlgebra 0

/-- Uniform total wrapper; the zero fallback is proved unreachable for every
physical input matrix below. It depends on no unknown scalar bound. -/
def residueCode (O : ResidueOracles) (κ : Parameters ℝ) (n : Nat) (c : Code n) : Code 0 :=
  (successiveResidueCodeProgram O κ n c).getD 0

theorem residueCode_correct (O : ResidueOracles) (κ : Parameters ℝ)
    (n : Nat) (c : Code n) (a b : ℝ)
    (ha : baseEmbed realModel n a ≤ (runStage O κ n c).value)
    (hb : (runStage O κ n c).value ≤ baseEmbed realModel n b) :
    successiveResidueCodeProgram O κ n c = some (residueCode O κ n c) ∧
      SuccessiveResidue n (runStage O κ n c).value
        (runStage O κ 0 (residueCode O κ n c)).value ∧
      (runStage O κ 0 (residueCode O κ n c)).value =
        ArchimedeanClass.stdPart (runStage O κ n c).value := by
  obtain ⟨d,hd,hr,hs⟩ := successiveResidueCodeProgram_correct O κ n c a b ha hb
  have he : residueCode O κ n c=d := by simp only [residueCode,hd,Option.getD_some]
  simpa only [he] using And.intro hd (And.intro hr hs)

def stageMatrixValues (O : ResidueOracles) (κ : Parameters ℝ) (n : Nat)
    (y : Fin 9 → Code n) : HermitianCoordinates (Tower realModel n) :=
  fun i => (runStage O κ n (y i)).value

def residueMatrixCode (O : ResidueOracles) (κ : Parameters ℝ)
    (y : Fin 9 → Code 16) : Fin 9 → Code 0 := fun i => residueCode O κ 16 (y i)

theorem residueMatrixCode_success (O : ResidueOracles) (κ : Parameters ℝ)
    (y : Fin 9 → Code 16) (hy : MatrixBounded (stageMatrixValues O κ 16 y)) (i : Fin 9) :
    successiveResidueCodeProgram O κ 16 (y i) = some (residueMatrixCode O κ y i) ∧
      SuccessiveResidue 16 (stageMatrixValues O κ 16 y i)
        (stageMatrixValues O κ 0 (residueMatrixCode O κ y) i) := by
  have h := residueCode_correct O κ 16 (y i) (-1) 1
    (by simpa only [stageMatrixValues,map_neg,map_one] using (hy i).1)
    (by simpa only [stageMatrixValues,map_one] using (hy i).2)
  exact ⟨h.1,h.2.1⟩

theorem residueMatrixCode_values (O : ResidueOracles) (κ : Parameters ℝ)
    (y : Fin 9 → Code 16) (hy : MatrixBounded (stageMatrixValues O κ 16 y)) :
    stageMatrixValues O κ 0 (residueMatrixCode O κ y) =
      residueMatrix9 (stageMatrixValues O κ 16 y) hy := by
  exact (successive_matrix_residue_eq _ hy _
    (fun i => (residueMatrixCode_success O κ y hy i).2)).symm

def realCodeGram (O : ResidueOracles) (κ : Parameters ℝ) (y : Fin 9 → Code 0) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  complexMatrix (hermitianRe (stageMatrixValues O κ 0 y))
    (hermitianIm (stageMatrixValues O κ 0 y))

theorem residueMatrixCode_minimizing (O : ResidueOracles) (κ : Parameters ℝ)
    (y : Fin 9 → Code 16)
    (hp : ∃ x : RealFields SixteenLevelField, mass x=1 ∧ GramMatches x (stageMatrixValues O κ 16 y))
    (hv : hermitianEnergy (actualParameters κ) (stageMatrixValues O κ 16 y)/2=actualCandidateMinimum κ) :
    W3.PhysicalGram (realCodeGram O κ (residueMatrixCode O κ y)) ∧
      W3.gramQuartic (couplings κ) (realCodeGram O κ (residueMatrixCode O κ y))=realMinimum κ := by
  have hb : MatrixBounded (stageMatrixValues O κ 16 y) := by
    obtain ⟨x,hx,hG⟩ := hp
    exact gramMatches_bounded hx hG
  have hv' := hv.trans (actualCandidateMinimum_eq κ)
  obtain ⟨_,_,phi,hphi,hgram,henergy⟩ := minimizing_matrix_residue κ _ hb hp hv'
  have he : realCodeGram O κ (residueMatrixCode O κ y)=W3.gram phi := by
    unfold realCodeGram
    rw [residueMatrixCode_values O κ y hb]
    exact hgram
  constructor
  · rw [he]
    exact (W3.physicalGram_iff_fields _).mpr ⟨phi,hphi,rfl⟩
  · rw [he,W3.gramQuartic_gram]
    exact henergy

/-- The real-stage syntax interpreter is exactly the pivot interpreter. -/
theorem realCodeGram_eq_pivot (O : ResidueOracles) (κ : Parameters ℝ) (y : Fin 9 → Code 0) :
    letI := O.coefficientEquality 0
    realCodeGram O κ y =
      pivotMatrixValue (stageInput κ 0) Fin.elim0 (O.roots 0) (pivotMatrixCode9 y) := by
  letI := O.coefficientEquality 0
  rw [pivotMatrixCode9_correct]
  have he : rationalCoordinates 0=Fin.elim0 := by funext i; exact Fin.elim0 i
  have hv : stageMatrixValues O κ 0 y =
      (fun j => (y j |>.run (stageInput κ 0) Fin.elim0 (O.roots 0)).value) := by
    funext j
    change (y j |>.run (stageInput κ 0) (rationalCoordinates 0) (O.roots 0)).value = _
    rw [he]
  exact congrArg (fun z => complexMatrix (hermitianRe z) (hermitianIm z)) hv

/-- Return literal input-code doublet rows and the exact Eq. (41) pivot trace. -/
def finalMatrixPivot (O : ResidueOracles) (κ : Parameters ℝ) (y : Fin 9 → Code 0)
    (hy : W3.PhysicalGram (realCodeGram O κ y)) : CodedPivotResult 0 := by
  letI := O.coefficientEquality 0
  exact codedRealPivotAlgorithm (stageInput κ 0) (O.roots 0) y
    (by rw [← realCodeGram_eq_pivot O κ y]; exact hy)

def finalMatrixFields (O : ResidueOracles) (κ : Parameters ℝ) (y : Fin 9 → Code 0)
    (hy : W3.PhysicalGram (realCodeGram O κ y)) : W3.Fields := by
  letI := O.coefficientEquality 0
  exact (finalMatrixPivot O κ y hy).fields (stageInput κ 0) Fin.elim0 (O.roots 0)

theorem finalMatrixFields_spec (O : ResidueOracles) (κ : Parameters ℝ) (y : Fin 9 → Code 0)
    (hy : W3.PhysicalGram (realCodeGram O κ y)) :
    ‖finalMatrixFields O κ y hy‖=1 ∧
      W3.gram (finalMatrixFields O κ y hy)=realCodeGram O κ y ∧
      W3.quartic (couplings κ) (finalMatrixFields O κ y hy)=
        W3.gramQuartic (couplings κ) (realCodeGram O κ y) := by
  letI := O.coefficientEquality 0
  have hp : W3.PhysicalGram (pivotMatrixValue (stageInput κ 0) Fin.elim0
      (O.roots 0) (pivotMatrixCode9 y)) := by rw [← realCodeGram_eq_pivot O κ y]; exact hy
  change ‖codedPivotedFields _ _ _ _ hp‖=1 ∧ _
  exact ⟨codedPivotedFields_normalized _ _ _ _ hp,
    (codedPivotedFields_gram _ _ _ _ hp).trans (realCodeGram_eq_pivot O κ y).symm,
    (codedPivotedFields_value _ _ _ (couplings κ) _ hp).trans
      (congrArg (W3.gramQuartic (couplings κ)) (realCodeGram_eq_pivot O κ y).symm)⟩

#print axioms residueMatrixCode_minimizing
#print axioms finalMatrixFields_spec
end W3.FiniteInput
