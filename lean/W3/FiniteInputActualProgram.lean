import W3.FiniteInputTwoSpectrumPhysical
import W3.FiniteInputRetainedCoverage
import W3.FiniteInputMatrixResidues
import W3.WeightedAlgebraicityExecution

/-! The uniform actual-input program. The only data arguments are the fifteen
original coordinates and exact primitive interface. Genericity, success and
bounds are theorems, not extra promises or supplied candidate expressions. -/
noncomputable section
namespace W3.FiniteInput
open W3.Infinitesimal W3.OperatorField W3.RealModel W3.TransferOperator W3.StrataTransfer
open W3.Weighted.Expression W3.Elimination
attribute [local instance] rationalTowerAlgebra
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def actualCodeProgram (O : ResidueOracles) (κ : Parameters ℝ) : List (PhysicalCodeRecord 16) := by
  letI := O.coefficientEquality 16
  exact twoSpectrumProgram (originalInput κ) (rationalCoordinates 16) (O.roots 16) actualParameterCode

def actualMinimumCodeProgram (O : ResidueOracles) (κ : Parameters ℝ) : Option (PhysicalCodeRecord 16) := by
  letI := O.coefficientEquality 16
  exact twoSpectrumMinimumProgram (originalInput κ) (rationalCoordinates 16) (O.roots 16) actualParameterCode

@[simp] theorem runStage_sixteen_value (O : ResidueOracles) (κ : Parameters ℝ) (c : Code 16) :
    letI := O.coefficientEquality 16
    (runStage O κ 16 c).value =
      (c.run (originalInput κ) (rationalCoordinates 16) (O.roots 16)).value := rfl

@[simp] theorem stageMatrixValues_sixteen (O : ResidueOracles) (κ : Parameters ℝ)
    (y : Fin 9 → Code 16) :
    letI := O.coefficientEquality 16
    stageMatrixValues O κ 16 y = runCodes (originalInput κ) (rationalCoordinates 16) (O.roots 16) y := rfl

lemma actual_code_generic (O : ResidueOracles) (κ : Parameters ℝ) :
    completeWeightedExceptional (originalPrimal (runParameters (K := SixteenLevelField)
      (originalInput κ) (rationalCoordinates 16) actualParameterCode)) ≠ 0 ∧
    originalInverseDen (runParameters (K := SixteenLevelField)
      (originalInput κ) (rationalCoordinates 16) actualParameterCode) ≠ 0 ∧
    completeWeightedExceptional (originalDual (runParameters (K := SixteenLevelField)
      (originalInput κ) (rationalCoordinates 16) actualParameterCode)) ≠ 0 := by
  letI := O.coefficientEquality 16
  have he := actualParameterCode_runParameters κ
  rw [he]
  exact actualParameters_generic κ

theorem actualCodeProgram_values (O : ResidueOracles) (κ : Parameters ℝ) :
    ((actualCodeProgram O κ).map (fun r => (runStage O κ 16 r.scalar).value)).toFinset =
      actualCandidateValues κ := by
  letI := O.coefficientEquality 16
  have h := twoSpectrumProgram_valueSet (originalInput κ) (rationalCoordinates 16) (O.roots 16)
    actualParameterCode (actual_code_generic O κ).1 (actual_code_generic O κ).2.2
  simpa only [actualCodeProgram,runStage_sixteen_value,
    actualParameterCode_runParameters,actualCandidateValues] using h

theorem actualMinimumCodeProgram_exists (O : ResidueOracles) (κ : Parameters ℝ) :
    ∃ r, actualMinimumCodeProgram O κ=some r := by
  letI := O.coefficientEquality 16
  exact twoSpectrumMinimumProgram_exists (originalInput κ) (rationalCoordinates 16) (O.roots 16)
    actualParameterCode (actual_code_generic O κ).1 (actual_code_generic O κ).2.2

/-- Only unwrap a successful literal finite-list selection, never choose an
expression representing an already known semantic answer. -/
def actualSelectedRecord (O : ResidueOracles) (κ : Parameters ℝ) : PhysicalCodeRecord 16 :=
  (actualMinimumCodeProgram O κ).get (by
    obtain ⟨r,hr⟩ := actualMinimumCodeProgram_exists O κ
    simp only [hr,Option.isSome_some])

theorem actualSelectedRecord_selected (O : ResidueOracles) (κ : Parameters ℝ) :
    actualMinimumCodeProgram O κ=some (actualSelectedRecord O κ) := by
  obtain ⟨r,hr⟩ := actualMinimumCodeProgram_exists O κ
  simp only [actualSelectedRecord,hr,Option.get_some]

theorem actualSelectedRecord_mem (O : ResidueOracles) (κ : Parameters ℝ) :
    actualSelectedRecord O κ ∈ actualCodeProgram O κ := by
  letI := O.coefficientEquality 16
  exact (codeArgmin_spec (originalInput κ) (rationalCoordinates 16) (O.roots 16)
    PhysicalCodeRecord.scalar _ _ (actualSelectedRecord_selected O κ)).1

theorem actualSelectedRecord_value (O : ResidueOracles) (κ : Parameters ℝ) :
    (runStage O κ 16 (actualSelectedRecord O κ).scalar).value=actualCandidateMinimum κ := by
  letI := O.coefficientEquality 16
  have h := twoSpectrumMinimumProgram_minimum (originalInput κ) (rationalCoordinates 16) (O.roots 16)
    actualParameterCode (actual_code_generic O κ).1 (actual_code_generic O κ).2.2
    (actualSelectedRecord O κ) (actualSelectedRecord_selected O κ)
  simpa only [runStage_sixteen_value,actualParameterCode_runParameters,
    actualCandidateMinimum,actualCandidateValues] using h

theorem actualCodeProgram_physical (O : ResidueOracles) (κ : Parameters ℝ)
    (r : PhysicalCodeRecord 16) (hr : r ∈ actualCodeProgram O κ) :
    (∃ x : RealFields SixteenLevelField,mass x=1 ∧ GramMatches x (stageMatrixValues O κ 16 r.matrix)) ∧
      hermitianEnergy (actualParameters κ) (stageMatrixValues O κ 16 r.matrix)/2=
        (runStage O κ 16 r.scalar).value := by
  letI := O.coefficientEquality 16
  have hg := actual_code_generic O κ
  have hp := twoSpectrumProgram_physical (originalInput κ) (rationalCoordinates 16) (O.roots 16)
    actualParameterCode hg.2.1 hg.1 hg.2.2 r hr
  have he := twoSpectrumProgram_energy (originalInput κ) (rationalCoordinates 16) (O.roots 16)
    actualParameterCode hg.2.1 hg.1 hg.2.2 r hr
  obtain ⟨x,hx,hG,_⟩ := hp
  constructor
  · refine ⟨x,hx,(gramMatches_iff _ _).mpr ?_⟩
    simpa only [stageMatrixValues_sixteen] using hG
  · simpa only [stageMatrixValues_sixteen,runStage_sixteen_value,
      actualParameterCode_runParameters] using he.symm

def actualValueCode (O : ResidueOracles) (κ : Parameters ℝ) : Code 0 :=
  residueCode O κ 16 (actualSelectedRecord O κ).scalar

theorem actualValueCode_success (O : ResidueOracles) (κ : Parameters ℝ) :
    successiveResidueCodeProgram O κ 16 (actualSelectedRecord O κ).scalar=some (actualValueCode O κ) ∧
      SuccessiveResidue 16 (actualCandidateMinimum κ) (runStage O κ 0 (actualValueCode O κ)).value ∧
      (runStage O κ 0 (actualValueCode O κ)).value=realMinimum κ := by
  have hb := actualCandidateMinimum_input_bound κ
  have h := residueCode_correct O κ 16 (actualSelectedRecord O κ).scalar
    (-inputMagnitudeBound κ) (inputMagnitudeBound κ)
    (by rw [actualSelectedRecord_value]; exact hb.1)
    (by rw [actualSelectedRecord_value]; exact hb.2)
  rw [actualSelectedRecord_value] at h
  refine ⟨h.1,h.2.1,?_⟩
  exact h.2.2.trans (by rw [actualCandidateMinimum_eq]; exact (actual_minimum_signs_and_residue κ).2.2.2.2)

def actualMatrixCode (O : ResidueOracles) (κ : Parameters ℝ) : Fin 9 → Code 0 :=
  residueMatrixCode O κ (actualSelectedRecord O κ).matrix

theorem actualMatrixCode_spec (O : ResidueOracles) (κ : Parameters ℝ) :
    W3.PhysicalGram (realCodeGram O κ (actualMatrixCode O κ)) ∧
      W3.gramQuartic (couplings κ) (realCodeGram O κ (actualMatrixCode O κ))=realMinimum κ := by
  have h := actualCodeProgram_physical O κ _ (actualSelectedRecord_mem O κ)
  exact residueMatrixCode_minimizing O κ _ h.1 (h.2.trans (actualSelectedRecord_value O κ))

def actualPivotTrace (O : ResidueOracles) (κ : Parameters ℝ) : CodedPivotResult 0 :=
  finalMatrixPivot O κ (actualMatrixCode O κ) (actualMatrixCode_spec O κ).1

def actualFields (O : ResidueOracles) (κ : Parameters ℝ) : W3.Fields :=
  finalMatrixFields O κ (actualMatrixCode O κ) (actualMatrixCode_spec O κ).1

theorem actualFields_spec (O : ResidueOracles) (κ : Parameters ℝ) :
    ‖actualFields O κ‖=1 ∧ W3.gram (actualFields O κ)=realCodeGram O κ (actualMatrixCode O κ) ∧
      W3.quartic (couplings κ) (actualFields O κ)=(runStage O κ 0 (actualValueCode O κ)).value := by
  have h := finalMatrixFields_spec O κ (actualMatrixCode O κ) (actualMatrixCode_spec O κ).1
  exact ⟨h.1,h.2.1,h.2.2.trans ((actualMatrixCode_spec O κ).2.trans (actualValueCode_success O κ).2.2.symm)⟩

#print axioms actualCodeProgram_values
#print axioms actualSelectedRecord_value
#print axioms actualValueCode_success
#print axioms actualFields_spec
end W3.FiniteInput
