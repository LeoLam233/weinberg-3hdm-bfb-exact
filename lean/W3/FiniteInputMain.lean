import W3.Main
import W3.FiniteInputActualProgram
import W3.FiniteInputRetainedExecution

/-! Unrestricted central theorem with a uniform finite input-to-output program.
The arithmetic, exact comparison and finite real-root primitives are semantic
interfaces. No executable backend for arbitrary uncomputable reals is asserted.
All returned scalar/field programs contain only rational and original-input
leaves; genericity, physicality, bounds and termination are proved for every κ. -/
noncomputable section
namespace W3.FiniteInput
open W3.Infinitesimal W3.OperatorField W3.RealModel W3.TransferOperator W3.StrataTransfer
attribute [local instance] rationalTowerAlgebra
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def strictThresholdCode : Code 16 := 2 * .coefficient (.epsilon (0 : Fin 16).rev)

theorem strictThresholdCode_value (O : ResidueOracles) (κ : Parameters ℝ) :
    (runStage O κ 16 strictThresholdCode).value=2*chronologicalEpsilon 0 := by
  letI := O.coefficientEquality 16
  change (strictThresholdCode.run (stageInput κ 16) (rationalCoordinates 16) (O.roots 16)).value = _
  simp only [strictThresholdCode,run_mul,run_two,Code.run,CoefficientCode.eval]
  change (rationalTowerHom 16) ((2 : ℚ) : RationalTower 16) *
    (rationalTowerHom 16) (rationalChronologicalEpsilon 0) = _
  rw [rationalTowerHom_chronologicalEpsilon,map_ratCast]
  norm_num

def weakSignProgram (O : ResidueOracles) (κ : Parameters ℝ) : Bool :=
  decide (0 < (runStage O κ 16 (actualSelectedRecord O κ).scalar).value)
def strictSignProgram (O : ResidueOracles) (κ : Parameters ℝ) : Bool :=
  decide ((runStage O κ 16 strictThresholdCode).value <
    (runStage O κ 16 (actualSelectedRecord O κ).scalar).value)
def negativeSignProgram (O : ResidueOracles) (κ : Parameters ℝ) : Bool :=
  decide ((runStage O κ 16 (actualSelectedRecord O κ).scalar).value < 0)
def flatSignProgram (O : ResidueOracles) (κ : Parameters ℝ) : Bool :=
  decide (0 < (runStage O κ 16 (actualSelectedRecord O κ).scalar).value ∧
    (runStage O κ 16 (actualSelectedRecord O κ).scalar).value <
      (runStage O κ 16 strictThresholdCode).value)

theorem signPrograms_spec (O : ResidueOracles) (κ : Parameters ℝ) :
    (weakSignProgram O κ=true ↔ ∀ K,W3.PhysicalGram K→0≤W3.gramQuartic (couplings κ) K) ∧
    (strictSignProgram O κ=true ↔ ∀ K,W3.PhysicalGram K→0<W3.gramQuartic (couplings κ) K) ∧
    (negativeSignProgram O κ=true ↔ realMinimum κ<0) ∧
    (flatSignProgram O κ=true ↔ realMinimum κ=0) := by
  simp only [weakSignProgram,strictSignProgram,negativeSignProgram,flatSignProgram,
    decide_eq_true_eq,actualSelectedRecord_value,strictThresholdCode_value]
  have h := W3.universal_exact_criterion κ
  exact ⟨h.2.2.1.symm,h.2.2.2.1.symm,h.2.2.2.2.1.symm,h.2.2.2.2.2.1.symm⟩

theorem actualFields_negative_or_flat (O : ResidueOracles) (κ : Parameters ℝ) :
    (negativeSignProgram O κ=true → W3.quartic (couplings κ) (actualFields O κ)<0) ∧
    (flatSignProgram O κ=true → W3.quartic (couplings κ) (actualFields O κ)=0) := by
  have hval := (actualFields_spec O κ).2.2.trans (actualValueCode_success O κ).2.2
  rw [hval]
  exact ⟨(signPrograms_spec O κ).2.2.1.mp,(signPrograms_spec O κ).2.2.2.mp⟩

/-- Five central outputs of the exact finite construction: the literal finite
selected spectrum, all singular-input sign tests, the real minimum, a coded
physical field witness, and code coverage/execution for every old minimizer. -/
theorem uniform_finite_input_exact_criterion (O : ResidueOracles) (κ : Parameters ℝ) :
    ((actualCodeProgram O κ).map (fun r => (runStage O κ 16 r.scalar).value)).toFinset =
      actualCandidateValues κ ∧
    (actualCandidateValues κ).card≤30 ∧
    actualMinimumCodeProgram O κ=some (actualSelectedRecord O κ) ∧
    (runStage O κ 16 (actualSelectedRecord O κ).scalar).value=actualCandidateMinimum κ ∧
    (weakSignProgram O κ=true ↔ ∀ K,W3.PhysicalGram K→0≤W3.gramQuartic (couplings κ) K) ∧
    (strictSignProgram O κ=true ↔ ∀ K,W3.PhysicalGram K→0<W3.gramQuartic (couplings κ) K) ∧
    (negativeSignProgram O κ=true ↔ realMinimum κ<0) ∧
    (flatSignProgram O κ=true ↔ realMinimum κ=0) ∧
    successiveResidueCodeProgram O κ 16 (actualSelectedRecord O κ).scalar=some (actualValueCode O κ) ∧
    (runStage O κ 0 (actualValueCode O κ)).value=realMinimum κ ∧
    (‖actualFields O κ‖=1 ∧ W3.gram (actualFields O κ)=realCodeGram O κ (actualMatrixCode O κ) ∧
      W3.quartic (couplings κ) (actualFields O κ)=(runStage O κ 0 (actualValueCode O κ)).value) ∧
    (∀ y : Matrix16,∀ hy : y ∈ actualRetainedMatrices κ,
      hermitianEnergy (actualParameters κ) y/2=actualCandidateMinimum κ →
      ∃ p ∈ actualRetainedStageProgram O κ,
        stageMatrixValues O κ 16 p=y ∧
        (∀ i,successiveResidueCodeProgram O κ 16 (p i)=some (residueMatrixCode O κ p i) ∧
          SuccessiveResidue 16 (y i) (stageMatrixValues O κ 0 (residueMatrixCode O κ p) i)) ∧
        stageMatrixValues O κ 0 (residueMatrixCode O κ p)=
          residueMatrix9 y (actualRetainedMatrices_bounded κ y hy)) := by
  have hs := signPrograms_spec O κ
  have hv := actualValueCode_success O κ
  refine ⟨actualCodeProgram_values O κ,actualCandidateValues_card_le_thirty κ,
    actualSelectedRecord_selected O κ,actualSelectedRecord_value O κ,
    hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,hv.1,hv.2.2,actualFields_spec O κ,?_⟩
  intro y hy he
  obtain ⟨p,hp,hpy,hr,hres,_⟩ := every_old_retained_minimizer_coded_execution O κ y hy he
  exact ⟨p,hp,hpy,hr,hres⟩

/-- Literal program tests on all nine real and three unrestricted complex
couplings, with no genericity, reality or nonzero hypothesis. -/
theorem arbitrary_complex_finite_input_criterion (O : ResidueOracles) (k : W3.Couplings) :
    let κ := W3.Elimination.originalOfCouplings k
    (weakSignProgram O κ=true ↔ ∀ phi : W3.Fields,0≤W3.quartic k phi) ∧
    (strictSignProgram O κ=true ↔ ∀ phi : W3.Fields,phi≠0→0<W3.quartic k phi) ∧
    (negativeSignProgram O κ=true ↔ ∃ phi : W3.Fields,‖phi‖=1 ∧ W3.quartic k phi<0) ∧
    (flatSignProgram O κ=true ↔ (∀ phi : W3.Fields,0≤W3.quartic k phi) ∧
      ∃ phi : W3.Fields,‖phi‖=1 ∧ W3.quartic k phi=0) := by
  dsimp only
  simp only [weakSignProgram,strictSignProgram,negativeSignProgram,flatSignProgram,
    decide_eq_true_eq,actualSelectedRecord_value,strictThresholdCode_value]
  have h := W3.arbitrary_complex_criterion k
  exact ⟨h.1.symm,h.2.1.symm,h.2.2.1.symm,h.2.2.2.symm⟩

#print axioms uniform_finite_input_exact_criterion
#print axioms arbitrary_complex_finite_input_criterion
#print axioms every_old_retained_minimizer_coded_execution
end W3.FiniteInput
