import W3.FiniteInputAnnihilator
import W3.FiniteInputResidueClearing
import W3.FiniteInputResidueSelection
import W3.InfinitesimalResidueExecution

/-! # Actual code-to-code residue execution
A stage compiles its finite source code, structurally clears and normalizes the
emitted coefficient programs, enumerates root-index programs, and selects by
exact finite distance comparisons. Sixteen-stage execution uses structural
recursion and preserves those actual codes at every stage. -/
noncomputable section
namespace W3.FiniteInput
open Polynomial W3.Infinitesimal
attribute [local instance] rationalTowerAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The explicit input and epsilon interpretation at a tower stage. -/
def runStage (O : ResidueOracles) (u : Fin 15 → ℝ) (n : Nat) (c : Code n) :
    Evaluated (F := RationalTower n) (K := Tower realModel n) := by
  letI := O.coefficientEquality n
  exact c.run (stageInput u n) (rationalCoordinates n) (O.roots n)

/-- This is the actual emitted annihilator coefficient list of the source code. -/
def stageAnnihilatorCodes (O : ResidueOracles) (u : Fin 15 → ℝ) (n : Nat) (c : Code n) :
    List (CoefficientCode n) := by
  letI := O.coefficientEquality n
  exact c.annihilatorCodes (stageInput u n) (rationalCoordinates n) (O.roots n)

theorem stageAnnihilatorCodes_spec (O : ResidueOracles) (u : Fin 15 → ℝ)
    (n : Nat) (c : Code n) :
    (stagePolynomial u (stageAnnihilatorCodes O u n c)).Monic ∧
    (stagePolynomial u (stageAnnihilatorCodes O u n c)).eval₂ (rationalTowerHom n)
      (runStage O u n c).value = 0 := by
  letI := O.coefficientEquality n
  exact c.annihilatorCodes_spec (stageInput u n) (rationalCoordinates n) (O.roots n)

/-- All root coefficients for the next stage are synthesized from the source
code and the fifteen real inputs; no arbitrary polynomial is an extra input. -/
def stageResidueCoefficients (O : ResidueOracles) (u : Fin 15 → ℝ) (n : Nat)
    (c : Code (n+1)) : List (CoefficientCode n) := by
  letI := O.coefficientEquality n
  exact normalizedResidueCoefficients u (stageAnnihilatorCodes O u (n+1) c)

/-- A typed distance operand request retains both source programs. The
predecessor code is embedded canonically into the next tower field; no new
ambient scalar constant or root-matching oracle is inserted. -/
structure ResidueDistanceRequest (n : Nat) where
  source : Code (n+1)
  predecessor : Code n

def ResidueDistanceRequest.value (O : ResidueOracles) (u : Fin 15 → ℝ) {n : Nat}
    (r : ResidueDistanceRequest n) : Tower realModel (n+1) :=
  |(runStage O u (n+1) r.source).value -
    stepEmbed realModel n (runStage O u n r.predecessor).value|

/-- Every score comparison is an exact comparison between typed requests whose
operands still carry their finite input code provenance. -/
def selectResidueRequests (O : ResidueOracles) (u : Fin 15 → ℝ) (n : Nat)
    (c : Code (n+1)) : List (Code n) → Option (Code n)
  | [] => none
  | d :: ds => some (finiteArgmin
      (fun e => (ResidueDistanceRequest.mk c e).value O u) d ds)

/-- Finite, inspectable operand provenance for every score used by this stage. -/
def stageDistanceRequests (O : ResidueOracles) (u : Fin 15 → ℝ) (n : Nat)
    (c : Code (n+1)) : List (ResidueDistanceRequest n) := by
  letI := O.coefficientEquality n
  exact (rootFamily (stageInput u n) (rationalCoordinates n) (O.roots n)
    (stageResidueCoefficients O u n c)).map (ResidueDistanceRequest.mk c)

theorem stageDistanceRequests_operands (O : ResidueOracles) (u : Fin 15 → ℝ)
    (n : Nat) (c : Code (n+1)) (r : ResidueDistanceRequest n)
    (hr : r ∈ stageDistanceRequests O u n c) :
    r.source = c ∧ ∃ i : Nat,
      r.predecessor = .root (stageResidueCoefficients O u n c) i ∧
      i < ((O.roots n).roots ((stagePolynomial u (stageResidueCoefficients O u n c)).map
        (rationalTowerHom n))).length := by
  letI := O.coefficientEquality n
  simp only [stageDistanceRequests, List.mem_map] at hr
  obtain ⟨d, hd, rfl⟩ := hr
  refine ⟨rfl, ?_⟩
  simp only [rootFamily, List.mem_ofFn] at hd
  obtain ⟨i, hi⟩ := hd
  exact ⟨i.val, hi.symm, i.isLt⟩

/-- The unwrapped stage is still an ordinary finite Option program. -/
def codedResidueStageProgram (O : ResidueOracles) (u : Fin 15 → ℝ) (n : Nat)
    (c : Code (n+1)) : Option (Code n) := by
  letI := O.coefficientEquality n
  exact selectResidueRequests O u n c (rootFamily (stageInput u n)
    (rationalCoordinates n) (O.roots n) (stageResidueCoefficients O u n c))

theorem codedResidueStageProgram_eq_rootProgram (O : ResidueOracles) (u : Fin 15 → ℝ)
    (n : Nat) (c : Code (n+1)) :
    letI := O.coefficientEquality n
    codedResidueStageProgram O u n c =
      codedResidueRootProgram (stageInput u n) (rationalCoordinates n) (O.roots n)
        (stageResidueCoefficients O u n c) (runStage O u (n+1) c).value := by
  letI := O.coefficientEquality n
  unfold codedResidueStageProgram codedResidueRootProgram
  cases rootFamily (stageInput u n) (rationalCoordinates n) (O.roots n)
    (stageResidueCoefficients O u n c) <;> rfl

theorem codedResidueStageProgram_correct (O : ResidueOracles) (u : Fin 15 → ℝ)
    (n : Nat) (c : Code (n+1))
    (hx : BaseBounded (Tower realModel n) (runStage O u (n+1) c).value) :
    ∃ d : Code n, codedResidueStageProgram O u n c = some d ∧
      HasRelativeResidue (Tower realModel n)
        (runStage O u (n+1) c).value (runStage O u n d).value ∧
      ∃ i : Nat, d = .root (stageResidueCoefficients O u n c) i ∧
        i < ((O.roots n).roots ((stagePolynomial u (stageResidueCoefficients O u n c)).map
          (rationalTowerHom n))).length := by
  letI := O.coefficientEquality n
  have hspec := stageAnnihilatorCodes_spec O u (n+1) c
  rw [codedResidueStageProgram_eq_rootProgram]
  exact codedResidueRootProgram_correct n n (stageInput u n) (rationalCoordinates n) (O.roots n)
    (Polynomial.Bivariate.swap (bivariatePolynomial u
      (clearedCodes u (stageAnnihilatorCodes O u (n+1) c))))
    (swappedClearedCodes_ne_zero u _ hspec.1.ne_zero)
    (stageResidueCoefficients O u n c)
    (normalizedResidueCoefficients_eval u _) hx (swappedClearedCodes_root u _ hspec.2)

structure CodedResidueOutput (O : ResidueOracles) (u : Fin 15 → ℝ) (n : Nat)
    (c : Code (n+1)) where
  code : Code n
  relativeResidue : HasRelativeResidue (Tower realModel n)
    (runStage O u (n+1) c).value (runStage O u n code).value
  selected : codedResidueStageProgram O u n c = some code

/-- Total execution only unwraps the result of a proven-successful finite list
selector. It never obtains a residue or a code by existential choice. -/
def executeCodedResidueStage (O : ResidueOracles) (u : Fin 15 → ℝ) (n : Nat)
    (c : Code (n+1))
    (hx : BaseBounded (Tower realModel n) (runStage O u (n+1) c).value) :
    CodedResidueOutput O u n c := by
  let out := codedResidueStageProgram O u n c
  have hs : out.isSome := by
    obtain ⟨d, hd, _, _⟩ := codedResidueStageProgram_correct O u n c hx
    simp only [out, hd, Option.isSome_some]
  let d := out.get hs
  have hprop : HasRelativeResidue (Tower realModel n)
      (runStage O u (n+1) c).value (runStage O u n d).value ∧
      codedResidueStageProgram O u n c = some d := by
    obtain ⟨q, hq, hr, _⟩ := codedResidueStageProgram_correct O u n c hx
    have heq : d = q := by simp only [d, out, hq, Option.get_some]
    simpa only [heq] using And.intro hr hq
  exact ⟨d, hprop.1, hprop.2⟩

theorem executeCodedResidueStage_is_root_code (O : ResidueOracles) (u : Fin 15 → ℝ)
    (n : Nat) (c : Code (n+1))
    (hx : BaseBounded (Tower realModel n) (runStage O u (n+1) c).value) :
    ∃ i : Nat, (executeCodedResidueStage O u n c hx).code =
      .root (stageResidueCoefficients O u n c) i ∧
      i < ((O.roots n).roots ((stagePolynomial u (stageResidueCoefficients O u n c)).map
        (rationalTowerHom n))).length := by
  obtain ⟨d, hd, _, hi⟩ := codedResidueStageProgram_correct O u n c hx
  have he : d = (executeCodedResidueStage O u n c hx).code :=
    Option.some.inj (hd.symm.trans (executeCodedResidueStage O u n c hx).selected)
  simpa only [he] using hi

/-- Exactly n code-producing residue stages, ending with a real-stage code. -/
def executeCodedSuccessiveResidues (O : ResidueOracles) (u : Fin 15 → ℝ) :
    (n : Nat) → (c : Code n) → (a b : ℝ) →
    baseEmbed realModel n a ≤ (runStage O u n c).value →
    (runStage O u n c).value ≤ baseEmbed realModel n b →
    {d : Code 0 // SuccessiveResidue n (runStage O u n c).value (runStage O u 0 d).value}
  | 0, c, _, _, _, _ => ⟨c, rfl⟩
  | n+1, c, a, b, ha, hb => by
    let step := executeCodedResidueStage O u n c (real_interval_baseBounded n ha hb)
    have hbounds := relativeResidue_interval (Tower realModel n) step.relativeResidue ha hb
    let rest := executeCodedSuccessiveResidues O u n step.code a b hbounds.1 hbounds.2
    exact ⟨rest.val, (runStage O u n step.code).value, step.relativeResidue, rest.property⟩

theorem executeCodedSuccessiveResidues_eq_stdPart (O : ResidueOracles) (u : Fin 15 → ℝ)
    (n : Nat) (c : Code n) (a b : ℝ)
    (ha : baseEmbed realModel n a ≤ (runStage O u n c).value)
    (hb : (runStage O u n c).value ≤ baseEmbed realModel n b) :
    (runStage O u 0 (executeCodedSuccessiveResidues O u n c a b ha hb).val).value =
      ArchimedeanClass.stdPart (runStage O u n c).value :=
  (successiveResidue_eq_stdPart n
    (executeCodedSuccessiveResidues O u n c a b ha hb).property).symm

/-- The code-retaining evaluator agrees with the already verified semantic
successive-residue executor on the directly interpreted source expression. -/
theorem executeCodedSuccessiveResidues_eq_executeSuccessiveResidues
    (O : ResidueOracles) (u : Fin 15 → ℝ) (n : Nat) (c : Code n) (a b : ℝ)
    (ha : baseEmbed realModel n a ≤ (runStage O u n c).value)
    (hb : (runStage O u n c).value ≤ baseEmbed realModel n b) :
    (runStage O u 0 (executeCodedSuccessiveResidues O u n c a b ha hb).val).value =
      (executeSuccessiveResidues O n (runStage O u n c).value
        (runStage O u n c).expression a b ha hb).val :=
  successiveResidue_unique n (executeCodedSuccessiveResidues O u n c a b ha hb).property
    (executeSuccessiveResidues O n (runStage O u n c).value
      (runStage O u n c).expression a b ha hb).property

/-- Explicit sixteen-stage specialization of the uniform executable recursion. -/
theorem executeCodedSixteenResidues_eq_stdPart (O : ResidueOracles) (u : Fin 15 → ℝ)
    (c : Code 16) (a b : ℝ)
    (ha : realEmbedding16 a ≤ (runStage O u 16 c).value)
    (hb : (runStage O u 16 c).value ≤ realEmbedding16 b) :
    (runStage O u 0 (executeCodedSuccessiveResidues O u 16 c a b ha hb).val).value =
      ArchimedeanClass.stdPart (runStage O u 16 c).value :=
  executeCodedSuccessiveResidues_eq_stdPart O u 16 c a b ha hb

#print axioms codedResidueStageProgram_correct
#print axioms executeCodedResidueStage
#print axioms executeCodedSixteenResidues_eq_stdPart
end W3.FiniteInput
