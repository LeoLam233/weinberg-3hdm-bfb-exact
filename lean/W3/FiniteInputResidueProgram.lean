import W3.FiniteInputResidueExecution

/-! Proof-free data flow for the fixed finite residue recursion. Bounds appear
only in its totality theorem; neither bounds nor their proofs are inputs to the
code-producing program. -/
noncomputable section
namespace W3.FiniteInput
open W3.Infinitesimal
attribute [local instance] rationalTowerAlgebra
set_option backward.isDefEq.respectTransparency false

def successiveResidueCodeProgram (O : ResidueOracles) (u : Fin 15 → ℝ) :
    (n : Nat) → Code n → Option (Code 0)
  | 0,c => some c
  | n+1,c => (codedResidueStageProgram O u n c).bind
      (successiveResidueCodeProgram O u n)

theorem successiveResidueCodeProgram_eq (O : ResidueOracles) (u : Fin 15 → ℝ)
    (n : Nat) (c : Code n) (a b : ℝ)
    (ha : baseEmbed realModel n a ≤ (runStage O u n c).value)
    (hb : (runStage O u n c).value ≤ baseEmbed realModel n b) :
    successiveResidueCodeProgram O u n c =
      some (executeCodedSuccessiveResidues O u n c a b ha hb).val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let step := executeCodedResidueStage O u n c (real_interval_baseBounded n ha hb)
    have hs := step.selected
    have hbounds := relativeResidue_interval (Tower realModel n) step.relativeResidue ha hb
    simp only [successiveResidueCodeProgram,hs,Option.bind_some]
    exact ih step.code hbounds.1 hbounds.2

theorem successiveResidueCodeProgram_correct (O : ResidueOracles) (u : Fin 15 → ℝ)
    (n : Nat) (c : Code n) (a b : ℝ)
    (ha : baseEmbed realModel n a ≤ (runStage O u n c).value)
    (hb : (runStage O u n c).value ≤ baseEmbed realModel n b) :
    ∃ d : Code 0, successiveResidueCodeProgram O u n c = some d ∧
      SuccessiveResidue n (runStage O u n c).value (runStage O u 0 d).value ∧
      (runStage O u 0 d).value = ArchimedeanClass.stdPart (runStage O u n c).value :=
  ⟨_,successiveResidueCodeProgram_eq O u n c a b ha hb,
    (executeCodedSuccessiveResidues O u n c a b ha hb).property,
    executeCodedSuccessiveResidues_eq_stdPart O u n c a b ha hb⟩

/-- Any successful bounded execution returns the unique successive residue. -/
theorem successiveResidueCodeProgram_result (O : ResidueOracles) (u : Fin 15 → ℝ)
    (n : Nat) (c : Code n) (a b : ℝ)
    (ha : baseEmbed realModel n a ≤ (runStage O u n c).value)
    (hb : (runStage O u n c).value ≤ baseEmbed realModel n b)
    (d : Code 0) (hd : successiveResidueCodeProgram O u n c = some d) :
    SuccessiveResidue n (runStage O u n c).value (runStage O u 0 d).value ∧
      (runStage O u 0 d).value = ArchimedeanClass.stdPart (runStage O u n c).value := by
  obtain ⟨e,he,hr,hs⟩ := successiveResidueCodeProgram_correct O u n c a b ha hb
  have hed : e=d := Option.some.inj (he.symm.trans hd)
  simpa only [hed] using And.intro hr hs

#print axioms successiveResidueCodeProgram_correct
end W3.FiniteInput
