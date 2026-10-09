import W3.WeightedAlgebraicityCanonical
import W3.OperatorFieldTwoSpectrum
import W3.InfinitesimalSuccessiveResidue

/-! Unconditional algebraic presentation and finite sixteen-step extraction of
the actual selected minimum. -/
noncomputable section
namespace W3.Weighted
open W3.Elimination W3.Infinitesimal W3.OperatorField W3.RealModel

theorem actual_deformedMinimum_algebraic (κ : Parameters ℝ) :
    letI := rationalTowerAlgebra 16
    IsAlgebraic (RationalTower 16) (deformedMinimum κ) :=
  actual_twoSpectrum_value_algebraic κ (actualParameters_generic κ).2.2 _
    (deformedMinimum_mem_actualCandidateValues κ)

theorem actual_candidateMinimum_algebraic (κ : Parameters ℝ) :
    letI := rationalTowerAlgebra 16
    IsAlgebraic (RationalTower 16) (actualCandidateMinimum κ) := by
  rw [actualCandidateMinimum_eq]
  exact actual_deformedMinimum_algebraic κ

/-- The selected scalar supplies its own nonzero annihilating polynomial. -/
theorem actual_candidateMinimum_annihilator (κ : Parameters ℝ) :
    letI := rationalTowerAlgebra 16
    ∃ p : Polynomial (RationalTower 16), p ≠ 0 ∧
      Polynomial.aeval (actualCandidateMinimum κ) p = 0 :=
  actual_candidateMinimum_algebraic κ

/-- The root chosen from the explicit at-most-thirty list admits all sixteen
preceding-field residues, and their endpoint is exactly the original minimum. -/
theorem actual_minimum_successiveResidue (κ : Parameters ℝ) :
    SuccessiveResidue 16 (deformedMinimum κ) (realMinimum κ) := by
  have hb := abs_le.mp (actual_minimum_bound κ)
  have hd := nine_halves_epsilon_one_lt_zero
  have he0 := (chronologicalEpsilon_infinitesimal 0).1
  have hehalf : chronologicalEpsilon 0 < (1/2 : SixteenLevelField) := by
    simpa only [map_div₀,map_one,map_ofNat] using
      (chronologicalEpsilon_infinitesimal 0).2 (1/2) (by norm_num)
  have ha : realEmbedding16 (realMinimum κ-1) ≤ deformedMinimum κ := by
    rw [map_sub,map_one]
    linarith
  have hz : deformedMinimum κ ≤ realEmbedding16 (realMinimum κ+1) := by
    rw [map_add,map_one]
    linarith
  obtain ⟨r,_,_,hr⟩ := successiveResidue_exists 16 ha hz (actual_deformedMinimum_algebraic κ)
  have he : r=realMinimum κ := (successiveResidue_eq_stdPart 16 hr).symm.trans
    (actual_minimum_signs_and_residue κ).2.2.2.2
  exact he ▸ hr

/-- The literal finite-list minimum has that same finite algebraic extraction. -/
theorem actual_candidateMinimum_successiveResidue (κ : Parameters ℝ) :
    SuccessiveResidue 16 (actualCandidateMinimum κ) (realMinimum κ) := by
  rw [actualCandidateMinimum_eq]
  exact actual_minimum_successiveResidue κ

#print axioms actual_candidateMinimum_annihilator
#print axioms actual_deformedMinimum_algebraic
#print axioms actual_minimum_successiveResidue
#print axioms actual_candidateMinimum_successiveResidue
end W3.Weighted
