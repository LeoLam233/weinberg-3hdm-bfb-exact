import W3.WeightedAlgebraicityCompiled
import W3.InfinitesimalResidueExecution
import W3.TransferOperatorResidue

/-! Oracle-relative execution on the literal selected minimum and matrices.
All scalar bounds depend only on the given coefficients, never on an unknown
minimum or an extra annihilating polynomial. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace W3.Weighted.Expression
open W3.Elimination W3.Infinitesimal W3.OperatorField W3.TransferOperator W3.RealModel
open scoped BigOperators
local instance : Algebra (RationalTower 16) SixteenLevelField := rationalTowerAlgebra 16

/-- A directly computable magnitude bound from the fifteen input coefficients. -/
def inputMagnitudeBound (κ : Parameters ℝ) : ℝ := (∑ i, |κ i|)+1

lemma quarticReal_sum_monomials {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (κ : Parameters K) (x : RealFields K) : quarticReal κ x = ∑ i,κ i*monomials x i := by
  simp [quarticReal,twiceQuartic,monomials,Fin.sum_univ_succ]
  ring

lemma quarticReal_abs_bound {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (κ : Parameters K) (x : RealFields K) (hx : mass x=1) :
    |quarticReal κ x| ≤ ∑ i,|κ i| := by
  rw [quarticReal_sum_monomials]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  have hm : |monomials x i| ≤ 1 := (monomials_bound x hx i).trans (by
    unfold monomialBound
    split_ifs <;> norm_num)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hm (abs_nonneg (κ i))

/-- The scalar chosen from the finite list lies in an input-only real interval. -/
theorem actualCandidateMinimum_input_bound (κ : Parameters ℝ) :
    realEmbedding16 (-inputMagnitudeBound κ) ≤ actualCandidateMinimum κ ∧
      actualCandidateMinimum κ ≤ realEmbedding16 (inputMagnitudeBound κ) := by
  rw [actualCandidateMinimum_eq]
  have hm := abs_le.mp (quarticReal_abs_bound κ (realMinimumPoint κ) (realMinimumPoint_spec κ).1)
  change -(∑ i,|κ i|) ≤ realMinimum κ ∧ realMinimum κ ≤ ∑ i,|κ i| at hm
  have hml : realEmbedding16 (-(∑ i,|κ i|)) ≤ realEmbedding16 (realMinimum κ) :=
    realEmbedding16.monotone' hm.1
  have hmu : realEmbedding16 (realMinimum κ) ≤ realEmbedding16 (∑ i,|κ i|) :=
    realEmbedding16.monotone' hm.2
  rw [map_neg] at hml
  have hb := abs_le.mp (actual_minimum_bound κ)
  have hd := nine_halves_epsilon_one_lt_zero
  have he0 := (chronologicalEpsilon_infinitesimal 0).1
  have hehalf : chronologicalEpsilon 0 < (1/2 : SixteenLevelField) := by
    simpa only [map_div₀,map_one,map_ofNat] using
      (chronologicalEpsilon_infinitesimal 0).2 (1/2) (by norm_num)
  unfold inputMagnitudeBound
  rw [map_neg,map_add,map_one]
  constructor <;> linarith

/-- Run the finite determinant/normalization/root-comparison procedure exactly
sixteen times on the actual selected scalar expression. -/
def executeActualMinimum (O : ResidueOracles) (κ : Parameters ℝ) : ℝ :=
  (executeSuccessiveResidues O 16 (actualCandidateMinimum κ) (actualMinimumExpression κ)
    (-inputMagnitudeBound κ) (inputMagnitudeBound κ)
    (actualCandidateMinimum_input_bound κ).1 (actualCandidateMinimum_input_bound κ).2).val

/-- Complete scalar effectiveness endpoint: the finite oracle-relative program
returns the original global normalized minimum for every input. -/
theorem executeActualMinimum_eq (O : ResidueOracles) (κ : Parameters ℝ) :
    executeActualMinimum O κ = realMinimum κ := by
  rw [executeActualMinimum,executeSuccessiveResidues_eq_stdPart,actualCandidateMinimum_eq]
  exact (actual_minimum_signs_and_residue κ).2.2.2.2

/-- Actual neutral-coordinate execution uses the supplied physical bound and
retains exactly the selected projector root branch. -/
def executePrimalCoordinate (O : ResidueOracles) (κ : Parameters ℝ)
    (hp : completeWeightedExceptional (originalPrimal (actualParameters κ)) ≠ 0)
    (j : CandidateIndex (originalPrimal (actualParameters κ)))
    (hb : MatrixBounded (hermitianProjector (candidateVector _ hp j))) (i : Fin 9) : ℝ :=
  (executeSuccessiveResidues O 16 _ (actualPrimalCoordinateExpression κ hp j i) (-1) 1
    (by simpa only [map_neg,map_one] using (hb i).1)
    (by simpa only [map_one] using (hb i).2)).val

theorem executePrimalCoordinate_eq (O : ResidueOracles) (κ : Parameters ℝ)
    (hp : completeWeightedExceptional (originalPrimal (actualParameters κ)) ≠ 0)
    (j : CandidateIndex (originalPrimal (actualParameters κ)))
    (hb : MatrixBounded (hermitianProjector (candidateVector _ hp j))) (i : Fin 9) :
    executePrimalCoordinate O κ hp j hb i =
      residueMatrix9 (hermitianProjector (candidateVector _ hp j)) hb i := by
  rw [executePrimalCoordinate,executeSuccessiveResidues_eq_stdPart,residueMatrix9_eq_stdPart]

/-- Actual charged-coordinate execution after the exact physical filter. -/
def executeDualCoordinate (O : ResidueOracles) (κ : Parameters ℝ)
    (hd : completeWeightedExceptional (originalDual (actualParameters κ)) ≠ 0)
    (j : CandidateIndex (originalDual (actualParameters κ)))
    (hb : MatrixBounded (dualCoordinates (actualParameters κ) (candidateVector _ hd j))) (i : Fin 9) : ℝ :=
  (executeSuccessiveResidues O 16 _ (actualDualCoordinateExpression κ hd j i) (-1) 1
    (by simpa only [map_neg,map_one] using (hb i).1)
    (by simpa only [map_one] using (hb i).2)).val

theorem executeDualCoordinate_eq (O : ResidueOracles) (κ : Parameters ℝ)
    (hd : completeWeightedExceptional (originalDual (actualParameters κ)) ≠ 0)
    (j : CandidateIndex (originalDual (actualParameters κ)))
    (hb : MatrixBounded (dualCoordinates (actualParameters κ) (candidateVector _ hd j))) (i : Fin 9) :
    executeDualCoordinate O κ hd j hb i =
      residueMatrix9 (dualCoordinates (actualParameters κ) (candidateVector _ hd j)) hb i := by
  rw [executeDualCoordinate,executeSuccessiveResidues_eq_stdPart,residueMatrix9_eq_stdPart]

#print axioms executeActualMinimum_eq
#print axioms executePrimalCoordinate_eq
#print axioms executeDualCoordinate_eq
end W3.Weighted.Expression
