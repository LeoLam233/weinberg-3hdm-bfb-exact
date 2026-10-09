import W3.WeightedAlgebraicityExpressionsMinimum
import W3.InfinitesimalExpressionCompiler

/-! Concrete power-product-basis annihilators emitted from the selected weighted
spectrum expressions. No additional finite-dimensional presentation is assumed. -/
noncomputable section
namespace W3.Weighted.Expression
open W3.Elimination W3.Infinitesimal W3.OperatorField W3.TransferOperator W3.RealModel
local instance : Algebra (RationalTower 16) SixteenLevelField := rationalTowerAlgebra 16
local instance : DecidableEq (RationalTower 16) := Classical.decEq _

/-- A finite syntax retaining the actually selected minimum and all root branches. -/
def actualMinimumExpression (κ : Parameters ℝ) :
    RootExpression (RationalTower 16) SixteenLevelField (actualCandidateMinimum κ) :=
  Classical.choice (actual_candidateMinimum_presented κ)

/-- The exact multiplication-table determinant emitted by the recursive compiler. -/
def actualMinimumAnnihilator (κ : Parameters ℝ) : Polynomial (RationalTower 16) := by
  classical
  exact (actualMinimumExpression κ).annihilator

/-- Monicity, nonzero polynomial, exact selected-root identity and a literal
finite degree all follow from the constructed quotient basis. -/
theorem actualMinimumAnnihilator_spec (κ : Parameters ℝ) :
    (actualMinimumAnnihilator κ).Monic ∧ actualMinimumAnnihilator κ ≠ 0 ∧
    Polynomial.aeval (actualCandidateMinimum κ) (actualMinimumAnnihilator κ)=0 ∧
    (actualMinimumAnnihilator κ).natDegree =
      Fintype.card (actualMinimumExpression κ).compile.presentation.Index := by
  classical
  exact ⟨(actualMinimumExpression κ).annihilator_spec.1,
    (actualMinimumExpression κ).annihilator_ne_zero,
    (actualMinimumExpression κ).annihilator_spec.2,
    (actualMinimumExpression κ).annihilator_degree⟩

/-- Each selected neutral projector coordinate retains a finite syntax. -/
def actualPrimalCoordinateExpression (κ : Parameters ℝ)
    (hp : completeWeightedExceptional (originalPrimal (actualParameters κ)) ≠ 0)
    (j : CandidateIndex (originalPrimal (actualParameters κ))) (i : Fin 9) :
    RootExpression (RationalTower 16) SixteenLevelField
      (hermitianProjector (candidateVector _ hp j) i) :=
  Classical.choice (actual_primal_candidate_presented κ hp j i)

/-- Each selected reconstructed charged coordinate retains a finite syntax. -/
def actualDualCoordinateExpression (κ : Parameters ℝ)
    (hd : completeWeightedExceptional (originalDual (actualParameters κ)) ≠ 0)
    (j : CandidateIndex (originalDual (actualParameters κ))) (i : Fin 9) :
    RootExpression (RationalTower 16) SixteenLevelField
      (dualCoordinates (actualParameters κ) (candidateVector _ hd j) i) :=
  Classical.choice ((actual_dual_candidate_presented κ hd j).1 i)

/-- The emitted neutral-coordinate polynomial is monic and vanishes at the
actual selected entry, including entries on singleton and pair faces. -/
theorem actualPrimalCoordinate_compiled (κ : Parameters ℝ)
    (hp : completeWeightedExceptional (originalPrimal (actualParameters κ)) ≠ 0)
    (j : CandidateIndex (originalPrimal (actualParameters κ))) (i : Fin 9) :
    let e := actualPrimalCoordinateExpression κ hp j i
    e.annihilator.Monic ∧
      Polynomial.aeval (hermitianProjector (candidateVector _ hp j) i) e.annihilator=0 := by
  classical
  exact (actualPrimalCoordinateExpression κ hp j i).annihilator_spec

/-- The same emitted-polynomial guarantee for actual charged reconstruction. -/
theorem actualDualCoordinate_compiled (κ : Parameters ℝ)
    (hd : completeWeightedExceptional (originalDual (actualParameters κ)) ≠ 0)
    (j : CandidateIndex (originalDual (actualParameters κ))) (i : Fin 9) :
    let e := actualDualCoordinateExpression κ hd j i
    e.annihilator.Monic ∧
      Polynomial.aeval (dualCoordinates (actualParameters κ) (candidateVector _ hd j) i) e.annihilator=0 := by
  classical
  exact (actualDualCoordinateExpression κ hd j i).annihilator_spec

#print axioms actualMinimumAnnihilator_spec
#print axioms actualPrimalCoordinate_compiled
#print axioms actualDualCoordinate_compiled
end W3.Weighted.Expression
