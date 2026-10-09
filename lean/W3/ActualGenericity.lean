import W3.RealPerturbation
import W3.EliminationElementary

/-! Genericity of the *actual* canonical deformation, including its correlated
trace-square shifts. No independent-genericity premise is assumed. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace W3.Infinitesimal
open MvPolynomial

/-- The fifteen affine-polynomial changes of the sixteen independent variables. -/
def deformationPolynomial (κ : Fin 15 → ℝ) (i : Fin 15) : MvPolynomial (Fin 16) ℝ :=
  C (κ i) + (if i.val < 6 then 2 * X 0 else 0) + X i.succ

def deformationSubstitution (κ : Fin 15 → ℝ) :
    MvPolynomial (Fin 15) ℝ →ₐ[ℝ] MvPolynomial (Fin 16) ℝ :=
  aeval (deformationPolynomial κ)

def deformationRetraction (κ : Fin 15 → ℝ) :
    MvPolynomial (Fin 16) ℝ →ₐ[ℝ] MvPolynomial (Fin 15) ℝ :=
  aeval (Fin.cons 0 (fun i => X i - C (κ i)))

lemma deformationSubstitution_leftInverse (κ : Fin 15 → ℝ) :
    Function.LeftInverse (deformationRetraction κ) (deformationSubstitution κ) := by
  have h : (deformationRetraction κ).comp (deformationSubstitution κ) = AlgHom.id ℝ _ := by
    ext i
    simp only [AlgHom.comp_apply, deformationSubstitution, aeval_X, deformationRetraction,
      deformationPolynomial, map_add, aeval_C]
    split_ifs <;> simp
  intro p
  exact congrArg (fun f : MvPolynomial (Fin 15) ℝ →ₐ[ℝ] MvPolynomial (Fin 15) ℝ => f p) h

/-- The unique canonical source deformation, including epsilon_0 trace-square. -/
def actualParameters (κ : Fin 15 → ℝ) : Fin 15 → SixteenLevelField :=
  W3.RealModel.deformedParameters (fun i => realEmbedding16 (κ i))
    (chronologicalEpsilon 0) coefficientEpsilon

lemma actualParameters_eval (κ : Fin 15 → ℝ) :
    letI : Algebra ℝ SixteenLevelField := towerAlgebra realModel 16
    aeval (actualParameters κ) =
      (aeval chronologicalEpsilon).comp (deformationSubstitution κ) := by
  letI : Algebra ℝ SixteenLevelField := towerAlgebra realModel 16
  ext i
  simp only [aeval_X, AlgHom.comp_apply, deformationSubstitution, deformationPolynomial,
    map_add, aeval_C, actualParameters, W3.RealModel.deformedParameters, coefficientEpsilon]
  split_ifs <;> simp
  all_goals rfl

/-- All fifteen deformed couplings are jointly independent in the actual field. -/
theorem actualParameters_algebraicIndependent (κ : Fin 15 → ℝ) :
    letI : Algebra ℝ SixteenLevelField := towerAlgebra realModel 16
    AlgebraicIndependent ℝ (actualParameters κ) := by
  letI : Algebra ℝ SixteenLevelField := towerAlgebra realModel 16
  rw [algebraicIndependent_iff_injective_aeval, actualParameters_eval]
  exact (show Function.Injective (aeval chronologicalEpsilon) from chronologicalEpsilon_algebraicIndependent).comp
    (deformationSubstitution_leftInverse κ).injective

/-- The complete primal, inverse and dual genericity conditions are now
unconditional for every original fifteen-real-coordinate input. -/
theorem actualParameters_generic (κ : Fin 15 → ℝ) :
    W3.Elimination.completeWeightedExceptional (W3.Elimination.originalPrimal (actualParameters κ)) ≠ 0 ∧
    W3.Elimination.originalInverseDen (actualParameters κ) ≠ 0 ∧
    W3.Elimination.completeWeightedExceptional (W3.Elimination.originalDual (actualParameters κ)) ≠ 0 := by
  letI : Algebra ℝ SixteenLevelField := towerAlgebra realModel 16
  have hi := actualParameters_algebraicIndependent κ
  exact ⟨W3.Elimination.completePrimal_ne_zero_of_independent _ hi,
    W3.Elimination.completeDual_ne_zero_of_independent _ hi⟩

#print axioms actualParameters_algebraicIndependent
#print axioms actualParameters_generic
end W3.Infinitesimal
