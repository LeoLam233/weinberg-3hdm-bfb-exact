import W3.Operator
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-! Concrete nine-real-coordinate realization of the general Weinberg operator.
The diagonal block is any invertible real 3×3 matrix; the Hermitian realization
and support lemmas require no genericity or nonzero field components. -/
noncomputable section
namespace W3.Operator
open ComplexConjugate Matrix
open scoped BigOperators

abbrev Coordinates := (Fin 3 → ℝ) × (Fin 3 → ℂ)

def coordinateMatrix (x : Coordinates) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(x.1 0 : ℂ), x.2 0, x.2 1;
     conj (x.2 0), (x.1 1 : ℂ), x.2 2;
     conj (x.2 1), conj (x.2 2), (x.1 2 : ℂ)]

theorem coordinateMatrix_hermitian (x : Coordinates) :
    (coordinateMatrix x).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coordinateMatrix, Matrix.conjTranspose_apply]

/-- Extraction of the nine Hermitian coordinates, also defined on arbitrary matrices. -/
def matrixCoordinates (K : Matrix (Fin 3) (Fin 3) ℂ) : Coordinates :=
  (fun i => (K i i).re, ![K 0 1, K 0 2, K 1 2])

@[simp] theorem matrixCoordinates_coordinateMatrix (x : Coordinates) :
    matrixCoordinates (coordinateMatrix x) = x := by
  apply Prod.ext <;> funext i <;> fin_cases i <;> simp [matrixCoordinates, coordinateMatrix]

theorem coordinateMatrix_injective : Function.Injective coordinateMatrix := by
  intro x y h
  have h' := congrArg matrixCoordinates h
  simpa using h'

def blockLinear (c : ℝ) (d : ℂ) : ℂ →ₗ[ℝ] ℂ where
  toFun := block c d
  map_add' := by intro z w; simp [block, mul_add]; ring
  map_smul' := by intro r z; simp [block, Complex.real_smul]; ring

def coordinateMatrixLinear : Coordinates →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℂ where
  toFun := coordinateMatrix
  map_add' := by
    intro x y; ext i j
    fin_cases i <;> fin_cases j <;> simp [coordinateMatrix]
  map_smul' := by
    intro t x; ext i j
    fin_cases i <;> fin_cases j <;> simp [coordinateMatrix]

@[simp] theorem coordinateMatrixLinear_apply (x : Coordinates) :
    coordinateMatrixLinear x = coordinateMatrix x := rfl

/-- Equation (20) in unrestricted Hermitian coordinates. -/
def structuredLinear (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)
    (d : Fin 3 → ℂ) : Coordinates →ₗ[ℝ] Coordinates where
  toFun x := (A *ᵥ x.1, fun i => block (c i) (d i) (x.2 i))
  map_add' := by
    intro x y
    apply Prod.ext
    · exact Matrix.mulVec_add A x.1 y.1
    · funext i; exact (blockLinear (c i) (d i)).map_add _ _
  map_smul' := by
    intro r x
    apply Prod.ext
    · exact Matrix.mulVec_smul A r x.1
    · funext i; exact (blockLinear (c i) (d i)).map_smul r _

/-- Equation (21), with the actual nonsingular matrix inverse. -/
def structuredInverse (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)
    (d : Fin 3 → ℂ) (x : Coordinates) : Coordinates :=
  (A⁻¹ *ᵥ x.1, fun i => inverseBlock (c i) (d i) (x.2 i))

theorem structured_left_inverse (A : Matrix (Fin 3) (Fin 3) ℝ)
    (c : Fin 3 → ℝ) (d : Fin 3 → ℂ) (hA : A.det ≠ 0)
    (hΔ : ∀ i, blockDet (c i) (d i) ≠ 0) :
    Function.LeftInverse (structuredInverse A c d) (structuredLinear A c d) := by
  intro x
  apply Prod.ext
  · change A⁻¹ *ᵥ (A *ᵥ x.1) = x.1
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA),
      Matrix.one_mulVec]
  · funext i
    exact inverseBlock_block (c i) (d i) (x.2 i) (hΔ i)

theorem structured_right_inverse (A : Matrix (Fin 3) (Fin 3) ℝ)
    (c : Fin 3 → ℝ) (d : Fin 3 → ℂ) (hA : A.det ≠ 0)
    (hΔ : ∀ i, blockDet (c i) (d i) ≠ 0) :
    Function.RightInverse (structuredInverse A c d) (structuredLinear A c d) := by
  intro x
  apply Prod.ext
  · change A *ᵥ (A⁻¹ *ᵥ x.1) = x.1
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA),
      Matrix.one_mulVec]
  · funext i
    exact block_inverseBlock (c i) (d i) (x.2 i) (hΔ i)

def structuredEquiv (A : Matrix (Fin 3) (Fin 3) ℝ)
    (c : Fin 3 → ℝ) (d : Fin 3 → ℂ) (hA : A.det ≠ 0)
    (hΔ : ∀ i, blockDet (c i) (d i) ≠ 0) : Coordinates ≃ₗ[ℝ] Coordinates :=
  { structuredLinear A c d with
    invFun := structuredInverse A c d
    left_inv := structured_left_inverse A c d hA hΔ
    right_inv := structured_right_inverse A c d hA hΔ }

@[simp] theorem structuredEquiv_symm_apply (A : Matrix (Fin 3) (Fin 3) ℝ)
    (c : Fin 3 → ℝ) (d : Fin 3 → ℂ) (hA : A.det ≠ 0)
    (hΔ : ∀ i, blockDet (c i) (d i) ≠ 0) (x : Coordinates) :
    (structuredEquiv A c d hA hΔ).symm x = structuredInverse A c d x := rfl

def identityCoordinates : Coordinates := (fun _ => 1, fun _ => 0)

@[simp] theorem coordinateMatrix_identity : coordinateMatrix identityCoordinates = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coordinateMatrix, identityCoordinates]

theorem inverse_identity_diagonal (A : Matrix (Fin 3) (Fin 3) ℝ)
    (c : Fin 3 → ℝ) (d : Fin 3 → ℂ) :
    coordinateMatrix (structuredInverse A c d identityCoordinates) =
      Matrix.diagonal (fun i => ((A⁻¹ *ᵥ (fun _ => 1)) i : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinateMatrix, structuredInverse, identityCoordinates, inverseBlock]

/-- The inverse identity has no vector kernel when every component of G1 is nonzero. -/
lemma inverse_identity_action_ne_zero (A : Matrix (Fin 3) (Fin 3) ℝ)
    (c : Fin 3 → ℝ) (d : Fin 3 → ℂ) (z : Fin 3 → ℂ) (hz : z ≠ 0)
    (hg : ∀ i, (A⁻¹ *ᵥ (fun _ => 1)) i ≠ 0) :
    coordinateMatrix (structuredInverse A c d identityCoordinates) *ᵥ z ≠ 0 := by
  rw [inverse_identity_diagonal]
  intro h
  apply hz
  funext i
  have hi := congrFun h i
  simp only [Matrix.mulVec_diagonal, Pi.zero_apply] at hi
  exact (mul_eq_zero.mp hi).resolve_left (Complex.ofReal_ne_zero.mpr (hg i))

/-- Rank-one projector coordinates use P=z z†. -/
def projectorCoordinates (z : Fin 3 → ℂ) : Coordinates :=
  (fun i => Complex.normSq (z i), ![z 0 * conj (z 1), z 0 * conj (z 2), z 1 * conj (z 2)])

def projector (z : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => z i * conj (z j)

theorem coordinateMatrix_projector (z : Fin 3 → ℂ) :
    coordinateMatrix (projectorCoordinates z) = projector z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinateMatrix, projectorCoordinates, projector, Complex.mul_conj, mul_comm]

/-- Corrected support statement: diagonal mixing may fill a zero diagonal, but
 the corresponding component of (R P)z still vanishes. -/
theorem inverse_projector_zero_component (A : Matrix (Fin 3) (Fin 3) ℝ)
    (c : Fin 3 → ℝ) (d : Fin 3 → ℂ) (z : Fin 3 → ℂ) (i : Fin 3)
    (hi : z i = 0) :
    (coordinateMatrix (structuredInverse A c d (projectorCoordinates z)) *ᵥ z) i = 0 := by
  fin_cases i <;> dsimp at hi <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, coordinateMatrix,
      structuredInverse, projectorCoordinates, inverseBlock, hi]

#print axioms structuredEquiv
#print axioms inverse_projector_zero_component
end W3.Operator
