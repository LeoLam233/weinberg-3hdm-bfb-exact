import W3.Model
import W3.OperatorConcrete
import Mathlib.LinearAlgebra.BilinearMap

/-! Exact alignment between the full complex field model and the structured operator. -/
noncomputable section
namespace W3.Operator
open ComplexConjugate Matrix
open scoped BigOperators

/-- Real symmetric diagonal block of equation (20). -/
def couplingMatrix (κ : W3.Couplings) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![κ.a 0, κ.b 0, κ.b 1; κ.b 0, κ.a 1, κ.b 2; κ.b 1, κ.b 2, κ.a 2]

def couplingOperator (κ : W3.Couplings) : Coordinates →ₗ[ℝ] Coordinates :=
  structuredLinear (couplingMatrix κ) κ.c κ.d

def coordinatePair (x y : Coordinates) : ℝ :=
  (∑ i, x.1 i * y.1 i) +
    2 * ∑ i, ((x.2 i).re * (y.2 i).re + (x.2 i).im * (y.2 i).im)

lemma coordinatePair_symmetric (x y : Coordinates) : coordinatePair x y = coordinatePair y x := by
  simp only [coordinatePair, Fin.sum_univ_three]
  ring

def coordinateBilinear : Coordinates →ₗ[ℝ] Coordinates →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ coordinatePair
    (by intro x y z; simp [coordinatePair, Fin.sum_univ_three]; ring)
    (by intro r x z; simp [coordinatePair, Fin.sum_univ_three, Complex.smul_re, Complex.smul_im]; ring)
    (by intro x y z; simp [coordinatePair, Fin.sum_univ_three]; ring)
    (by intro r x z; simp [coordinatePair, Fin.sum_univ_three, Complex.smul_re, Complex.smul_im]; ring)

@[simp] theorem coordinateBilinear_apply (x y : Coordinates) :
    coordinateBilinear x y = coordinatePair x y := rfl

/-- The coordinate pairing is exactly the real Hermitian trace pairing. -/
theorem coordinatePair_eq_trace (x y : Coordinates) :
    coordinatePair x y = (coordinateMatrix x * coordinateMatrix y).trace.re := by
  simp [coordinatePair, coordinateMatrix, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_three, Complex.mul_re, Complex.mul_im]
  ring

/-- Self-adjointness with arbitrary complex coefficients d. -/
theorem couplingOperator_selfadjoint (κ : W3.Couplings) (x y : Coordinates) :
    coordinatePair x (couplingOperator κ y) = coordinatePair (couplingOperator κ x) y := by
  simp [coordinatePair, couplingOperator, structuredLinear, couplingMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, block, Complex.mul_re, Complex.mul_im]
  ring

def fieldCoordinates (φ : W3.Fields) : Coordinates :=
  (W3.radius φ, ![W3.gram φ 0 1, W3.gram φ 0 2, W3.gram φ 1 2])

lemma gram_conj_swap (φ : W3.Fields) (i j : Fin 3) :
    conj (W3.gram φ i j) = W3.gram φ j i := by
  simp [W3.gram, Fin.sum_univ_two, mul_comm]

theorem coordinateMatrix_fieldCoordinates (φ : W3.Fields) :
    coordinateMatrix (fieldCoordinates φ) = W3.gram φ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinateMatrix, fieldCoordinates, W3.gram_diag, gram_conj_swap]

def coordinateEnergy (κ : W3.Couplings) (x : Coordinates) : ℝ :=
  (∑ i, κ.a i * x.1 i ^ 2) / 2 +
  (κ.b 0 * x.1 0 * x.1 1 + κ.c 0 * Complex.normSq (x.2 0) + (κ.d 0 * x.2 0 ^ 2).re) +
  (κ.b 1 * x.1 0 * x.1 2 + κ.c 1 * Complex.normSq (x.2 1) + (κ.d 1 * x.2 1 ^ 2).re) +
  (κ.b 2 * x.1 1 * x.1 2 + κ.c 2 * Complex.normSq (x.2 2) + (κ.d 2 * x.2 2 ^ 2).re)

theorem coordinateEnergy_eq_half_pair (κ : W3.Couplings) (x : Coordinates) :
    coordinateEnergy κ x = coordinatePair x (couplingOperator κ x) / 2 := by
  simp [coordinateEnergy, coordinatePair, couplingOperator, structuredLinear, couplingMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, block, Complex.mul_re, Complex.mul_im,
    Complex.normSq_apply, pow_two]
  ring

@[simp] theorem quartic_eq_coordinateEnergy (κ : W3.Couplings) (φ : W3.Fields) :
    W3.quartic κ φ = coordinateEnergy κ (fieldCoordinates φ) := rfl

/-- Equation (20) is the exact quartic from Model.lean, not a new objective. -/
theorem quartic_eq_trace_operator (κ : W3.Couplings) (φ : W3.Fields) :
    W3.quartic κ φ =
      ((W3.gram φ : Matrix (Fin 3) (Fin 3) ℂ) * coordinateMatrix (couplingOperator κ (fieldCoordinates φ))).trace.re / 2 := by
  rw [quartic_eq_coordinateEnergy, coordinateEnergy_eq_half_pair, coordinatePair_eq_trace,
    coordinateMatrix_fieldCoordinates]

#print axioms quartic_eq_trace_operator
#print axioms couplingOperator_selfadjoint
end W3.Operator
