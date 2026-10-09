import W3.EliminationPhase
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic.FinCases

noncomputable section
namespace W3.Elimination
open Polynomial
variable {R : Type*} [CommRing R]

/-- Fixed-size Sylvester matrix for quadratics, in the Mathlib column convention. -/
def quadraticSylvester (a b c d e f : R) : Matrix (Fin 4) (Fin 4) R :=
  !![f, 0, c, 0; e, f, b, c; d, e, a, b; 0, d, 0, a]

theorem quadraticSylvester_det (a b c d e f : R) :
    (quadraticSylvester a b c d e f).det = resultant₂ a b c d e f := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply,
    quadraticSylvester, resultant₂, Fin.succAbove]
  ring

theorem quadratic_sylvester_eq (a b c d e f : R) :
    Polynomial.sylvester (quad (C a) (C b) (C c) X)
      (quad (C d) (C e) (C f) X) 2 2 = quadraticSylvester a b c d e f := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Polynomial.sylvester, quadraticSylvester, quad, coeff_add, coeff_C,
      coeff_C_mul, coeff_X_pow, Fin.addCases, coeff_X]

/-- Bridge from the explicit eliminant to the library's determinant resultant. -/
theorem resultant₂_eq_resultant (a b c d e f : R) :
    resultant₂ a b c d e f =
      Polynomial.resultant (quad (C a) (C b) (C c) X)
        (quad (C d) (C e) (C f) X) 2 2 := by
  rw [Polynomial.resultant, quadratic_sylvester_eq, quadraticSylvester_det]

end W3.Elimination
