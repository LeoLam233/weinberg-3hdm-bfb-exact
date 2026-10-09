import W3.Model
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

noncomputable section
open scoped BigOperators Matrix ComplexOrder
open ComplexConjugate
namespace W3

def fieldMatrix (φ : Fields) : Matrix (Fin 2) (Fin 3) ℂ := fun k i => φ (k,i)

lemma gram_matrix (φ : Fields) : gram φ = (fieldMatrix φ)ᴴ * fieldMatrix φ := by
  ext i j
  simp [gram, Matrix.mul_apply, fieldMatrix]

lemma gram_posSemidef (φ : Fields) : Matrix.PosSemidef (gram φ) := by
  rw [gram_matrix]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma gram_det_zero (φ : Fields) : Matrix.det (gram φ) = 0 := by
  simp [Matrix.det_fin_three, gram, Fin.sum_univ_two]
  ring

lemma gram_trace (φ : Fields) : Matrix.trace (gram φ) = (‖φ‖ ^ 2 : ℝ) := by
  simp only [Matrix.trace, Matrix.diag, gram_diag, ← Complex.ofReal_sum, total_radius]

/-- The 2-column complex Lagrange identity, proved as a polynomial identity. -/
lemma gram_cauchy_identity (φ : Fields) (i j : Fin 3) :
    radius φ i * radius φ j - Complex.normSq (gram φ i j) =
      Complex.normSq (φ (0,i) * φ (1,j) - φ (1,i) * φ (0,j)) := by
  simp [gram, radius, Fin.sum_univ_two, Complex.normSq]
  ring

lemma gram_normSq_le (φ : Fields) (i j : Fin 3) :
    Complex.normSq (gram φ i j) ≤ radius φ i * radius φ j := by
  have h := Complex.normSq_nonneg (φ (0,i) * φ (1,j) - φ (1,i) * φ (0,j))
  rw [← gram_cauchy_identity] at h
  linarith

lemma radius_le_one (φ : Fields) (hφ : ‖φ‖ = 1) (i : Fin 3) : radius φ i ≤ 1 := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => radius_nonneg φ j)
    (Finset.mem_univ i)
  simpa [total_radius, hφ] using h

lemma radius_pair_sum_le (φ : Fields) (hφ : ‖φ‖ = 1) (i j : Fin 3) (hij : i ≠ j) :
    radius φ i + radius φ j ≤ 1 := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (s := ({i,j} : Finset (Fin 3))) (t := Finset.univ)
    (by intro x _; exact Finset.mem_univ x)
    (fun k _ _ => radius_nonneg φ k)
  simpa [Finset.sum_pair hij, total_radius, hφ] using h

lemma radius_pair_le_quarter (φ : Fields) (hφ : ‖φ‖ = 1) (i j : Fin 3) (hij : i ≠ j) :
    radius φ i * radius φ j ≤ (1:ℝ)/4 := by
  have hi := radius_nonneg φ i
  have hj := radius_nonneg φ j
  have hs := radius_pair_sum_le φ hφ i j hij
  have hsq : (radius φ i + radius φ j)^2 ≤ 1 := by nlinarith
  nlinarith [sq_nonneg (radius φ i - radius φ j)]

lemma gram_normSq_le_quarter (φ : Fields) (hφ : ‖φ‖ = 1) (i j : Fin 3) (hij : i ≠ j) :
    Complex.normSq (gram φ i j) ≤ (1:ℝ)/4 :=
  (gram_normSq_le φ i j).trans (radius_pair_le_quarter φ hφ i j hij)

lemma abs_re_sq_le_normSq (z : ℂ) : |(z^2).re| ≤ Complex.normSq z := by
  rw [abs_le]
  simp [pow_two, Complex.normSq]
  constructor <;> nlinarith [sq_nonneg z.re, sq_nonneg z.im]

lemma abs_im_sq_le_normSq (z : ℂ) : |(z^2).im| ≤ Complex.normSq z := by
  rw [abs_le]
  simp [pow_two, Complex.normSq]
  constructor <;> nlinarith [sq_nonneg (z.re-z.im), sq_nonneg (z.re+z.im)]

#print axioms gram_posSemidef
#print axioms gram_normSq_le_quarter
end W3
