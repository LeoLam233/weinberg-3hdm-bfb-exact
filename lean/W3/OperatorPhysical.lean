import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The exact physical filter for a Hermitian 3×3 matrix with trace one and a kernel.
No positivity, spectral shape, or rank decomposition is assumed. -/
noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
namespace W3.Operator

theorem three_real_filter (x y z : ℝ) (htr : x + y + z = 1)
    (hdet : x * y * z = 0) :
    (0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z) ↔ x ^ 2 + y ^ 2 + z ^ 2 ≤ 1 := by
  constructor
  · rintro ⟨hx,hy,hz⟩
    nlinarith [mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz]
  · intro hp
    rcases mul_eq_zero.mp hdet with hxy | hz
    · rcases mul_eq_zero.mp hxy with hx | hy
      · subst x
        constructor
        · norm_num
        · constructor <;> nlinarith [sq_nonneg y, sq_nonneg z]
      · subst y
        constructor
        · nlinarith [sq_nonneg x, sq_nonneg z]
        · constructor
          · norm_num
          · nlinarith [sq_nonneg x, sq_nonneg z]
    · subst z
      constructor
      · nlinarith [sq_nonneg x, sq_nonneg y]
      · constructor
        · nlinarith [sq_nonneg x, sq_nonneg y]
        · norm_num

theorem three_spectrum_filter (e : Fin 3 → ℝ) (htr : ∑ i, e i = 1)
    (hdet : ∏ i, e i = 0) :
    (∀ i, 0 ≤ e i) ↔ (∑ i, e i ^ 2) ≤ 1 := by
  simp only [Fin.sum_univ_three, Fin.prod_univ_three] at *
  rw [show (∀ i, 0 ≤ e i) ↔ 0 ≤ e 0 ∧ 0 ≤ e 1 ∧ 0 ≤ e 2 by
    constructor
    · intro h; exact ⟨h 0,h 1,h 2⟩
    · rintro ⟨h0,h1,h2⟩ i; fin_cases i <;> assumption]
  exact three_real_filter _ _ _ htr hdet

lemma trace_square_eq_sum_eigenvalues {n : Type*} [Fintype n] [DecidableEq n]
    {K : Matrix n n ℂ} (hK : K.IsHermitian) :
    (K * K).trace = ∑ i, ((hK.eigenvalues i) ^ 2 : ℂ) := by
  conv_lhs => rw [hK.spectral_theorem, ← map_mul]
  simp [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.diagonal_mul_diagonal, pow_two]

/-- The scalar purity test is exact only after the singularity condition is established. -/
theorem physical_filter_of_det_zero (K : Matrix (Fin 3) (Fin 3) ℂ)
    (hK : K.IsHermitian) (htr : K.trace = 1) (hdet : K.det = 0) :
    K.PosSemidef ↔ (K * K).trace.re ≤ 1 := by
  have hetr : ∑ i, hK.eigenvalues i = 1 := by
    have h := congrArg Complex.re (hK.trace_eq_sum_eigenvalues.symm.trans htr)
    simpa using h
  have hedet : ∏ i, hK.eigenvalues i = 0 := by
    have h := hK.det_eq_prod_eigenvalues.symm.trans hdet
    simpa [Fin.prod_univ_three, Complex.mul_re, Complex.mul_im] using congrArg Complex.re h
  have hepur : (K * K).trace.re = ∑ i, hK.eigenvalues i ^ 2 := by
    rw [trace_square_eq_sum_eigenvalues hK]
    simp [← Complex.ofReal_pow]
  rw [hK.posSemidef_iff_eigenvalues_nonneg, hepur]
  exact three_spectrum_filter _ hetr hedet

/-- Nontrivial kernel version used directly in the charged reconstruction. -/
theorem physical_filter_of_kernel (K : Matrix (Fin 3) (Fin 3) ℂ)
    (hK : K.IsHermitian) (htr : K.trace = 1)
    (z : Fin 3 → ℂ) (hz : z ≠ 0) (hker : K *ᵥ z = 0) :
    K.PosSemidef ↔ (K * K).trace.re ≤ 1 := by
  apply physical_filter_of_det_zero K hK htr
  by_contra hdet
  apply hz
  exact (Matrix.mulVec_injective_of_det_ne_zero hdet) (by simpa using hker)

#print axioms physical_filter_of_kernel
end W3.Operator
