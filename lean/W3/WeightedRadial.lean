import W3.WeightedPhase

noncomputable section
namespace W3.Weighted
open W3.Elimination
section Field
variable {K : Type*} [Field K]

/-- Vanishing weighted cross components is equivalent to radial
proportionality with exactly the coefficient obtained by contraction. -/
theorem radial_proportionality_iff (r₁ r₂ r₃ g₁ g₂ g₃ b₁ b₂ b₃ : K)
    (hg₁ : g₁ ≠ 0) (hG : g₁ * r₁ + g₂ * r₂ + g₃ * r₃ ≠ 0) :
    (g₁ * b₂ - g₂ * b₁ = 0 ∧ g₁ * b₃ - g₃ * b₁ = 0) ↔
    (b₁ = ((r₁ * b₁ + r₂ * b₂ + r₃ * b₃) / (g₁ * r₁ + g₂ * r₂ + g₃ * r₃)) * g₁ ∧
     b₂ = ((r₁ * b₁ + r₂ * b₂ + r₃ * b₃) / (g₁ * r₁ + g₂ * r₂ + g₃ * r₃)) * g₂ ∧
     b₃ = ((r₁ * b₁ + r₂ * b₂ + r₃ * b₃) / (g₁ * r₁ + g₂ * r₂ + g₃ * r₃)) * g₃) := by
  constructor
  · rintro ⟨h₂, h₃⟩
    have h₁ : b₁ * (g₁ * r₁ + g₂ * r₂ + g₃ * r₃) =
        (r₁ * b₁ + r₂ * b₂ + r₃ * b₃) * g₁ := by
      linear_combination -r₂ * h₂ - r₃ * h₃
    refine ⟨?_, ?_, ?_⟩
    · rw [div_mul_eq_mul_div]
      exact (eq_div_iff hG).mpr h₁
    · rw [div_mul_eq_mul_div]
      apply (eq_div_iff hG).mpr
      apply mul_left_cancel₀ hg₁
      linear_combination g₂ * h₁ + (g₁ * r₁ + g₂ * r₂ + g₃ * r₃) * h₂
    · rw [div_mul_eq_mul_div]
      apply (eq_div_iff hG).mpr
      apply mul_left_cancel₀ hg₁
      linear_combination g₃ * h₁ + (g₁ * r₁ + g₂ * r₂ + g₃ * r₃) * h₃
  · rintro ⟨h₁, h₂, h₃⟩
    constructor
    · linear_combination g₁ * h₂ - g₂ * h₁
    · linear_combination g₁ * h₃ - g₃ * h₁

def weightedQuotient (k : SpectrumData K) (q v : ComplexPair K)
    (g₁ g₂ g₃ r₁ r₂ r₃ : K) : K :=
  (r₁ * twiceB₁ k q v r₁ r₂ r₃ + r₂ * twiceB₂ k q v r₁ r₂ r₃ +
    r₃ * twiceB₃ k q v r₁ r₂ r₃) / (2 * (g₁ * r₁ + g₂ * r₂ + g₃ * r₃) ^ 2)

/-- The algebraic Euler equations for the actual quotient (4). -/
def FullRadialEquations (k : SpectrumData K) (q v : ComplexPair K)
    (g₁ g₂ g₃ r₁ r₂ r₃ : K) : Prop :=
  let ν := weightedQuotient k q v g₁ g₂ g₃ r₁ r₂ r₃
  let G := g₁ * r₁ + g₂ * r₂ + g₃ * r₃
  twiceB₁ k q v r₁ r₂ r₃ = 2 * ν * G * g₁ ∧
  twiceB₂ k q v r₁ r₂ r₃ = 2 * ν * G * g₂ ∧
  twiceB₃ k q v r₁ r₂ r₃ = 2 * ν * G * g₃

/-- The two phase-row equations from Eq. (15). -/
def ReducedRadialEquations (k : SpectrumData K) (q v : ComplexPair K) (g₁ g₂ g₃ : K) : Prop :=
  rowImag (rowDifference g₁ g₂ (cRow₁ k) (cRow₂ k)) q v = 0 ∧
  rowImag (rowDifference g₁ g₃ (cRow₁ k) (cRow₃ k)) q v = 0

theorem twiceB_reconstructed₁ (k : SpectrumData K) (q v : ComplexPair K) (D : K) :
    twiceB₁ k q v ((edge₂₃ k q v).im / D) (-(edge₁₃ k v).im / D) ((edge₁₂ k q).im / D) =
      rowImag (cRow₁ k) q v / D := by
  rw [← current_matrix_identity₁]
  unfold twiceB₁
  ring

theorem twiceB_reconstructed₂ (k : SpectrumData K) (q v : ComplexPair K) (D : K)
    (hq : ComplexPair.normSq q = 1) :
    twiceB₂ k q v ((edge₂₃ k q v).im / D) (-(edge₁₃ k v).im / D) ((edge₁₂ k q).im / D) =
      rowImag (cRow₂ k) q v / D := by
  rw [← current_matrix_identity₂ k q v hq]
  unfold twiceB₂
  ring

theorem twiceB_reconstructed₃ (k : SpectrumData K) (q v : ComplexPair K) (D : K)
    (hv : ComplexPair.normSq v = 1) :
    twiceB₃ k q v ((edge₂₃ k q v).im / D) (-(edge₁₃ k v).im / D) ((edge₁₂ k q).im / D) =
      rowImag (cRow₃ k) q v / D := by
  rw [← current_matrix_identity₃ k q v hv]
  unfold twiceB₃
  ring

variable [CharZero K]

theorem full_radial_cross_iff (k : SpectrumData K) (q v : ComplexPair K)
    (g₁ g₂ g₃ r₁ r₂ r₃ : K) (hg₁ : g₁ ≠ 0)
    (hG : g₁ * r₁ + g₂ * r₂ + g₃ * r₃ ≠ 0) :
    FullRadialEquations k q v g₁ g₂ g₃ r₁ r₂ r₃ ↔
    (g₁ * twiceB₂ k q v r₁ r₂ r₃ - g₂ * twiceB₁ k q v r₁ r₂ r₃ = 0 ∧
     g₁ * twiceB₃ k q v r₁ r₂ r₃ - g₃ * twiceB₁ k q v r₁ r₂ r₃ = 0) := by
  have hcoeff : 2 * weightedQuotient k q v g₁ g₂ g₃ r₁ r₂ r₃ *
      (g₁ * r₁ + g₂ * r₂ + g₃ * r₃) =
      (r₁ * twiceB₁ k q v r₁ r₂ r₃ + r₂ * twiceB₂ k q v r₁ r₂ r₃ +
       r₃ * twiceB₃ k q v r₁ r₂ r₃) / (g₁ * r₁ + g₂ * r₂ + g₃ * r₃) := by
    unfold weightedQuotient
    field_simp
    <;> ring
  unfold FullRadialEquations
  dsimp only
  rw [hcoeff]
  exact (radial_proportionality_iff _ _ _ _ _ _ _ _ _ hg₁ hG).symm

/-- Central bridge: after exact amplitude reconstruction, both radial
Euler equations are equivalent to the two phase equations (15). -/
theorem reconstructed_radial_iff (k : SpectrumData K) (q v : ComplexPair K)
    (g₁ g₂ g₃ D : K) (hq : ComplexPair.normSq q = 1) (hv : ComplexPair.normSq v = 1)
    (hg₁ : g₁ ≠ 0) (hD : D ≠ 0)
    (hG : g₁ * ((edge₂₃ k q v).im / D) + g₂ * (-(edge₁₃ k v).im / D) +
      g₃ * ((edge₁₂ k q).im / D) ≠ 0) :
    FullRadialEquations k q v g₁ g₂ g₃
      ((edge₂₃ k q v).im / D) (-(edge₁₃ k v).im / D) ((edge₁₂ k q).im / D) ↔
      ReducedRadialEquations k q v g₁ g₂ g₃ := by
  rw [full_radial_cross_iff _ _ _ _ _ _ _ _ _ hg₁ hG]
  rw [twiceB_reconstructed₁, twiceB_reconstructed₂ k q v D hq,
    twiceB_reconstructed₃ k q v D hv]
  unfold ReducedRadialEquations
  rw [rowDifference_imag, rowDifference_imag]
  have h (a b c d : K) : a * (b / D) - c * (d / D) = 0 ↔ a * b - c * d = 0 := by
    rw [← mul_div_assoc, ← mul_div_assoc, ← sub_div, div_eq_zero_iff]
    simp [hD]
  exact and_congr (h _ _ _ _) (h _ _ _ _)

end Field
end W3.Weighted
