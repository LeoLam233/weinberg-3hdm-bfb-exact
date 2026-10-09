import W3.WeightedPair

noncomputable section
namespace W3.Weighted
open ComplexPair
section Field
variable {K : Type*} [Field K]

theorem complex_norm_mul (d q : ComplexPair K) : normSq (mul d q) = normSq d * normSq q := by
  unfold normSq mul
  ring

/-- The two discrete pair phase branches, without a square-root choice built
into the field. The caller supplies the positive norm root in a real closed field. -/
theorem pair_phase_real_branches (d q : ComplexPair K) (ρ : K)
    (hq : normSq q = 1) (hρ : ρ ^ 2 = normSq d) (hi : (mul d q).im = 0) :
    (mul d q).re = ρ ∨ (mul d q).re = -ρ := by
  have hn := complex_norm_mul d q
  rw [hq, mul_one, ← hρ] at hn
  unfold normSq at hn
  rw [hi] at hn
  have hf : ((mul d q).re - ρ) * ((mul d q).re + ρ) = 0 := by
    linear_combination hn
  rcases mul_eq_zero.mp hf with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

theorem phase_alignment_of_real_value (d q : ComplexPair K) (ρ : K)
    (hρ : ρ ≠ 0) (hn : normSq d = ρ ^ 2)
    (hi : (mul d q).im = 0) (hr : (mul d q).re = ρ) :
    q.re = d.re / ρ ∧ q.im = -d.im / ρ := by
  simp only [normSq, mul] at hn hi hr
  constructor
  · apply (eq_div_iff hρ).mpr
    apply mul_left_cancel₀ hρ
    linear_combination d.re * hr + d.im * hi - q.re * hn
  · apply (eq_div_iff hρ).mpr
    apply mul_left_cancel₀ hρ
    linear_combination -d.im * hr + d.re * hi - q.im * hn

/-- Exact pair phase formula q = sigma * conjugate(d) / |d|. -/
theorem pair_phase_alignment (d q : ComplexPair K) (ρ : K)
    (hq : normSq q = 1) (hρ : ρ ^ 2 = normSq d) (hρ₀ : ρ ≠ 0)
    (hi : (mul d q).im = 0) :
    (q.re = d.re / ρ ∧ q.im = -d.im / ρ ∧ (mul d q).re = ρ) ∨
    (q.re = -d.re / ρ ∧ q.im = d.im / ρ ∧ (mul d q).re = -ρ) := by
  rcases pair_phase_real_branches d q ρ hq hρ hi with hr | hr
  · obtain ⟨hx, hy⟩ := phase_alignment_of_real_value d q ρ hρ₀ hρ.symm hi hr
    exact Or.inl ⟨hx, hy, hr⟩
  · have hneg : normSq d = (-ρ) ^ 2 := by rw [neg_sq, hρ]
    obtain ⟨hx, hy⟩ := phase_alignment_of_real_value d q (-ρ) (neg_ne_zero.mpr hρ₀) hneg hi hr
    exact Or.inr ⟨by simpa only [div_neg, neg_div] using hx, by simpa only [div_neg, neg_div, neg_neg] using hy, hr⟩

/-- The constructed positive and negative phase branches both lie on the
unit circle and make the edge phase current vanish. -/
theorem pair_phase_construct (d : ComplexPair K) (ρ : K)
    (hρ : ρ ^ 2 = normSq d) (hρ₀ : ρ ≠ 0) :
    let q : ComplexPair K := ⟨d.re / ρ, -d.im / ρ⟩
    normSq q = 1 ∧ (mul d q).im = 0 ∧ (mul d q).re = ρ := by
  dsimp only
  constructor
  · unfold normSq
    dsimp only
    field_simp
    simpa [normSq] using hρ.symm
  constructor
  · simp only [mul]
    ring
  · simp only [mul]
    field_simp
    simpa [normSq] using hρ.symm
end Field
end W3.Weighted
