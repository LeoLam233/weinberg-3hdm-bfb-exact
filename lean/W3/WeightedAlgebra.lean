import W3.EliminationPhase

/-! Algebraic common weighted spectrum, over arbitrary coefficient fields.
Complex quantities are represented by two field coordinates, so these proofs
apply without a real/complex analytic transfer to an ordered extension. -/
noncomputable section
namespace W3.Weighted

structure ComplexPair (K : Type*) where
  re : K
  im : K

namespace ComplexPair
variable {K : Type*} [CommRing K]
def mul (z w : ComplexPair K) : ComplexPair K :=
  ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩
def conj (z : ComplexPair K) : ComplexPair K := ⟨z.re, -z.im⟩
def scale (a : K) (z : ComplexPair K) : ComplexPair K := ⟨a * z.re, a * z.im⟩
def sub (z w : ComplexPair K) : ComplexPair K := ⟨z.re - w.re, z.im - w.im⟩
def normSq (z : ComplexPair K) : K := z.re ^ 2 + z.im ^ 2

theorem mul_assoc (z w v : ComplexPair K) : mul (mul z w) v = mul z (mul w v) := by
  cases z; cases w; cases v; simp only [mul]; congr 1 <;> ring

theorem loop_identity (a b c q p : ComplexPair K) :
    (mul (mul (mul a q) (mul c (mul p (conj q)))) (conj (mul b p))).im =
      (mul (mul a c) (conj b)).im * normSq q * normSq p := by
  simp only [mul, conj, normSq]
  ring

theorem loop_invariant (a b c q p : ComplexPair K)
    (hq : normSq q = 1) (hp : normSq p = 1) :
    (mul (mul (mul a q) (mul c (mul p (conj q)))) (conj (mul b p))).im =
      (mul (mul a c) (conj b)).im := by
  rw [loop_identity, hq, hp, mul_one, mul_one]

/-- Nonreal loop coupling excludes simultaneous zero phase currents. -/
theorem nonreal_loop_excludes_zero (a b c q p : ComplexPair K)
    (hq : normSq q = 1) (hp : normSq p = 1)
    (hloop : (mul (mul a c) (conj b)).im ≠ 0) :
    ¬ ((mul a q).im = 0 ∧ (mul b p).im = 0 ∧
       (mul c (mul p (conj q))).im = 0) := by
  rintro ⟨ha, hb, hc⟩
  apply hloop
  rw [← loop_invariant a b c q p hq hp]
  simp only [mul, conj] at ha hb hc ⊢
  rw [ha, hb, hc]
  ring
end ComplexPair

section Currents
variable {K : Type*} [Field K]

/-- Equation (9), including its signs and the common current. -/
def CurrentEquations (r₁ r₂ r₃ s₁₂ s₁₃ s₂₃ : K) : Prop :=
  r₁ * r₂ * s₁₂ = r₂ * r₃ * s₂₃ ∧
  r₂ * r₃ * s₂₃ = -(r₁ * r₃ * s₁₃)

/-- A full-support phase-stationary point has nonzero current if the three
edge currents cannot all vanish. No positivity or ordered-field axiom is used. -/
theorem nonzero_common_current (r₁ r₂ r₃ s₁₂ s₁₃ s₂₃ : K)
    (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0) (h₃ : r₃ ≠ 0)
    (hc : CurrentEquations r₁ r₂ r₃ s₁₂ s₁₃ s₂₃)
    (hn : ¬ (s₁₂ = 0 ∧ s₁₃ = 0 ∧ s₂₃ = 0)) :
    r₂ * r₃ * s₂₃ ≠ 0 := by
  intro hz
  apply hn
  have hs₂₃ : s₂₃ = 0 := (mul_eq_zero.mp hz).resolve_left (mul_ne_zero h₂ h₃)
  have hs₁₂ : s₁₂ = 0 := (mul_eq_zero.mp (hc.1.trans hz)).resolve_left (mul_ne_zero h₁ h₂)
  have hs₁₃ : s₁₃ = 0 := by
    have h : r₁ * r₃ * s₁₃ = 0 := neg_eq_zero.mp (hc.2.symm.trans hz)
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero h₁ h₃)
  exact ⟨hs₁₂, hs₁₃, hs₂₃⟩

/-- Exact amplitude elimination, equation (11), including proof that its
normalizing denominator is nonzero. -/
theorem current_reconstruction (r₁ r₂ r₃ s₁₂ s₁₃ s₂₃ : K)
    (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0) (h₃ : r₃ ≠ 0)
    (hsum : r₁ + r₂ + r₃ = 1)
    (hc : CurrentEquations r₁ r₂ r₃ s₁₂ s₁₃ s₂₃)
    (hn : ¬ (s₁₂ = 0 ∧ s₁₃ = 0 ∧ s₂₃ = 0)) :
    s₂₃ - s₁₃ + s₁₂ ≠ 0 ∧
    r₁ = s₂₃ / (s₂₃ - s₁₃ + s₁₂) ∧
    r₂ = -s₁₃ / (s₂₃ - s₁₃ + s₁₂) ∧
    r₃ = s₁₂ / (s₂₃ - s₁₃ + s₁₂) := by
  have hcur := nonzero_common_current r₁ r₂ r₃ s₁₂ s₁₃ s₂₃ h₁ h₂ h₃ hc hn
  have hs₂₃ : s₂₃ ≠ 0 := fun h => hcur (by rw [h, mul_zero])
  have he₁ : r₁ * s₁₂ = r₃ * s₂₃ := by
    apply mul_left_cancel₀ h₂
    linear_combination hc.1
  have he₂ : r₂ * s₂₃ = -(r₁ * s₁₃) := by
    apply mul_left_cancel₀ h₃
    linear_combination hc.2
  have he₃ : r₂ * s₁₂ = -(r₃ * s₁₃) := by
    apply mul_left_cancel₀ h₁
    linear_combination r₂ * he₁ + r₃ * he₂
  have hr₁ : r₁ * (s₂₃ - s₁₃ + s₁₂) = s₂₃ := by
    linear_combination s₂₃ * hsum + he₁ - he₂
  have hr₂ : r₂ * (s₂₃ - s₁₃ + s₁₂) = -s₁₃ := by
    linear_combination -s₁₃ * hsum + he₂ + he₃
  have hr₃ : r₃ * (s₂₃ - s₁₃ + s₁₂) = s₁₂ := by
    linear_combination s₁₂ * hsum - he₁ - he₃
  have hden : s₂₃ - s₁₃ + s₁₂ ≠ 0 := by
    intro h
    apply hs₂₃
    simpa [h] using hr₁.symm
  exact ⟨hden, (eq_div_iff hden).mpr hr₁, (eq_div_iff hden).mpr hr₂,
    (eq_div_iff hden).mpr hr₃⟩

/-- Conversely the reconstructed amplitudes satisfy both phase equations. -/
theorem reconstructed_current_equations (s₁₂ s₁₃ s₂₃ : K) :
    CurrentEquations (s₂₃ / (s₂₃ - s₁₃ + s₁₂))
      (-s₁₃ / (s₂₃ - s₁₃ + s₁₂)) (s₁₂ / (s₂₃ - s₁₃ + s₁₂)) s₁₂ s₁₃ s₂₃ := by
  constructor <;> ring

end Currents
end W3.Weighted
