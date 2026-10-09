import W3.WeightedAmplitude

noncomputable section
namespace W3.Weighted
open ComplexPair
section Ring
variable {K : Type*} [CommRing K]

def zeroAmplitude : ComplexPair K := ⟨0, 0⟩
@[simp] theorem zeroAmplitude_re : (zeroAmplitude : ComplexPair K).re = 0 := rfl
@[simp] theorem zeroAmplitude_im : (zeroAmplitude : ComplexPair K).im = 0 := rfl

@[simp] theorem normSq_zeroAmplitude : normSq (zeroAmplitude : ComplexPair K) = 0 := by
  simp [zeroAmplitude, normSq]
@[simp] theorem amplitudeEdge_zero_right (d z : ComplexPair K) :
    amplitudeEdge d z zeroAmplitude = zeroAmplitude := by
  simp [amplitudeEdge, zeroAmplitude, mul, conj]
@[simp] theorem amplitudeEdge_zero_left (d z : ComplexPair K) :
    amplitudeEdge d zeroAmplitude z = zeroAmplitude := by
  simp [amplitudeEdge, zeroAmplitude, mul, conj]

def PairAmplitudeEquations (a b e : K) (d z₁ z₂ : ComplexPair K) (g₁ g₂ lam : K) : Prop :=
  normSq z₁ * (a * normSq z₁ + e * normSq z₂) + (amplitudeEdge d z₁ z₂).re = lam * g₁ * normSq z₁ ∧
  normSq z₂ * (e * normSq z₁ + b * normSq z₂) + (amplitudeEdge d z₁ z₂).re = lam * g₂ * normSq z₂ ∧
  (amplitudeEdge d z₁ z₂).im = 0

theorem amplitude_support₁₂ (k : SpectrumData K) (z₁ z₂ : ComplexPair K) (g₁ g₂ g₃ lam : K)
    (he : AmplitudeEquations k z₁ z₂ zeroAmplitude g₁ g₂ g₃ lam) :
    PairAmplitudeEquations k.a₁ k.a₂ k.e₁₂ k.d₁₂ z₁ z₂ g₁ g₂ lam := by
  have h₁ := congrArg ComplexPair.re he.1
  have h₂ := congrArg ComplexPair.re he.2.1
  have hi := congrArg ComplexPair.im he.2.1
  refine ⟨?_, ?_, ?_⟩
  · simpa only [amplitudeRow₁, normSq_zeroAmplitude, amplitudeEdge_zero_left, amplitudeEdge_zero_right, zeroAmplitude_re, zeroAmplitude_im, mul_zero, zero_mul, add_zero, zero_add, sub_zero] using h₁
  · simpa only [amplitudeRow₂, normSq_zeroAmplitude, amplitudeEdge_zero_left, amplitudeEdge_zero_right, zeroAmplitude_re, zeroAmplitude_im, mul_zero, zero_mul, add_zero, zero_add, sub_zero] using h₂
  · simpa only [amplitudeRow₂, normSq_zeroAmplitude, amplitudeEdge_zero_left, amplitudeEdge_zero_right, zeroAmplitude_re, zeroAmplitude_im, mul_zero, zero_mul, add_zero, zero_add, sub_zero] using hi

theorem amplitude_support₁₃ (k : SpectrumData K) (z₁ z₃ : ComplexPair K) (g₁ g₂ g₃ lam : K)
    (he : AmplitudeEquations k z₁ zeroAmplitude z₃ g₁ g₂ g₃ lam) :
    PairAmplitudeEquations k.a₁ k.a₃ k.e₁₃ k.d₁₃ z₁ z₃ g₁ g₃ lam := by
  have h₁ := congrArg ComplexPair.re he.1
  have h₃ := congrArg ComplexPair.re he.2.2
  have hi := congrArg ComplexPair.im he.2.2
  refine ⟨?_, ?_, ?_⟩
  · simpa only [amplitudeRow₁, normSq_zeroAmplitude, amplitudeEdge_zero_left, amplitudeEdge_zero_right, zeroAmplitude_re, zeroAmplitude_im, mul_zero, zero_mul, add_zero, zero_add, sub_zero] using h₁
  · simpa only [amplitudeRow₃, normSq_zeroAmplitude, amplitudeEdge_zero_left, amplitudeEdge_zero_right, zeroAmplitude_re, zeroAmplitude_im, mul_zero, zero_mul, add_zero, zero_add, sub_zero] using h₃
  · simpa only [amplitudeRow₃, normSq_zeroAmplitude, amplitudeEdge_zero_left, amplitudeEdge_zero_right, zeroAmplitude_re, zeroAmplitude_im, mul_zero, zero_mul, add_zero, zero_add, sub_zero] using hi

theorem amplitude_support₂₃ (k : SpectrumData K) (z₂ z₃ : ComplexPair K) (g₁ g₂ g₃ lam : K)
    (he : AmplitudeEquations k zeroAmplitude z₂ z₃ g₁ g₂ g₃ lam) :
    PairAmplitudeEquations k.a₂ k.a₃ k.e₂₃ k.d₂₃ z₂ z₃ g₂ g₃ lam := by
  have h₂ := congrArg ComplexPair.re he.2.1
  have h₃ := congrArg ComplexPair.re he.2.2
  have hi := congrArg ComplexPair.im he.2.2
  refine ⟨?_, ?_, ?_⟩
  · simpa only [amplitudeRow₂, normSq_zeroAmplitude, amplitudeEdge_zero_left, amplitudeEdge_zero_right, zeroAmplitude_re, zeroAmplitude_im, mul_zero, zero_mul, add_zero, zero_add, sub_zero] using h₂
  · simpa only [amplitudeRow₃, normSq_zeroAmplitude, amplitudeEdge_zero_left, amplitudeEdge_zero_right, zeroAmplitude_re, zeroAmplitude_im, mul_zero, zero_mul, add_zero, zero_add, sub_zero] using h₃
  · simpa only [amplitudeRow₃, normSq_zeroAmplitude, amplitudeEdge_zero_left, amplitudeEdge_zero_right, zeroAmplitude_re, zeroAmplitude_im, mul_zero, zero_mul, add_zero, zero_add, sub_zero] using hi
end Ring

section Field
variable {K : Type*} [Field K] [CharZero K]

/-- Pair-support eigen-equations give the exact two phase branches and radial
stationarity. This uses no invertibility of the pair amplitude matrix. -/
theorem pair_amplitude_radial (a b e : K) (d z₁ z₂ : ComplexPair K) (g₁ g₂ lam : K)
    (h₁ : normSq z₁ ≠ 0) (h₂ : normSq z₂ ≠ 0)
    (hG : g₁ * normSq z₁ + g₂ * normSq z₂ ≠ 0)
    (he : PairAmplitudeEquations a b e d z₁ z₂ g₁ g₂ lam) :
    let q := relativePhase z₁ z₂
    (mul d q).im = 0 ∧
    PairRadialEquations (a / 2) (b / 2) ((e + (mul d q).re) / 2)
      g₁ g₂ (normSq z₁) (normSq z₂) (lam / (2 * (g₁ * normSq z₁ + g₂ * normSq z₂))) := by
  dsimp only
  have hedge := amplitudeEdge_phase₁₂ d z₁ z₂ h₁ h₂
  rcases he with ⟨hr₁, hr₂, hi⟩
  rw [hedge] at hr₁ hr₂ hi
  simp only [scale] at hr₁ hr₂ hi
  have hs : (mul d (relativePhase z₁ z₂)).im = 0 :=
    (mul_eq_zero.mp hi).resolve_left (mul_ne_zero h₁ h₂)
  have hbr₁ : a * normSq z₁ + (e + (mul d (relativePhase z₁ z₂)).re) * normSq z₂ = lam * g₁ := by
    apply mul_left_cancel₀ h₁
    linear_combination hr₁
  have hbr₂ : (e + (mul d (relativePhase z₁ z₂)).re) * normSq z₁ + b * normSq z₂ = lam * g₂ := by
    apply mul_left_cancel₀ h₂
    linear_combination hr₂
  have hcoeff : lam / (2 * (g₁ * normSq z₁ + g₂ * normSq z₂)) *
      (g₁ * normSq z₁ + g₂ * normSq z₂) = lam / 2 := by
    rw [div_mul_eq_div_div, div_mul_cancel₀ _ hG]
  refine ⟨hs, ?_, ?_⟩
  · rw [hcoeff]
    linear_combination (1 / 2 : K) * hbr₁
  · rw [hcoeff]
    linear_combination (1 / 2 : K) * hbr₂

end Field
end W3.Weighted
