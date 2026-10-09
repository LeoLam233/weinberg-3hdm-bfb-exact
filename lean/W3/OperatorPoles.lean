import W3.WeightedSupports
import W3.EliminationStationary
import W3.EliminationElementary

/-! All-support exclusion of the weighted pole for genuine amplitude
stationarity, using the explicit nonzero generic polynomials. -/
noncomputable section
namespace W3.Weighted
open ComplexPair W3.Elimination
section Ordered
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

lemma normSq_eq_zeroAmplitude (z : ComplexPair K) (h : normSq z = 0) : z = zeroAmplitude := by
  apply complexPair_ext <;> simp only [zeroAmplitude_re, zeroAmplitude_im]
  · unfold normSq at h
    nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  · unfold normSq at h
    nlinarith [sq_nonneg z.re, sq_nonneg z.im]

/-- Pair pole exclusion before forming any quotient, including zero eigenvalue. -/
theorem pair_amplitude_weight_ne_zero (a b e : K) (d z₁ z₂ : ComplexPair K)
    (g₁ g₂ lam : K) (h₁ : normSq z₁ ≠ 0) (h₂ : normSq z₂ ≠ 0)
    (hex : pairExceptional a b e d.re d.im g₁ g₂ ≠ 0)
    (he : PairAmplitudeEquations a b e d z₁ z₂ g₁ g₂ lam) :
    g₁ * normSq z₁ + g₂ * normSq z₂ ≠ 0 := by
  have hedge := amplitudeEdge_phase₁₂ d z₁ z₂ h₁ h₂
  rcases he with ⟨hr₁,hr₂,hi⟩
  rw [hedge] at hr₁ hr₂ hi
  simp only [scale] at hr₁ hr₂ hi
  have hphase : (mul d (relativePhase z₁ z₂)).im = 0 :=
    (mul_eq_zero.mp hi).resolve_left (mul_ne_zero h₁ h₂)
  have hm : (mul d (relativePhase z₁ z₂)).re ^ 2 = d.re ^ 2 + d.im ^ 2 := by
    have h := complex_norm_mul d (relativePhase z₁ z₂)
    rw [relativePhase_norm z₁ z₂ h₁ h₂, mul_one] at h
    simpa [normSq, hphase] using h
  intro hpole
  have hp : (a/2) * normSq z₁ ^ 2 + (e + (mul d (relativePhase z₁ z₂)).re) *
      normSq z₁ * normSq z₂ + (b/2) * normSq z₂ ^ 2 = 0 := by
    linear_combination (1/2 : K) * hr₁ + (1/2 : K) * hr₂ + (lam/2) * hpole
  exact pair_phase_zero_excludes_pole a b e d.re d.im g₁ g₂ _ _ _ hm hex h₁ hp hpole

/-- Full support pole exclusion uses the two radial cross equations, without
assuming or dividing by a nonzero weighted normalization. -/
theorem full_amplitude_weight_ne_zero (w : WeightedData K)
    (hexc : weightedExceptional w ≠ 0) (hloop : weightedLoop w ≠ 0)
    (z₁ z₂ z₃ : ComplexPair K) (lam : K)
    (h₁ : normSq z₁ ≠ 0) (h₂ : normSq z₂ ≠ 0) (h₃ : normSq z₃ ≠ 0)
    (hn : normSq z₁ + normSq z₂ + normSq z₃ = 1)
    (he : AmplitudeEquations (toSpectrum w) z₁ z₂ z₃ w.g1 w.g2 w.g3 lam) :
    w.g1 * normSq z₁ + w.g2 * normSq z₂ + w.g3 * normSq z₃ ≠ 0 := by
  obtain ⟨hc,hr₁,hr₂,hr₃⟩ :=
    (amplitude_equations_iff (toSpectrum w) z₁ z₂ z₃ w.g1 w.g2 w.g3 lam h₁ h₂ h₃).mp he
  apply full_support_cross_excludes_pole w hexc (relativePhase z₁ z₂) (relativePhase z₁ z₃)
    (normSq z₁) (normSq z₂) (normSq z₃)
    (relativePhase_norm z₁ z₂ h₁ h₂) (relativePhase_norm z₁ z₃ h₁ h₃)
    hloop h₁ h₂ h₃ hn hc
  · rw [hr₁,hr₂]; ring
  · rw [hr₁,hr₃]; ring

/-- Exhaustive singleton, pair and full-support generic pole exclusion. This is
an explicit polynomial certificate replacing the informal incidence count. -/
theorem generic_amplitude_weight_ne_zero (w : WeightedData K)
    (hex : completeWeightedExceptional w ≠ 0)
    (z₁ z₂ z₃ : ComplexPair K) (lam : K)
    (hn : normSq z₁ + normSq z₂ + normSq z₃ = 1)
    (he : AmplitudeEquations (toSpectrum w) z₁ z₂ z₃ w.g1 w.g2 w.g3 lam) :
    w.g1 * normSq z₁ + w.g2 * normSq z₂ + w.g3 * normSq z₃ ≠ 0 := by
  obtain ⟨hphase,helem⟩ := mul_ne_zero_iff.mp hex
  obtain ⟨hloop,hg₁,hg₂,hg₃,hgs,hp₁₂,hp₁₃,hp₂₃⟩ := elementaryExceptional_properties w helem
  by_cases h₁ : normSq z₁ = 0
  · have hz₁ := normSq_eq_zeroAmplitude z₁ h₁
    subst z₁
    by_cases h₂ : normSq z₂ = 0
    · have hz₂ := normSq_eq_zeroAmplitude z₂ h₂
      subst z₂
      have hn₃ : normSq z₃ = 1 := by simpa using hn
      simpa [hn₃] using hg₃
    · by_cases h₃ : normSq z₃ = 0
      · have hz₃ := normSq_eq_zeroAmplitude z₃ h₃
        subst z₃
        have hn₂ : normSq z₂ = 1 := by simpa using hn
        simpa [hn₂] using hg₂
      · simpa only [normSq_zeroAmplitude, mul_zero, zero_add] using
          pair_amplitude_weight_ne_zero w.alpha2 w.alpha3 w.e23 ⟨w.d23r,w.d23i⟩ z₂ z₃
            w.g2 w.g3 lam h₂ h₃ hp₂₃ (amplitude_support₂₃ _ _ _ _ _ _ _ he)
  · by_cases h₂ : normSq z₂ = 0
    · have hz₂ := normSq_eq_zeroAmplitude z₂ h₂
      subst z₂
      by_cases h₃ : normSq z₃ = 0
      · have hz₃ := normSq_eq_zeroAmplitude z₃ h₃
        subst z₃
        have hn₁ : normSq z₁ = 1 := by simpa using hn
        simpa [hn₁] using hg₁
      · simpa only [normSq_zeroAmplitude, mul_zero, add_zero] using
          pair_amplitude_weight_ne_zero w.alpha1 w.alpha3 w.e13 ⟨w.d13r,w.d13i⟩ z₁ z₃
            w.g1 w.g3 lam h₁ h₃ hp₁₃ (amplitude_support₁₃ _ _ _ _ _ _ _ he)
    · by_cases h₃ : normSq z₃ = 0
      · have hz₃ := normSq_eq_zeroAmplitude z₃ h₃
        subst z₃
        simpa only [normSq_zeroAmplitude, mul_zero, add_zero] using
          pair_amplitude_weight_ne_zero w.alpha1 w.alpha2 w.e12 ⟨w.d12r,w.d12i⟩ z₁ z₂
            w.g1 w.g2 lam h₁ h₂ hp₁₂ (amplitude_support₁₂ _ _ _ _ _ _ _ he)
      · exact full_amplitude_weight_ne_zero w hphase hloop z₁ z₂ z₃ lam h₁ h₂ h₃ hn he

#print axioms generic_amplitude_weight_ne_zero
end Ordered
end W3.Weighted
