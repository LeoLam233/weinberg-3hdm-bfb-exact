import W3.WeightedSpectrum
import Mathlib.FieldTheory.IsRealClosed.Basic

/-! Algebraic square-root realization of candidate phases and radii, over any
ordered real closed coefficient field, without using ℂ or transcendental phases. -/
noncomputable section
namespace W3.Weighted
open ComplexPair
section RealClosed
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]

theorem exists_nonnegative_sqrt (r : K) (hr : 0 ≤ r) : ∃ a : K, 0 ≤ a ∧ a ^ 2 = r := by
  obtain ⟨s, hs⟩ := (IsSquare.of_nonneg hr : IsSquare r)
  exact ⟨|s|, abs_nonneg _, by simpa [sq_abs, pow_two] using hs.symm⟩

theorem exists_positive_sqrt (r : K) (hr : 0 < r) : ∃ a : K, 0 < a ∧ a ^ 2 = r := by
  obtain ⟨a, ha, hs⟩ := exists_nonnegative_sqrt r hr.le
  refine ⟨a, lt_of_le_of_ne ha ?_, hs⟩
  intro he
  rw [← he] at hs
  nlinarith

/-- Every nonnegative radius and algebraic unit phase has a squared-amplitude
representative. The chosen z corresponds to source z=conjugate(w). -/
theorem phase_radius_realization (r : K) (q : ComplexPair K)
    (hr : 0 ≤ r) (hq : normSq q = 1) :
    ∃ z : ComplexPair K, normSq z = r ∧ conj (mul z z) = scale r q := by
  have hn : q.re ^ 2 + q.im ^ 2 = 1 := hq
  by_cases hr0 : r = 0
  · refine ⟨⟨0,0⟩, ?_, ?_⟩
    · simp [normSq, hr0]
    · apply complexPair_ext <;> simp [mul, conj, scale, hr0]
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  by_cases hminus : q.re = -1
  · have hi : q.im = 0 := by rw [hminus] at hn; nlinarith [sq_nonneg q.im]
    obtain ⟨b, hb, hb2⟩ := exists_nonnegative_sqrt r hr
    refine ⟨⟨0, -b⟩, ?_, ?_⟩
    · simp [normSq, hb2]
    · apply complexPair_ext <;> simp [mul, conj, scale, hminus, hi, ← hb2] <;> ring
  have hre : 0 < 1 + q.re := by
    have hb : -1 ≤ q.re := by nlinarith [sq_nonneg q.im, sq_nonneg (q.re + 1)]
    have hnz : 1 + q.re ≠ 0 := by intro he; apply hminus; linear_combination he
    exact lt_of_le_of_ne (by linarith) (Ne.symm hnz)
  obtain ⟨a, ha, ha2⟩ := exists_positive_sqrt (r * (1 + q.re) / 2) (div_pos (mul_pos hrp hre) (by norm_num))
  have ha0 := ne_of_gt ha
  let b := r * q.im / (2 * a)
  have hb2 : b ^ 2 = r * (1 - q.re) / 2 := by
    dsimp [b]
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 2 (mul_ne_zero (by norm_num) ha0))).mpr
    linear_combination r ^ 2 * hn - 2 * r * (1 - q.re) * ha2
  have hab : 2 * a * b = r * q.im := by
    dsimp [b]
    field_simp [ha0]
  refine ⟨⟨a, -b⟩, ?_, ?_⟩
  · simp only [normSq, neg_sq]
    rw [ha2, hb2]
    ring
  · apply complexPair_ext
    · simp only [conj, mul, scale]
      nlinarith [ha2, hb2]
    · simp only [conj, mul, scale]
      linear_combination hab

/-- Every unit-circle point has a unit squared-amplitude representative. -/
theorem phase_realization (q : ComplexPair K) (hq : normSq q = 1) :
    ∃ z : ComplexPair K, normSq z = 1 ∧ amplitudeUnit z = q := by
  obtain ⟨z, hn, hs⟩ := phase_radius_realization 1 q zero_le_one hq
  refine ⟨z, hn, ?_⟩
  unfold amplitudeUnit
  rw [hn, inv_one, hs]
  apply complexPair_ext <;> simp [scale]


/-- Normalizing a nonzero represented radius recovers its exact unit phase. -/
theorem amplitudeUnit_of_square (r : K) (q z : ComplexPair K)
    (hr : r ≠ 0) (hn : normSq z = r) (hs : conj (mul z z) = scale r q) :
    amplitudeUnit z = q := by
  unfold amplitudeUnit
  rw [hn, hs]
  apply complexPair_ext <;> simp [scale, hr]

/-- Every positive full-support candidate has actual squared-amplitude
representatives, rather than merely formal phase/radius coordinates. -/
theorem full_point_realization (x : SpectrumPoint K)
    (h₁ : 0 < x.r₁) (h₂ : 0 < x.r₂) (h₃ : 0 < x.r₃)
    (hq : normSq x.q = 1) (hv : normSq x.v = 1) :
    ∃ z₁ z₂ z₃ : ComplexPair K, amplitudePoint z₁ z₂ z₃ = x := by
  have ho : normSq (onePhase : ComplexPair K) = 1 := by simp [onePhase, normSq]
  obtain ⟨z₁, hn₁, hs₁⟩ := phase_radius_realization x.r₁ onePhase h₁.le ho
  obtain ⟨z₂, hn₂, hs₂⟩ := phase_radius_realization x.r₂ x.q h₂.le hq
  obtain ⟨z₃, hn₃, hs₃⟩ := phase_radius_realization x.r₃ x.v h₃.le hv
  have hu₁ := amplitudeUnit_of_square _ _ _ (ne_of_gt h₁) hn₁ hs₁
  have hu₂ := amplitudeUnit_of_square _ _ _ (ne_of_gt h₂) hn₂ hs₂
  have hu₃ := amplitudeUnit_of_square _ _ _ (ne_of_gt h₃) hn₃ hs₃
  refine ⟨z₁, z₂, z₃, ?_⟩
  apply spectrumPoint_ext
  · exact hn₁
  · exact hn₂
  · exact hn₃
  · change relativePhase z₁ z₂ = x.q
    rw [relativePhase, hu₁, hu₂]
    apply complexPair_ext <;> simp [onePhase, mul, conj]
  · change relativePhase z₁ z₃ = x.v
    rw [relativePhase, hu₁, hu₃]
    apply complexPair_ext <;> simp [onePhase, mul, conj]

/-- Soundness of retained full-support roots includes a normalized stationary
amplitude witness in the same real closed field. -/
theorem fullCandidates_realizable (w : W3.Elimination.WeightedData K)
    (he : W3.Elimination.weightedExceptional w ≠ 0) (hg₁ : w.g1 ≠ 0)
    (x : SpectrumPoint K) (hm : x ∈ fullCandidates w) :
    ∃ z₁ z₂ z₃ : ComplexPair K, ∃ lam : K,
      amplitudePoint z₁ z₂ z₃ = x ∧ normSq z₁ + normSq z₂ + normSq z₃ = 1 ∧
      AmplitudeEquations (W3.Elimination.toSpectrum w) z₁ z₂ z₃ w.g1 w.g2 w.g3 lam := by
  obtain ⟨hq,hv,h₁,h₂,h₃,hsum,hG,hstat⟩ := fullCandidates_sound w he hg₁ x hm
  obtain ⟨z₁,z₂,z₃,hx⟩ := full_point_realization x h₁ h₂ h₃ hq hv
  have hn₁ : normSq z₁ = x.r₁ := congrArg SpectrumPoint.r₁ hx
  have hn₂ : normSq z₂ = x.r₂ := congrArg SpectrumPoint.r₂ hx
  have hn₃ : normSq z₃ = x.r₃ := congrArg SpectrumPoint.r₃ hx
  have hq' : relativePhase z₁ z₂ = x.q := congrArg SpectrumPoint.q hx
  have hv' : relativePhase z₁ z₃ = x.v := congrArg SpectrumPoint.v hx
  have hG' : w.g1 * normSq z₁ + w.g2 * normSq z₂ + w.g3 * normSq z₃ ≠ 0 := by
    simpa [hn₁,hn₂,hn₃,spectrumWeight] using hG
  have hs' : FullStationaryEquations (W3.Elimination.toSpectrum w) (relativePhase z₁ z₂)
      (relativePhase z₁ z₃) w.g1 w.g2 w.g3 (normSq z₁) (normSq z₂) (normSq z₃) := by
    simpa [hn₁,hn₂,hn₃,hq',hv'] using hstat
  obtain ⟨lam, hamp⟩ := (exists_amplitude_iff_stationary (W3.Elimination.toSpectrum w)
    z₁ z₂ z₃ w.g1 w.g2 w.g3 (by rw [hn₁]; exact ne_of_gt h₁)
    (by rw [hn₂]; exact ne_of_gt h₂) (by rw [hn₃]; exact ne_of_gt h₃) hg₁ hG').mpr hs'
  exact ⟨z₁,z₂,z₃,lam,hx,by simpa [hn₁,hn₂,hn₃] using hsum,hamp⟩

/-- Canonical nonnegative coupling magnitudes; the real closed field supplies
the roots, so the finite list has no unproved square-root oracle. -/
def canonicalMagnitudes (w : W3.Elimination.WeightedData K) (i : Fin 3) : K :=
  Classical.choose (exists_nonnegative_sqrt (normSq (pairInput w i).d)
    (by unfold normSq; exact add_nonneg (sq_nonneg _) (sq_nonneg _)))

theorem canonicalMagnitudes_spec (w : W3.Elimination.WeightedData K) (i : Fin 3) :
    0 ≤ canonicalMagnitudes w i ∧ (canonicalMagnitudes w i) ^ 2 = normSq (pairInput w i).d :=
  Classical.choose_spec (exists_nonnegative_sqrt (normSq (pairInput w i).d)
    (by unfold normSq; exact add_nonneg (sq_nonneg _) (sq_nonneg _)))

end RealClosed
end W3.Weighted
