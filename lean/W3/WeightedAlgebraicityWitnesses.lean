import W3.WeightedAlgebraicityCandidates

/-! Algebraicity of square-root representatives and physical projector entries.
No arbitrary global amplitude phase is incorrectly declared algebraic. -/
noncomputable section
namespace W3.Weighted
open ComplexPair W3.Elimination
section Algebraic
variable {F L : Type*} [Field F] [Field L] [Algebra F L] [LinearOrder L] [IsStrictOrderedRing L]

/-- A complex pair is algebraic coordinatewise if its norm and the real part
of its square are algebraic. This is a pair of explicit quadratic equations. -/
theorem algebraicPair_of_norm_square (z : ComplexPair L)
    (hn : IsAlgebraic F (normSq z)) (hs : IsAlgebraic F (mul z z).re) : AlgebraicPair F z := by
  have h2 : IsAlgebraic F (2 : L) := isAlgebraic_natCast 2
  have hr : z.re ^ 2 = (normSq z + (mul z z).re) / 2 := by
    simp only [normSq,mul]
    ring
  have hi : z.im ^ 2 = (normSq z - (mul z z).re) / 2 := by
    simp only [normSq,mul]
    ring
  exact ⟨IsAlgebraic.of_pow (by decide : 0 < 2) (hr ▸ algebraic_div (hn.add hs) h2),
    IsAlgebraic.of_pow (by decide : 0 < 2) (hi ▸ algebraic_div (hn.sub hs) h2)⟩

/-- The squared-amplitude witnesses constructed in Section 2 and Section 8
are algebraic over F, including the phase −1 branch and zero radius. -/
theorem realized_amplitude_algebraic (r : L) (q z : ComplexPair L)
    (hr : IsAlgebraic F r) (hq : AlgebraicPair F q)
    (hn : normSq z = r) (hs : conj (mul z z) = scale r q) : AlgebraicPair F z := by
  apply algebraicPair_of_norm_square z
  · rwa [hn]
  · have he := congrArg ComplexPair.re hs
    change (mul z z).re = r*q.re at he
    rw [he]
    exact hr.mul hq.1

/-- Every representative of a matched rank-one projector has algebraic entries,
even if its irrelevant common amplitude phase is transcendental over F. -/
theorem matched_projector_algebraic (x : SpectrumPoint L) (hx : AlgebraicPoint F x)
    (z₁ z₂ z₃ : ComplexPair L) (hm : PointMatches x z₁ z₂ z₃) :
    IsAlgebraic F (normSq z₁) ∧ IsAlgebraic F (normSq z₂) ∧ IsAlgebraic F (normSq z₃) ∧
    AlgebraicPair F (mul z₁ (conj z₂)) ∧ AlgebraicPair F (mul z₁ (conj z₃)) ∧
    AlgebraicPair F (mul z₂ (conj z₃)) := by
  obtain ⟨hr₁,hr₂,hr₃,hq,hv⟩ := hx
  obtain ⟨hn₁,hn₂,hn₃,hs₁₂,hs₁₃,hs₂₃⟩ := hm
  have hz₁ : IsAlgebraic F (normSq z₁) := hn₁ ▸ hr₁
  have hz₂ : IsAlgebraic F (normSq z₂) := hn₂ ▸ hr₂
  have hz₃ : IsAlgebraic F (normSq z₃) := hn₃ ▸ hr₃
  have finish (z w : ComplexPair L) (r s : L) (v : ComplexPair L)
      (hnz : IsAlgebraic F (normSq z)) (hnw : IsAlgebraic F (normSq w))
      (hr : IsAlgebraic F r) (hs : IsAlgebraic F s) (hv : AlgebraicPair F v)
      (hmatch : squaredEntry z w = scale (r*s) v) :
      AlgebraicPair F (mul z (conj w)) := by
    apply algebraicPair_of_norm_square
    · rw [complex_norm_mul,complexPair_norm_conj]
      exact hnz.mul hnw
    · change IsAlgebraic F (squaredEntry z w).re
      rw [hmatch]
      exact (hr.mul hs).mul hv.1
  exact ⟨hz₁,hz₂,hz₃,finish _ _ _ _ _ hz₁ hz₂ hr₁ hr₂ hq hs₁₂,
    finish _ _ _ _ _ hz₁ hz₃ hr₁ hr₃ hv hs₁₃,
    finish _ _ _ _ _ hz₂ hz₃ hr₂ hr₃ (algebraicPair_mul hv (algebraicPair_conj hq)) hs₂₃⟩

/-- Actual selected candidates imply algebraicity of the physical projector;
there is no assumed annihilator at this endpoint. -/
theorem selected_projector_algebraic (w : WeightedData F)
    (hS : phaseSextic (weightedP w) (weightedQ w) ≠ 0)
    (ρ : Fin 3 → L) (hρ : ∀ i, (ρ i)^2 = normSq (pairInput (mapWeighted (algebraMap F L) w) i).d)
    (x : SpectrumPoint L) (hm : x ∈ spectrumCandidates (mapWeighted (algebraMap F L) w) ρ)
    (z₁ z₂ z₃ : ComplexPair L) (hmatch : PointMatches x z₁ z₂ z₃) :
    IsAlgebraic F (normSq z₁) ∧ IsAlgebraic F (normSq z₂) ∧ IsAlgebraic F (normSq z₃) ∧
    AlgebraicPair F (mul z₁ (conj z₂)) ∧ AlgebraicPair F (mul z₁ (conj z₃)) ∧
    AlgebraicPair F (mul z₂ (conj z₃)) :=
  matched_projector_algebraic x (spectrumCandidates_algebraic w hS ρ hρ x hm) z₁ z₂ z₃ hmatch

variable [IsRealClosed L]

theorem phase_radius_algebraic_realization (r : L) (q : ComplexPair L)
    (hr : 0 ≤ r) (hq : normSq q = 1) (har : IsAlgebraic F r) (haq : AlgebraicPair F q) :
    ∃ z : ComplexPair L, AlgebraicPair F z ∧ normSq z = r ∧ conj (mul z z) = scale r q := by
  obtain ⟨z,hn,hs⟩ := phase_radius_realization r q hr hq
  exact ⟨z,realized_amplitude_algebraic r q z har haq hn hs,hn,hs⟩

#print axioms selected_projector_algebraic
#print axioms phase_radius_algebraic_realization
end Algebraic
end W3.Weighted
