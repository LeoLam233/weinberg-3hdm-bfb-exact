import W3.WeightedRealization
import W3.WeightedCoverage

/-! Every retained branch has a normalized stationary amplitude witness.
The witness construction is algebraic over the same real closed field. -/
noncomputable section
namespace W3.Weighted
open ComplexPair W3.Elimination
section Ordered
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem scalar_pair_implies_amplitude (p : PairInput K) (z₁ z₂ : ComplexPair K) (lam : K)
    (h₁ : normSq z₁ ≠ 0) (h₂ : normSq z₂ ≠ 0)
    (hp : (mul p.d (relativePhase z₁ z₂)).im = 0)
    (hr₁ : p.a * normSq z₁ + (p.e + (mul p.d (relativePhase z₁ z₂)).re) * normSq z₂ = lam * p.g₁)
    (hr₂ : (p.e + (mul p.d (relativePhase z₁ z₂)).re) * normSq z₁ + p.b * normSq z₂ = lam * p.g₂) :
    PairAmplitudeEquations p.a p.b p.e p.d z₁ z₂ p.g₁ p.g₂ lam := by
  unfold PairAmplitudeEquations
  rw [amplitudeEdge_phase₁₂ _ _ _ h₁ h₂]
  simp only [scale]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination normSq z₁ * hr₁
  · linear_combination normSq z₂ * hr₂
  · rw [hp, mul_zero]

theorem pair_amplitude_support₁₂ (k : SpectrumData K) (z₁ z₂ : ComplexPair K) (g₁ g₂ g₃ lam : K)
    (h : PairAmplitudeEquations k.a₁ k.a₂ k.e₁₂ k.d₁₂ z₁ z₂ g₁ g₂ lam) :
    AmplitudeEquations k z₁ z₂ zeroAmplitude g₁ g₂ g₃ lam := by
  refine ⟨?_, ?_, ?_⟩ <;> apply complexPair_ext <;>
    simp [amplitudeRow₁, amplitudeRow₂, amplitudeRow₃, h.1, h.2.1, h.2.2]

theorem pair_amplitude_support₁₃ (k : SpectrumData K) (z₁ z₃ : ComplexPair K) (g₁ g₂ g₃ lam : K)
    (h : PairAmplitudeEquations k.a₁ k.a₃ k.e₁₃ k.d₁₃ z₁ z₃ g₁ g₃ lam) :
    AmplitudeEquations k z₁ zeroAmplitude z₃ g₁ g₂ g₃ lam := by
  refine ⟨?_, ?_, ?_⟩ <;> apply complexPair_ext <;>
    simp [amplitudeRow₁, amplitudeRow₂, amplitudeRow₃, h.1, h.2.1, h.2.2]

theorem pair_amplitude_support₂₃ (k : SpectrumData K) (z₂ z₃ : ComplexPair K) (g₁ g₂ g₃ lam : K)
    (h : PairAmplitudeEquations k.a₂ k.a₃ k.e₂₃ k.d₂₃ z₂ z₃ g₂ g₃ lam) :
    AmplitudeEquations k zeroAmplitude z₂ z₃ g₁ g₂ g₃ lam := by
  refine ⟨?_, ?_, ?_⟩ <;> apply complexPair_ext <;>
    simp [amplitudeRow₁, amplitudeRow₂, amplitudeRow₃, h.1, h.2.1, h.2.2]

end Ordered
section RealClosed
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]

/-- Exact pair amplitudes realizing the printed n/W branch. -/
theorem retained_pair_amplitudes (w : WeightedData K) (ρ : Fin 3 → K) (i : Fin 3) (s : Bool)
    (hρ : (ρ i)^2 = normSq (pairInput w i).d) (hret : PairRetained w ρ i s) :
    ∃ z₁ z₂ : ComplexPair K,
      normSq z₁ = pairLeft (pairInput w i) (ρ i) s ∧
      normSq z₂ = pairRight (pairInput w i) (ρ i) s ∧
      relativePhase z₁ z₂ = pairPhase (pairInput w i).d (ρ i) s ∧
      PairAmplitudeEquations (pairInput w i).a (pairInput w i).b (pairInput w i).e
        (pairInput w i).d z₁ z₂ (pairInput w i).g₁ (pairInput w i).g₂
        (2 * spectrumValue w (pairPoint w ρ i s) * spectrumWeight w (pairPoint w ρ i s)) := by
  let p := pairInput w i
  let l := pairLeft p (ρ i) s
  let r := pairRight p (ρ i) s
  let q := pairPhase p.d (ρ i) s
  obtain ⟨hρ₀,hW,hN,hl,hr,hG⟩ := hret
  obtain ⟨hq,hpi,hpr⟩ := pairPhase_correct p.d (ρ i) s hρ hρ₀
  obtain ⟨z₁,hn₁,hs₁⟩ := phase_radius_realization l onePhase hl.le (by simp [onePhase,normSq])
  obtain ⟨z₂,hn₂,hs₂⟩ := phase_radius_realization r q hr.le hq
  have hu₁ := amplitudeUnit_of_square _ _ _ (ne_of_gt hl) hn₁ hs₁
  have hu₂ := amplitudeUnit_of_square _ _ _ (ne_of_gt hr) hn₂ hs₂
  have hrel : relativePhase z₁ z₂ = q := by
    rw [relativePhase, hu₁, hu₂]
    apply complexPair_ext <;> simp [onePhase,mul,conj]
  have hrad := pair_reconstruction_stationary (p.a/2) (p.b/2) (pairH p (ρ i) s) p.g₁ p.g₂ hW hN
  have hvalue := (retained_pair_formula w ρ i s hρ ⟨hρ₀,hW,hN,hl,hr,hG⟩).2
  have hweight := pairPoint_weight w ρ i s
  refine ⟨z₁,z₂,hn₁,hn₂,hrel,?_⟩
  apply scalar_pair_implies_amplitude p z₁ z₂ _ (by rw [hn₁]; exact ne_of_gt hl)
    (by rw [hn₂]; exact ne_of_gt hr)
  · rw [hrel]; exact hpi
  · rw [hn₁,hn₂,hrel,hpr,hvalue,hweight]
    change p.a * l + (p.e + branchSign s * ρ i) * r =
      2 * (pairDet (p.a/2) (p.b/2) (pairH p (ρ i) s) /
        pairW (p.a/2) (p.b/2) (pairH p (ρ i) s) p.g₁ p.g₂) * (p.g₁*l+p.g₂*r) * p.g₁
    have hh : (p.a/2)*l + pairH p (ρ i) s*r =
        (pairDet (p.a/2) (p.b/2) (pairH p (ρ i) s) /
        pairW (p.a/2) (p.b/2) (pairH p (ρ i) s) p.g₁ p.g₂) * (p.g₁*l+p.g₂*r) * p.g₁ := hrad.1
    unfold pairH at hh ⊢
    linear_combination 2 * hh
  · rw [hn₁,hn₂,hrel,hpr,hvalue,hweight]
    change (p.e + branchSign s * ρ i) * l + p.b * r =
      2 * (pairDet (p.a/2) (p.b/2) (pairH p (ρ i) s) /
        pairW (p.a/2) (p.b/2) (pairH p (ρ i) s) p.g₁ p.g₂) * (p.g₁*l+p.g₂*r) * p.g₂
    have hh : pairH p (ρ i) s*l + (p.b/2)*r =
        (pairDet (p.a/2) (p.b/2) (pairH p (ρ i) s) /
        pairW (p.a/2) (p.b/2) (pairH p (ρ i) s) p.g₁ p.g₂) * (p.g₁*l+p.g₂*r) * p.g₂ := hrad.2
    unfold pairH at hh ⊢
    linear_combination 2 * hh

/-- Unified witness predicate used to check that every finite-list value is
physically realized by a normalized stationary rank-one projector. -/
def SpectrumWitness (w : WeightedData K) (x : SpectrumPoint K) : Prop :=
  ∃ z₁ z₂ z₃ : ComplexPair K, ∃ lam : K,
    normSq z₁ + normSq z₂ + normSq z₃ = 1 ∧
    w.g1*normSq z₁+w.g2*normSq z₂+w.g3*normSq z₃ ≠ 0 ∧
    AmplitudeEquations (toSpectrum w) z₁ z₂ z₃ w.g1 w.g2 w.g3 lam ∧
    amplitudeEnergy (toSpectrum w) z₁ z₂ z₃ /
      (w.g1*normSq z₁+w.g2*normSq z₂+w.g3*normSq z₃)^2 = spectrumValue w x

/-- Every retained pair candidate has an actual normalized amplitude witness. -/
theorem pairPoint_witness (w : WeightedData K) (ρ : Fin 3 → K) (i : Fin 3) (s : Bool)
    (hρ : (ρ i)^2 = normSq (pairInput w i).d) (hret : PairRetained w ρ i s) :
    SpectrumWitness w (pairPoint w ρ i s) := by
  obtain ⟨z₁,z₂,hn₁,hn₂,hrel,hamp⟩ := retained_pair_amplitudes w ρ i s hρ hret
  have hn := (retained_pair_formula w ρ i s hρ hret).1
  have hG := hret.2.2.2.2.2
  have hw := pairPoint_weight w ρ i s
  have finish (a b c : ComplexPair K)
      (hN : normSq a+normSq b+normSq c=1)
      (hW : w.g1*normSq a+w.g2*normSq b+w.g3*normSq c = spectrumWeight w (pairPoint w ρ i s))
      (he : AmplitudeEquations (toSpectrum w) a b c w.g1 w.g2 w.g3
        (2*spectrumValue w (pairPoint w ρ i s)*spectrumWeight w (pairPoint w ρ i s))) :
      SpectrumWitness w (pairPoint w ρ i s) := by
    have hW₀ : w.g1*normSq a+w.g2*normSq b+w.g3*normSq c ≠ 0 := hW ▸ hG
    refine ⟨a,b,c,_,hN,hW₀,he,?_⟩
    rw [normalized_eigen_quotient _ _ _ _ _ _ _ _ hW₀ he,hW]
    field_simp [hG]
  fin_cases i
  · apply finish z₁ z₂ zeroAmplitude
    · simpa [hn₁,hn₂] using hn
    · rw [hw,hn₁,hn₂]; simp [pairInput]
    · exact pair_amplitude_support₁₂ _ _ _ _ _ _ _ hamp
  · apply finish z₁ zeroAmplitude z₂
    · simpa [hn₁,hn₂] using hn
    · rw [hw,hn₁,hn₂]; simp [pairInput]
    · exact pair_amplitude_support₁₃ _ _ _ _ _ _ _ hamp
  · apply finish zeroAmplitude z₁ z₂
    · simpa [hn₁,hn₂] using hn
    · rw [hw,hn₁,hn₂]; simp [pairInput]
    · exact pair_amplitude_support₂₃ _ _ _ _ _ _ _ hamp

end RealClosed
end W3.Weighted
