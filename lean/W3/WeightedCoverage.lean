import W3.WeightedValue
import W3.OperatorSupports
import W3.OperatorPoles

/-! Exhaustive all-support value coverage by the concrete fifteen-point list. -/
noncomputable section
namespace W3.Weighted
open ComplexPair W3.Elimination
section Ordered
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

lemma pairInput_exceptional (w : WeightedData K) (he : elementaryExceptional w ≠ 0) (i : Fin 3) :
    pairExceptional (pairInput w i).a (pairInput w i).b (pairInput w i).e
      (pairInput w i).d.re (pairInput w i).d.im (pairInput w i).g₁ (pairInput w i).g₂ ≠ 0 := by
  obtain ⟨_,_,_,_,_,h₁₂,h₁₃,h₂₃⟩ := elementaryExceptional_properties w he
  fin_cases i
  · exact h₁₂
  · exact h₁₃
  · exact h₂₃

lemma pairInput_norm_ne_zero (w : WeightedData K) (hl : weightedLoop w ≠ 0) (i : Fin 3) :
    normSq (pairInput w i).d ≠ 0 := by
  obtain ⟨h₁₂,h₁₃,h₂₃⟩ := weightedLoop_edge_norms_ne_zero w hl
  fin_cases i
  · exact h₁₂
  · exact h₁₃
  · exact h₂₃

lemma generic_pair_W_ne_zero (w : WeightedData K) (he : elementaryExceptional w ≠ 0)
    (ρ : Fin 3 → K) (hρ : ∀ i, (ρ i)^2 = normSq (pairInput w i).d) (i : Fin 3) (s : Bool) :
    pairW ((pairInput w i).a/2) ((pairInput w i).b/2) (pairH (pairInput w i) (ρ i) s)
      (pairInput w i).g₁ (pairInput w i).g₂ ≠ 0 := by
  have h := pair_denominator_ne_zero (pairInput w i).a (pairInput w i).b (pairInput w i).e
    (pairInput w i).d.re (pairInput w i).d.im (pairInput w i).g₁ (pairInput w i).g₂
    (ρ i) (branchSign s) (hρ i) (branchSign_sq s) (pairInput_exceptional w he i)
  convert h using 1 <;> unfold pairW pairH <;> ring

lemma amplitudeEnergy_single₁ (k : SpectrumData K) (z : ComplexPair K) :
    amplitudeEnergy k z zeroAmplitude zeroAmplitude = k.a₁ * normSq z ^ 2 / 2 := by
  simp [amplitudeEnergy, amplitudeRow₁, amplitudeRow₂, amplitudeRow₃]
  ring
lemma amplitudeEnergy_single₂ (k : SpectrumData K) (z : ComplexPair K) :
    amplitudeEnergy k zeroAmplitude z zeroAmplitude = k.a₂ * normSq z ^ 2 / 2 := by
  simp [amplitudeEnergy, amplitudeRow₁, amplitudeRow₂, amplitudeRow₃]
  ring
lemma amplitudeEnergy_single₃ (k : SpectrumData K) (z : ComplexPair K) :
    amplitudeEnergy k zeroAmplitude zeroAmplitude z = k.a₃ * normSq z ^ 2 / 2 := by
  simp [amplitudeEnergy, amplitudeRow₁, amplitudeRow₂, amplitudeRow₃]
  ring

lemma normalized_eigen_quotient (k : SpectrumData K) (z₁ z₂ z₃ : ComplexPair K)
    (g₁ g₂ g₃ lam : K) (hG : g₁*normSq z₁+g₂*normSq z₂+g₃*normSq z₃ ≠ 0)
    (he : AmplitudeEquations k z₁ z₂ z₃ g₁ g₂ g₃ lam) :
    amplitudeEnergy k z₁ z₂ z₃ / (g₁*normSq z₁+g₂*normSq z₂+g₃*normSq z₃)^2 =
      lam / (2*(g₁*normSq z₁+g₂*normSq z₂+g₃*normSq z₃)) := by
  rw [amplitude_energy_eigen _ _ _ _ _ _ _ _ he]
  field_simp [hG]

/-- Every normalized stationary amplitude projector, on every support, has
its exact weighted value in the concrete finite common spectrum. -/
theorem amplitude_value_in_spectrum (w : WeightedData K) (hex : completeWeightedExceptional w ≠ 0)
    (ρ : Fin 3 → K) (hρ : ∀ i, (ρ i)^2 = normSq (pairInput w i).d)
    (z₁ z₂ z₃ : ComplexPair K) (lam : K)
    (hn : normSq z₁+normSq z₂+normSq z₃=1)
    (he : AmplitudeEquations (toSpectrum w) z₁ z₂ z₃ w.g1 w.g2 w.g3 lam) :
    amplitudeEnergy (toSpectrum w) z₁ z₂ z₃ /
      (w.g1*normSq z₁+w.g2*normSq z₂+w.g3*normSq z₃)^2 ∈ spectrumValues w ρ := by
  classical
  obtain ⟨hphase,helem⟩ := mul_ne_zero_iff.mp hex
  obtain ⟨hloop,hg₁,hg₂,hg₃,hgs,hp₁₂,hp₁₃,hp₂₃⟩ := elementaryExceptional_properties w helem
  have hρ₀ (i : Fin 3) : ρ i ≠ 0 := by
    intro hz
    apply pairInput_norm_ne_zero w hloop i
    rw [← hρ i, hz, zero_pow (by decide)]
  have hW := generic_pair_W_ne_zero w helem ρ hρ
  have hG := generic_amplitude_weight_ne_zero w hex z₁ z₂ z₃ lam hn he
  have hval := normalized_eigen_quotient (toSpectrum w) z₁ z₂ z₃ w.g1 w.g2 w.g3 lam hG he
  have npos (z : ComplexPair K) (hz : normSq z ≠ 0) : 0 < normSq z := by
    have hs : 0 ≤ normSq z := add_nonneg (sq_nonneg _) (sq_nonneg _)
    exact lt_of_le_of_ne hs (Ne.symm hz)
  have mem_single (i : Fin 3) (hg : ![w.g1,w.g2,w.g3] i ≠ 0) :
      singletonPoint (K:=K) i ∈ spectrumCandidates w ρ :=
    Finset.mem_union_left _ (Finset.mem_union_left _ (singletonPoint_mem w i hg))
  have mem_pair (i : Fin 3) (s : Bool) (hm : pairPoint w ρ i s ∈ pairCandidates w ρ) :
      pairPoint w ρ i s ∈ spectrumCandidates w ρ :=
    Finset.mem_union_left _ (Finset.mem_union_right _ hm)
  by_cases h₁ : normSq z₁ = 0
  · have hz₁ := normSq_eq_zeroAmplitude z₁ h₁
    subst z₁
    by_cases h₂ : normSq z₂ = 0
    · have hz₂ := normSq_eq_zeroAmplitude z₂ h₂
      subst z₂
      have hn₃ : normSq z₃ = 1 := by simpa using hn
      apply Finset.mem_image.mpr
      refine ⟨singletonPoint 2, mem_single 2 hg₃, ?_⟩
      rw [singletonPoint_value, amplitudeEnergy_single₃]
      simp [normSq_zeroAmplitude, hn₃, toSpectrum, div_mul_eq_div_div]
    · by_cases h₃ : normSq z₃ = 0
      · have hz₃ := normSq_eq_zeroAmplitude z₃ h₃
        subst z₃
        have hn₂ : normSq z₂ = 1 := by simpa using hn
        apply Finset.mem_image.mpr
        refine ⟨singletonPoint 1, mem_single 1 hg₂, ?_⟩
        rw [singletonPoint_value, amplitudeEnergy_single₂]
        simp [normSq_zeroAmplitude, hn₂, toSpectrum, div_mul_eq_div_div]
      · obtain ⟨s,hm,_,_,_,hv⟩ := pair_amplitude_candidate w ρ 2 z₂ z₃ lam
          (npos _ h₂) (npos _ h₃) (by simpa using hn) (by simpa [pairInput] using hG)
          (hρ 2) (hρ₀ 2) (hW 2) (amplitude_support₂₃ _ _ _ _ _ _ _ he)
        apply Finset.mem_image.mpr
        refine ⟨_, mem_pair 2 s hm, ?_⟩
        rw [hval]
        simpa [pairInput] using hv
  · by_cases h₂ : normSq z₂ = 0
    · have hz₂ := normSq_eq_zeroAmplitude z₂ h₂
      subst z₂
      by_cases h₃ : normSq z₃ = 0
      · have hz₃ := normSq_eq_zeroAmplitude z₃ h₃
        subst z₃
        have hn₁ : normSq z₁ = 1 := by simpa using hn
        apply Finset.mem_image.mpr
        refine ⟨singletonPoint 0, mem_single 0 hg₁, ?_⟩
        rw [singletonPoint_value, amplitudeEnergy_single₁]
        simp [normSq_zeroAmplitude, hn₁, toSpectrum, div_mul_eq_div_div]
      · obtain ⟨s,hm,_,_,_,hv⟩ := pair_amplitude_candidate w ρ 1 z₁ z₃ lam
          (npos _ h₁) (npos _ h₃) (by simpa using hn) (by simpa [pairInput] using hG)
          (hρ 1) (hρ₀ 1) (hW 1) (amplitude_support₁₃ _ _ _ _ _ _ _ he)
        apply Finset.mem_image.mpr
        refine ⟨_, mem_pair 1 s hm, ?_⟩
        rw [hval]
        simpa [pairInput] using hv
    · by_cases h₃ : normSq z₃ = 0
      · have hz₃ := normSq_eq_zeroAmplitude z₃ h₃
        subst z₃
        obtain ⟨s,hm,_,_,_,hv⟩ := pair_amplitude_candidate w ρ 0 z₁ z₂ lam
          (npos _ h₁) (npos _ h₂) (by simpa using hn) (by simpa [pairInput] using hG)
          (hρ 0) (hρ₀ 0) (hW 0) (amplitude_support₁₂ _ _ _ _ _ _ _ he)
        apply Finset.mem_image.mpr
        refine ⟨_, mem_pair 0 s hm, ?_⟩
        rw [hval]
        simpa [pairInput] using hv
      · apply Finset.mem_image.mpr
        refine ⟨amplitudePoint z₁ z₂ z₃, Finset.mem_union_right _ ?_, ?_⟩
        · exact full_amplitude_mem_candidates w hphase hg₁ z₁ z₂ z₃ lam hloop
            (npos _ h₁) (npos _ h₂) (npos _ h₃) hn he
        · exact spectrumValue_amplitudePoint w z₁ z₂ z₃ h₁ h₂ h₃

end Ordered
end W3.Weighted
