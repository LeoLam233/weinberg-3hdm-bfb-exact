import W3.WeightedCoverage

/-! Exact radii and squared-projector correspondence, retaining the invariants
needed to transfer the charged reconstruction's purity and physical filter. -/
noncomputable section
namespace W3.Weighted
open ComplexPair W3.Elimination
section Ordered
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def squaredEntry (z w : ComplexPair K) : ComplexPair K := mul (mul z (conj w)) (mul z (conj w))

def PointMatches (x : SpectrumPoint K) (z₁ z₂ z₃ : ComplexPair K) : Prop :=
  x.r₁ = normSq z₁ ∧ x.r₂ = normSq z₂ ∧ x.r₃ = normSq z₃ ∧
  squaredEntry z₁ z₂ = scale (x.r₁*x.r₂) x.q ∧
  squaredEntry z₁ z₃ = scale (x.r₁*x.r₃) x.v ∧
  squaredEntry z₂ z₃ = scale (x.r₂*x.r₃) (mul x.v (conj x.q))

lemma amplitudePoint_matches (z₁ z₂ z₃ : ComplexPair K)
    (h₁ : normSq z₁ ≠ 0) (h₂ : normSq z₂ ≠ 0) (h₃ : normSq z₃ ≠ 0) :
    PointMatches (amplitudePoint z₁ z₂ z₃) z₁ z₂ z₃ := by
  refine ⟨rfl,rfl,rfl,?_,?_,?_⟩
  · exact (relativePhase_projector_square z₁ z₂ h₁ h₂).symm
  · exact (relativePhase_projector_square z₁ z₃ h₁ h₃).symm
  · change squaredEntry z₂ z₃ = scale _ (mul (relativePhase z₁ z₃) (conj (relativePhase z₁ z₂)))
    rw [relativePhase_composition _ _ _ h₁]
    exact (relativePhase_projector_square z₂ z₃ h₂ h₃).symm

lemma pair12_matches (z₁ z₂ : ComplexPair K) (h₁ : normSq z₁ ≠ 0) (h₂ : normSq z₂ ≠ 0) :
    PointMatches ⟨normSq z₁,normSq z₂,0,relativePhase z₁ z₂,onePhase⟩ z₁ z₂ zeroAmplitude := by
  refine ⟨rfl,rfl,by simp,?_,?_,?_⟩
  · exact (relativePhase_projector_square z₁ z₂ h₁ h₂).symm
  · apply complexPair_ext <;> simp [squaredEntry,zeroAmplitude,scale,mul,conj]
  · apply complexPair_ext <;> simp [squaredEntry,zeroAmplitude,scale,mul,conj]
lemma pair13_matches (z₁ z₃ : ComplexPair K) (h₁ : normSq z₁ ≠ 0) (h₃ : normSq z₃ ≠ 0) :
    PointMatches ⟨normSq z₁,0,normSq z₃,onePhase,relativePhase z₁ z₃⟩ z₁ zeroAmplitude z₃ := by
  refine ⟨rfl,by simp,rfl,?_,?_,?_⟩
  · apply complexPair_ext <;> simp [squaredEntry,zeroAmplitude,scale,mul,conj]
  · exact (relativePhase_projector_square z₁ z₃ h₁ h₃).symm
  · apply complexPair_ext <;> simp [squaredEntry,zeroAmplitude,scale,mul,conj]
lemma pair23_matches (z₂ z₃ : ComplexPair K) (h₂ : normSq z₂ ≠ 0) (h₃ : normSq z₃ ≠ 0) :
    PointMatches ⟨0,normSq z₂,normSq z₃,onePhase,relativePhase z₂ z₃⟩ zeroAmplitude z₂ z₃ := by
  refine ⟨by simp,rfl,rfl,?_,?_,?_⟩
  · apply complexPair_ext <;> simp [squaredEntry,zeroAmplitude,scale,mul,conj]
  · apply complexPair_ext <;> simp [squaredEntry,zeroAmplitude,scale,mul,conj]
  · have hh := (relativePhase_projector_square z₂ z₃ h₂ h₃).symm
    have hm : mul (relativePhase z₂ z₃) (conj (onePhase : ComplexPair K)) = relativePhase z₂ z₃ := by
      apply complexPair_ext <;> simp [onePhase,mul,conj]
    change squaredEntry z₂ z₃ = scale _ (mul (relativePhase z₂ z₃) (conj onePhase))
    rw [hm]
    exact hh

lemma single1_matches (z : ComplexPair K) (hn : normSq z = 1) :
    PointMatches (singletonPoint 0) z zeroAmplitude zeroAmplitude := by
  refine ⟨hn.symm,by simp [singletonPoint],by simp [singletonPoint],?_,?_,?_⟩ <;>
    apply complexPair_ext <;> simp [singletonPoint,squaredEntry,zeroAmplitude,scale,mul,conj]
lemma single2_matches (z : ComplexPair K) (hn : normSq z = 1) :
    PointMatches (singletonPoint 1) zeroAmplitude z zeroAmplitude := by
  refine ⟨by simp [singletonPoint],hn.symm,by simp [singletonPoint],?_,?_,?_⟩ <;>
    apply complexPair_ext <;> simp [singletonPoint,squaredEntry,zeroAmplitude,scale,mul,conj]
lemma single3_matches (z : ComplexPair K) (hn : normSq z = 1) :
    PointMatches (singletonPoint 2) zeroAmplitude zeroAmplitude z := by
  refine ⟨by simp [singletonPoint],by simp [singletonPoint],hn.symm,?_,?_,?_⟩ <;>
    apply complexPair_ext <;> simp [singletonPoint,squaredEntry,zeroAmplitude,scale,mul,conj]

/-- Point correspondence alone identifies the complete quadratic weighted
energy, including all three complex couplings, even with inactive phases. -/
theorem pointMatches_value (w : WeightedData K) (x : SpectrumPoint K) (z₁ z₂ z₃ : ComplexPair K)
    (hm : PointMatches x z₁ z₂ z₃) :
    spectrumValue w x = amplitudeEnergy (toSpectrum w) z₁ z₂ z₃ /
      (w.g1*normSq z₁+w.g2*normSq z₂+w.g3*normSq z₃)^2 := by
  obtain ⟨h₁,h₂,h₃,h₁₂,h₁₃,h₂₃⟩ := hm
  have he₁₂ : amplitudeEdge (toSpectrum w).d₁₂ z₁ z₂ =
      mul (toSpectrum w).d₁₂ (scale (x.r₁*x.r₂) x.q) := congrArg (mul (toSpectrum w).d₁₂) h₁₂
  have he₁₃ : amplitudeEdge (toSpectrum w).d₁₃ z₁ z₃ =
      mul (toSpectrum w).d₁₃ (scale (x.r₁*x.r₃) x.v) := congrArg (mul (toSpectrum w).d₁₃) h₁₃
  have he₂₃ : amplitudeEdge (toSpectrum w).d₂₃ z₂ z₃ =
      mul (toSpectrum w).d₂₃ (scale (x.r₂*x.r₃) (mul x.v (conj x.q))) := congrArg (mul (toSpectrum w).d₂₃) h₂₃
  unfold spectrumValue weightedQuotient amplitudeEnergy amplitudeRow₁ amplitudeRow₂ amplitudeRow₃
  rw [he₁₂,he₁₃,he₂₃,← h₁,← h₂,← h₃,div_mul_eq_div_div]
  congr 1
  simp only [twiceB₁,twiceB₂,twiceB₃,edge₁₂,edge₁₃,edge₂₃,mul,scale]
  ring


/-- Completeness retaining the actual radii and squared projector entries,
so charged reconstruction filters can be transported without phase ambiguity. -/
theorem amplitude_matches_candidate (w : WeightedData K) (hex : completeWeightedExceptional w ≠ 0)
    (ρ : Fin 3 → K) (hρ : ∀ i, (ρ i)^2 = normSq (pairInput w i).d)
    (z₁ z₂ z₃ : ComplexPair K) (lam : K)
    (hn : normSq z₁+normSq z₂+normSq z₃=1)
    (he : AmplitudeEquations (toSpectrum w) z₁ z₂ z₃ w.g1 w.g2 w.g3 lam) :
    ∃ x ∈ spectrumCandidates w ρ, PointMatches x z₁ z₂ z₃ := by
  classical
  obtain ⟨hphase,helem⟩ := mul_ne_zero_iff.mp hex
  obtain ⟨hloop,hg₁,hg₂,hg₃,_,_,_,_⟩ := elementaryExceptional_properties w helem
  have hρ₀ (i : Fin 3) : ρ i ≠ 0 := by
    intro hz
    apply pairInput_norm_ne_zero w hloop i
    rw [← hρ i, hz, zero_pow (by decide)]
  have hW := generic_pair_W_ne_zero w helem ρ hρ
  have hG := generic_amplitude_weight_ne_zero w hex z₁ z₂ z₃ lam hn he
  have npos (z : ComplexPair K) (hz : normSq z ≠ 0) : 0 < normSq z :=
    lt_of_le_of_ne (add_nonneg (sq_nonneg _) (sq_nonneg _)) (Ne.symm hz)
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
      exact ⟨_,mem_single 2 hg₃,single3_matches z₃ (by simpa using hn)⟩
    · by_cases h₃ : normSq z₃ = 0
      · have hz₃ := normSq_eq_zeroAmplitude z₃ h₃
        subst z₃
        exact ⟨_,mem_single 1 hg₂,single2_matches z₂ (by simpa using hn)⟩
      · obtain ⟨s,hm,hl,hr,hq,_⟩ := pair_amplitude_candidate w ρ 2 z₂ z₃ lam
          (npos _ h₂) (npos _ h₃) (by simpa using hn) (by simpa [pairInput] using hG)
          (hρ 2) (hρ₀ 2) (hW 2) (amplitude_support₂₃ _ _ _ _ _ _ _ he)
        refine ⟨_,mem_pair 2 s hm,?_⟩
        change PointMatches ⟨0,pairLeft (pairInput w 2) (ρ 2) s,
          pairRight (pairInput w 2) (ρ 2) s,onePhase,pairPhase (pairInput w 2).d (ρ 2) s⟩ _ _ _
        rw [hl,hr,hq]
        exact pair23_matches _ _ h₂ h₃
  · by_cases h₂ : normSq z₂ = 0
    · have hz₂ := normSq_eq_zeroAmplitude z₂ h₂
      subst z₂
      by_cases h₃ : normSq z₃ = 0
      · have hz₃ := normSq_eq_zeroAmplitude z₃ h₃
        subst z₃
        exact ⟨_,mem_single 0 hg₁,single1_matches z₁ (by simpa using hn)⟩
      · obtain ⟨s,hm,hl,hr,hq,_⟩ := pair_amplitude_candidate w ρ 1 z₁ z₃ lam
          (npos _ h₁) (npos _ h₃) (by simpa using hn) (by simpa [pairInput] using hG)
          (hρ 1) (hρ₀ 1) (hW 1) (amplitude_support₁₃ _ _ _ _ _ _ _ he)
        refine ⟨_,mem_pair 1 s hm,?_⟩
        change PointMatches ⟨pairLeft (pairInput w 1) (ρ 1) s,0,
          pairRight (pairInput w 1) (ρ 1) s,onePhase,pairPhase (pairInput w 1).d (ρ 1) s⟩ _ _ _
        rw [hl,hr,hq]
        exact pair13_matches _ _ h₁ h₃
    · by_cases h₃ : normSq z₃ = 0
      · have hz₃ := normSq_eq_zeroAmplitude z₃ h₃
        subst z₃
        obtain ⟨s,hm,hl,hr,hq,_⟩ := pair_amplitude_candidate w ρ 0 z₁ z₂ lam
          (npos _ h₁) (npos _ h₂) (by simpa using hn) (by simpa [pairInput] using hG)
          (hρ 0) (hρ₀ 0) (hW 0) (amplitude_support₁₂ _ _ _ _ _ _ _ he)
        refine ⟨_,mem_pair 0 s hm,?_⟩
        change PointMatches ⟨pairLeft (pairInput w 0) (ρ 0) s,
          pairRight (pairInput w 0) (ρ 0) s,0,pairPhase (pairInput w 0).d (ρ 0) s,onePhase⟩ _ _ _
        rw [hl,hr,hq]
        exact pair12_matches _ _ h₁ h₂
      · refine ⟨amplitudePoint z₁ z₂ z₃,Finset.mem_union_right _ ?_,amplitudePoint_matches _ _ _ h₁ h₂ h₃⟩
        exact full_amplitude_mem_candidates w hphase hg₁ z₁ z₂ z₃ lam hloop
          (npos _ h₁) (npos _ h₂) (npos _ h₃) hn he

end Ordered
end W3.Weighted
