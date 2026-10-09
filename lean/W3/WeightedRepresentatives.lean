import W3.WeightedSoundness
import W3.WeightedCorrespondence

noncomputable section
namespace W3.Weighted
open ComplexPair W3.Elimination
section RealClosed
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]

/-- A complete algebraic witness preserving the quantities needed by both
spectra, including each squared projector entry. -/
def SpectrumRepresentation (w : WeightedData K) (x : SpectrumPoint K) : Prop :=
  ∃ z₁ z₂ z₃ : ComplexPair K, ∃ lam : K,
    PointMatches x z₁ z₂ z₃ ∧ normSq z₁+normSq z₂+normSq z₃=1 ∧
    w.g1*normSq z₁+w.g2*normSq z₂+w.g3*normSq z₃ ≠ 0 ∧
    AmplitudeEquations (toSpectrum w) z₁ z₂ z₃ w.g1 w.g2 w.g3 lam

theorem pairPoint_representation (w : WeightedData K) (ρ : Fin 3 → K) (i : Fin 3) (s : Bool)
    (hρ : (ρ i)^2 = normSq (pairInput w i).d) (hret : PairRetained w ρ i s) :
    SpectrumRepresentation w (pairPoint w ρ i s) := by
  obtain ⟨z₁,z₂,hn₁,hn₂,hrel,hamp⟩ := retained_pair_amplitudes w ρ i s hρ hret
  have hn := (retained_pair_formula w ρ i s hρ hret).1
  have hG := hret.2.2.2.2.2
  have hw := pairPoint_weight w ρ i s
  have h₁ : normSq z₁ ≠ 0 := by rw [hn₁]; exact ne_of_gt hret.2.2.2.1
  have h₂ : normSq z₂ ≠ 0 := by rw [hn₂]; exact ne_of_gt hret.2.2.2.2.1
  have finish (a b c : ComplexPair K) (hm : PointMatches (pairPoint w ρ i s) a b c)
      (hN : normSq a+normSq b+normSq c=1)
      (hW : w.g1*normSq a+w.g2*normSq b+w.g3*normSq c = spectrumWeight w (pairPoint w ρ i s))
      (he : AmplitudeEquations (toSpectrum w) a b c w.g1 w.g2 w.g3
        (2*spectrumValue w (pairPoint w ρ i s)*spectrumWeight w (pairPoint w ρ i s))) :
      SpectrumRepresentation w (pairPoint w ρ i s) :=
    ⟨a,b,c,_,hm,hN,hW ▸ hG,he⟩
  fin_cases i <;> dsimp only at hn₁ hn₂ hrel
  · apply finish z₁ z₂ zeroAmplitude
    · change PointMatches ⟨pairLeft (pairInput w 0) (ρ 0) s,pairRight (pairInput w 0) (ρ 0) s,
        0,pairPhase (pairInput w 0).d (ρ 0) s,onePhase⟩ _ _ _
      change normSq z₁ = pairLeft (pairInput w 0) (ρ 0) s at hn₁
      change normSq z₂ = pairRight (pairInput w 0) (ρ 0) s at hn₂
      change relativePhase z₁ z₂ = pairPhase (pairInput w 0).d (ρ 0) s at hrel
      rw [← hn₁,← hn₂,← hrel]
      exact pair12_matches _ _ h₁ h₂
    · simpa [hn₁,hn₂] using hn
    · rw [hw,hn₁,hn₂]; simp [pairInput]
    · exact pair_amplitude_support₁₂ _ _ _ _ _ _ _ hamp
  · apply finish z₁ zeroAmplitude z₂
    · change PointMatches ⟨pairLeft (pairInput w 1) (ρ 1) s,0,pairRight (pairInput w 1) (ρ 1) s,
        onePhase,pairPhase (pairInput w 1).d (ρ 1) s⟩ _ _ _
      change normSq z₁ = pairLeft (pairInput w 1) (ρ 1) s at hn₁
      change normSq z₂ = pairRight (pairInput w 1) (ρ 1) s at hn₂
      change relativePhase z₁ z₂ = pairPhase (pairInput w 1).d (ρ 1) s at hrel
      rw [← hn₁,← hn₂,← hrel]
      exact pair13_matches _ _ h₁ h₂
    · simpa [hn₁,hn₂] using hn
    · rw [hw,hn₁,hn₂]; simp [pairInput]
    · exact pair_amplitude_support₁₃ _ _ _ _ _ _ _ hamp
  · apply finish zeroAmplitude z₁ z₂
    · change PointMatches ⟨0,pairLeft (pairInput w 2) (ρ 2) s,pairRight (pairInput w 2) (ρ 2) s,
        onePhase,pairPhase (pairInput w 2).d (ρ 2) s⟩ _ _ _
      change normSq z₁ = pairLeft (pairInput w 2) (ρ 2) s at hn₁
      change normSq z₂ = pairRight (pairInput w 2) (ρ 2) s at hn₂
      change relativePhase z₁ z₂ = pairPhase (pairInput w 2).d (ρ 2) s at hrel
      rw [← hn₁,← hn₂,← hrel]
      exact pair23_matches _ _ h₁ h₂
    · simpa [hn₁,hn₂] using hn
    · rw [hw,hn₁,hn₂]; simp [pairInput]
    · exact pair_amplitude_support₂₃ _ _ _ _ _ _ _ hamp

theorem singletonPoint_representation (w : WeightedData K) (i : Fin 3)
    (hg : ![w.g1,w.g2,w.g3] i ≠ 0) : SpectrumRepresentation w (singletonPoint i) := by
  have hn : normSq (onePhase : ComplexPair K) = 1 := by simp [onePhase,normSq]
  fin_cases i
  · have hg' : w.g1 ≠ 0 := hg
    refine ⟨onePhase,zeroAmplitude,zeroAmplitude,w.alpha1/w.g1,single1_matches _ hn,?_,?_,?_⟩
    · simp [hn]
    · simpa [hn] using hg'
    · refine ⟨?_,?_,?_⟩ <;> apply complexPair_ext <;>
        simp [amplitudeRow₁,amplitudeRow₂,amplitudeRow₃,hn,toSpectrum,hg']
  · have hg' : w.g2 ≠ 0 := hg
    refine ⟨zeroAmplitude,onePhase,zeroAmplitude,w.alpha2/w.g2,single2_matches _ hn,?_,?_,?_⟩
    · simp [hn]
    · simpa [hn] using hg'
    · refine ⟨?_,?_,?_⟩ <;> apply complexPair_ext <;>
        simp [amplitudeRow₁,amplitudeRow₂,amplitudeRow₃,hn,toSpectrum,hg']
  · have hg' : w.g3 ≠ 0 := hg
    refine ⟨zeroAmplitude,zeroAmplitude,onePhase,w.alpha3/w.g3,single3_matches _ hn,?_,?_,?_⟩
    · simp [hn]
    · simpa [hn] using hg'
    · refine ⟨?_,?_,?_⟩ <;> apply complexPair_ext <;>
        simp [amplitudeRow₁,amplitudeRow₂,amplitudeRow₃,hn,toSpectrum,hg']

/-- Soundness of the entire common finite spectrum with exact amplitude and
projector invariants. This covers all seven nonempty support strata. -/
theorem spectrumCandidates_representable (w : WeightedData K) (ρ : Fin 3 → K)
    (hρ : ∀ i, (ρ i)^2 = normSq (pairInput w i).d)
    (he : weightedExceptional w ≠ 0) (hg₁ : w.g1 ≠ 0)
    (x : SpectrumPoint K) (hm : x ∈ spectrumCandidates w ρ) :
    SpectrumRepresentation w x := by
  classical
  simp only [spectrumCandidates,Finset.mem_union] at hm
  rcases hm with (hs | hp) | hf
  · unfold singletonCandidates at hs
    obtain ⟨i,hfilter,rfl⟩ := Finset.mem_image.mp hs
    have hi := (Finset.mem_filter.mp hfilter).2
    apply singletonPoint_representation w i
    fin_cases i <;> simpa [spectrumWeight,singletonPoint] using hi
  · unfold pairCandidates at hp
    obtain ⟨⟨i,s⟩,hfilter,rfl⟩ := Finset.mem_image.mp hp
    exact pairPoint_representation w ρ i s (hρ i) (Finset.mem_filter.mp hfilter).2
  · obtain ⟨hq,hv,h₁,h₂,h₃,hsum,hG,hstat⟩ := fullCandidates_sound w he hg₁ x hf
    obtain ⟨z₁,z₂,z₃,lam,hx,hn,hamp⟩ := fullCandidates_realizable w he hg₁ x hf
    have hr₁ : normSq z₁ = x.r₁ := congrArg SpectrumPoint.r₁ hx
    have hr₂ : normSq z₂ = x.r₂ := congrArg SpectrumPoint.r₂ hx
    have hr₃ : normSq z₃ = x.r₃ := congrArg SpectrumPoint.r₃ hx
    refine ⟨z₁,z₂,z₃,lam,?_,hn,?_,hamp⟩
    · rw [← hx]
      exact amplitudePoint_matches _ _ _ (by rw [hr₁]; exact ne_of_gt h₁)
        (by rw [hr₂]; exact ne_of_gt h₂) (by rw [hr₃]; exact ne_of_gt h₃)
    · simpa [hr₁,hr₂,hr₃,spectrumWeight] using hG

end RealClosed
end W3.Weighted
