import W3.WeightedRepresentatives

/-! Complete common-spectrum theorem, in every ordered real closed field.
The finite list is the explicit three/six/sextic construction, not an assumed
finite covering. This is the common engine used by the primal and dual problems. -/
noncomputable section
namespace W3.Weighted
open ComplexPair W3.Elimination
section RealClosed
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]

def CommonStationaryValue (w : WeightedData K) (ν : K) : Prop :=
  ∃ z₁ z₂ z₃ : ComplexPair K, ∃ lam : K,
    normSq z₁+normSq z₂+normSq z₃=1 ∧
    AmplitudeEquations (toSpectrum w) z₁ z₂ z₃ w.g1 w.g2 w.g3 lam ∧
    w.g1*normSq z₁+w.g2*normSq z₂+w.g3*normSq z₃ ≠ 0 ∧
    amplitudeEnergy (toSpectrum w) z₁ z₂ z₃ /
      (w.g1*normSq z₁+w.g2*normSq z₂+w.g3*normSq z₃)^2 = ν

/-- Exact, sound and complete common weighted spectrum across all supports. -/
theorem common_spectrum_exact (w : WeightedData K) (hex : completeWeightedExceptional w ≠ 0)
    (ρ : Fin 3 → K) (hρ : ∀ i, (ρ i)^2 = normSq (pairInput w i).d) (ν : K) :
    ν ∈ spectrumValues w ρ ↔ CommonStationaryValue w ν := by
  classical
  obtain ⟨hphase,helem⟩ := mul_ne_zero_iff.mp hex
  have hg₁ := (elementaryExceptional_properties w helem).2.1
  constructor
  · intro hm
    unfold spectrumValues at hm
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨z₁,z₂,z₃,lam,hmatch,hn,hG,hamp⟩ :=
      spectrumCandidates_representable w ρ hρ hphase hg₁ x hx
    exact ⟨z₁,z₂,z₃,lam,hn,hamp,hG,(pointMatches_value w x z₁ z₂ z₃ hmatch).symm⟩
  · rintro ⟨z₁,z₂,z₃,lam,hn,hamp,_,rfl⟩
    exact amplitude_value_in_spectrum w hex ρ hρ z₁ z₂ z₃ lam hn hamp

/-- Canonical construction, including its positive-root magnitude choices. -/
def exactCommonSpectrum (w : WeightedData K) : Finset K := spectrumValues w (canonicalMagnitudes w)

theorem exactCommonSpectrum_exact (w : WeightedData K) (hex : completeWeightedExceptional w ≠ 0) (ν : K) :
    ν ∈ exactCommonSpectrum w ↔ CommonStationaryValue w ν :=
  common_spectrum_exact w hex (canonicalMagnitudes w) (fun i => (canonicalMagnitudes_spec w i).2) ν

theorem exactCommonSpectrum_nonempty (w : WeightedData K) (hex : completeWeightedExceptional w ≠ 0) :
    (exactCommonSpectrum w).Nonempty :=
  spectrumValues_nonempty w _ ((elementaryExceptional_properties w (mul_ne_zero_iff.mp hex).2).2.1)

theorem exactCommonSpectrum_card_le_fifteen (w : WeightedData K) :
    (exactCommonSpectrum w).card ≤ 15 := spectrumValues_card_le_fifteen w _

#print axioms common_spectrum_exact
#print axioms exactCommonSpectrum_exact
#print axioms amplitude_matches_candidate
#print axioms spectrumCandidates_representable
end RealClosed
end W3.Weighted
