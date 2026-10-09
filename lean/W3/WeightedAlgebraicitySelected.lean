import W3.WeightedAlgebraicityWitnesses

noncomputable section
namespace W3.Weighted
open W3.Elimination Polynomial
section Algebraic
variable {F L : Type*} [Field F] [Field L] [Algebra F L] [LinearOrder L] [IsStrictOrderedRing L]

/-- The checked exceptional condition in the ambient field proves that the
sextic over the smaller coefficient presentation is nonzero. -/
theorem base_sextic_ne_zero_of_mapped_generic (w : WeightedData F)
    (he : weightedExceptional (mapWeighted (algebraMap F L) w) ≠ 0) :
    phaseSextic (weightedP w) (weightedQ w) ≠ 0 := by
  have hs := (phaseExceptional_properties
    (weightedP (mapWeighted (algebraMap F L) w))
    (weightedQ (mapWeighted (algebraMap F L) w))
    (weightedPole (mapWeighted (algebraMap F L) w)) he).1
  intro hz
  apply hs
  rw [← map_weightedP,← map_weightedQ,← map_phaseSextic,hz,Polynomial.map_zero]

/-- Actual selected values, without an assumed polynomial annihilator. -/
theorem selected_value_algebraic (w : WeightedData F)
    (he : weightedExceptional (mapWeighted (algebraMap F L) w) ≠ 0)
    (ρ : Fin 3 → L) (hρ : ∀ i, (ρ i)^2 = ComplexPair.normSq (pairInput (mapWeighted (algebraMap F L) w) i).d)
    (ν : L) (hm : ν ∈ spectrumValues (mapWeighted (algebraMap F L) w) ρ) : IsAlgebraic F ν := by
  classical
  unfold spectrumValues at hm
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hm
  exact spectrumValue_algebraic w x
    (spectrumCandidates_algebraic w (base_sextic_ne_zero_of_mapped_generic w he) ρ hρ x hx)

/-- All physical projector coordinates from the actual selected spectrum are
algebraic over its coefficient field, with genericity supplying nonzero sextic. -/
theorem selected_matched_projector_algebraic (w : WeightedData F)
    (he : weightedExceptional (mapWeighted (algebraMap F L) w) ≠ 0)
    (ρ : Fin 3 → L) (hρ : ∀ i, (ρ i)^2 = ComplexPair.normSq (pairInput (mapWeighted (algebraMap F L) w) i).d)
    (x : SpectrumPoint L) (hm : x ∈ spectrumCandidates (mapWeighted (algebraMap F L) w) ρ)
    (z₁ z₂ z₃ : ComplexPair L) (hmatch : PointMatches x z₁ z₂ z₃) :
    IsAlgebraic F (ComplexPair.normSq z₁) ∧ IsAlgebraic F (ComplexPair.normSq z₂) ∧
    IsAlgebraic F (ComplexPair.normSq z₃) ∧
    AlgebraicPair F (ComplexPair.mul z₁ (ComplexPair.conj z₂)) ∧
    AlgebraicPair F (ComplexPair.mul z₁ (ComplexPair.conj z₃)) ∧
    AlgebraicPair F (ComplexPair.mul z₂ (ComplexPair.conj z₃)) :=
  selected_projector_algebraic w (base_sextic_ne_zero_of_mapped_generic w he) ρ hρ x hm z₁ z₂ z₃ hmatch

variable [IsRealClosed L]

/-- Canonical magnitude root selection and duplicate-value removal preserve
algebraicity of every selected common-spectrum value. -/
theorem exactCommonSpectrum_algebraic (w : WeightedData F)
    (he : weightedExceptional (mapWeighted (algebraMap F L) w) ≠ 0)
    (ν : L) (hm : ν ∈ exactCommonSpectrum (mapWeighted (algebraMap F L) w)) : IsAlgebraic F ν :=
  selected_value_algebraic w he _ (fun i => (canonicalMagnitudes_spec _ i).2) ν hm

#print axioms exactCommonSpectrum_algebraic
#print axioms selected_matched_projector_algebraic
end Algebraic
end W3.Weighted
