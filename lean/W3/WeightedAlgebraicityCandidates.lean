import W3.WeightedAlgebraicity

noncomputable section
namespace W3.Weighted
open W3.Elimination Polynomial
section Algebraic
variable {F L : Type*} [Field F] [Field L] [Algebra F L] [LinearOrder L] [IsStrictOrderedRing L]

lemma algebraic_branchSign (s : Bool) : IsAlgebraic F (branchSign s : L) := by
  cases s
  · exact (isAlgebraic_one (R:=F) (A:=L)).neg
  · exact isAlgebraic_one

def AlgebraicPairInput (F : Type*) [Field F] [Algebra F L] (p : PairInput L) : Prop :=
  IsAlgebraic F p.a ∧ IsAlgebraic F p.b ∧ IsAlgebraic F p.e ∧
    AlgebraicPair F p.d ∧ IsAlgebraic F p.g₁ ∧ IsAlgebraic F p.g₂

lemma algebraic_mapped_pairInput (w : WeightedData F) (i : Fin 3) :
    AlgebraicPairInput F (pairInput (mapWeighted (algebraMap F L) w) i) := by
  fin_cases i <;> exact ⟨isAlgebraic_algebraMap _,isAlgebraic_algebraMap _,isAlgebraic_algebraMap _,
    ⟨isAlgebraic_algebraMap _,isAlgebraic_algebraMap _⟩,isAlgebraic_algebraMap _,isAlgebraic_algebraMap _⟩

lemma algebraic_pair_parameters (p : PairInput L) (hp : AlgebraicPairInput F p) (ρ : L)
    (hρ : IsAlgebraic F ρ) (s : Bool) :
    IsAlgebraic F (pairLeft p ρ s) ∧ IsAlgebraic F (pairRight p ρ s) ∧
      AlgebraicPair F (pairPhase p.d ρ s) := by
  obtain ⟨ha,hb,he,hd,hg₁,hg₂⟩ := hp
  have h2 : IsAlgebraic F (2 : L) := isAlgebraic_natCast 2
  have hs := algebraic_branchSign (F:=F) (L:=L) s
  have hh : IsAlgebraic F (pairH p ρ s) := algebraic_div (he.add (hs.mul hρ)) h2
  have hn₁ : IsAlgebraic F (pairN₁ (p.a/2) (p.b/2) (pairH p ρ s) p.g₁ p.g₂) :=
    ((algebraic_div hb h2).mul hg₁).sub (hh.mul hg₂)
  have hn₂ : IsAlgebraic F (pairN₂ (p.a/2) (p.b/2) (pairH p ρ s) p.g₁ p.g₂) :=
    ((algebraic_div ha h2).mul hg₂).sub (hh.mul hg₁)
  have hN : IsAlgebraic F (pairSum p ρ s) := hn₁.add hn₂
  exact ⟨algebraic_div hn₁ hN,algebraic_div hn₂ hN,
    algebraic_div (hs.mul hd.1) hρ,algebraic_div (hs.mul hd.2).neg hρ⟩

theorem pairPoint_algebraic (w : WeightedData F) (ρ : Fin 3 → L) (i : Fin 3) (s : Bool)
    (hρ : IsAlgebraic F (ρ i)) :
    AlgebraicPoint F (pairPoint (mapWeighted (algebraMap F L) w) ρ i s) := by
  obtain ⟨hl,hr,hq⟩ := algebraic_pair_parameters _ (algebraic_mapped_pairInput w i) (ρ i) hρ s
  fin_cases i
  · exact ⟨hl,hr,isAlgebraic_zero,hq,algebraic_onePhase⟩
  · exact ⟨hl,isAlgebraic_zero,hr,algebraic_onePhase,hq⟩
  · exact ⟨isAlgebraic_zero,hl,hr,algebraic_onePhase,hq⟩

theorem singletonPoint_algebraic (i : Fin 3) : AlgebraicPoint F (singletonPoint (K:=L) i) := by
  fin_cases i
  · exact ⟨isAlgebraic_one,isAlgebraic_zero,isAlgebraic_zero,algebraic_onePhase,algebraic_onePhase⟩
  · exact ⟨isAlgebraic_zero,isAlgebraic_one,isAlgebraic_zero,algebraic_onePhase,algebraic_onePhase⟩
  · exact ⟨isAlgebraic_zero,isAlgebraic_zero,isAlgebraic_one,algebraic_onePhase,algebraic_onePhase⟩

/-- A supplied exact magnitude is algebraic from its defining quadratic;
its algebraicity is not a premise of the selected-candidate theorem. -/
theorem exact_magnitude_algebraic (w : WeightedData F) (i : Fin 3) (ρ : L)
    (hρ : ρ^2 = ComplexPair.normSq (pairInput (mapWeighted (algebraMap F L) w) i).d) :
    IsAlgebraic F ρ := by
  have hp := algebraic_mapped_pairInput (F:=F) (L:=L) w i
  apply IsAlgebraic.of_pow (n:=2) (by decide)
  rw [hρ]
  exact (hp.2.2.2.1.1.pow 2).add (hp.2.2.2.1.2.pow 2)

/-- Every point in the actual finite spectrum has algebraic radii and phase
coordinates over the coefficient presentation F. -/
theorem spectrumCandidates_algebraic (w : WeightedData F)
    (hS : phaseSextic (weightedP w) (weightedQ w) ≠ 0)
    (ρ : Fin 3 → L) (hρ : ∀ i, (ρ i)^2 = ComplexPair.normSq (pairInput (mapWeighted (algebraMap F L) w) i).d)
    (x : SpectrumPoint L) (hm : x ∈ spectrumCandidates (mapWeighted (algebraMap F L) w) ρ) :
    AlgebraicPoint F x := by
  classical
  simp only [spectrumCandidates,Finset.mem_union] at hm
  rcases hm with (hs | hp) | hf
  · unfold singletonCandidates at hs
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hs
    exact singletonPoint_algebraic i
  · unfold pairCandidates at hp
    obtain ⟨⟨i,s⟩,_,rfl⟩ := Finset.mem_image.mp hp
    exact pairPoint_algebraic w ρ i s (exact_magnitude_algebraic w i (ρ i) (hρ i))
  · unfold fullCandidates at hf
    obtain ⟨⟨t,u⟩,hfilter,rfl⟩ := Finset.mem_image.mp hf
    exact selected_fullPoint_algebraic w t u hS (Finset.mem_filter.mp hfilter).1

/-- The actual weighted quotient values are algebraic as well. -/
theorem spectrumValue_algebraic (w : WeightedData F) (x : SpectrumPoint L)
    (hx : AlgebraicPoint F x) :
    IsAlgebraic F (spectrumValue (mapWeighted (algebraMap F L) w) x) := by
  obtain ⟨hr₁,hr₂,hr₃,hq,hv⟩ := hx
  have hd₁₂ : AlgebraicPair F (toSpectrum (mapWeighted (algebraMap F L) w)).d₁₂ :=
    ⟨isAlgebraic_algebraMap _,isAlgebraic_algebraMap _⟩
  have hd₁₃ : AlgebraicPair F (toSpectrum (mapWeighted (algebraMap F L) w)).d₁₃ :=
    ⟨isAlgebraic_algebraMap _,isAlgebraic_algebraMap _⟩
  have hd₂₃ : AlgebraicPair F (toSpectrum (mapWeighted (algebraMap F L) w)).d₂₃ :=
    ⟨isAlgebraic_algebraMap _,isAlgebraic_algebraMap _⟩
  have he₁₂ := (algebraicPair_mul hd₁₂ hq).1
  have he₁₃ := (algebraicPair_mul hd₁₃ hv).1
  have he₂₃ := (algebraicPair_mul hd₂₃ (algebraicPair_mul hv (algebraicPair_conj hq))).1
  have hB₁ : IsAlgebraic F (twiceB₁ (toSpectrum (mapWeighted (algebraMap F L) w)) x.q x.v x.r₁ x.r₂ x.r₃) :=
    (((isAlgebraic_algebraMap _).mul hr₁).add
      (((isAlgebraic_algebraMap _).add he₁₂).mul hr₂)).add
      (((isAlgebraic_algebraMap _).add he₁₃).mul hr₃)
  have hB₂ : IsAlgebraic F (twiceB₂ (toSpectrum (mapWeighted (algebraMap F L) w)) x.q x.v x.r₁ x.r₂ x.r₃) :=
    ((((isAlgebraic_algebraMap _).add he₁₂).mul hr₁).add
      ((isAlgebraic_algebraMap _).mul hr₂)).add
      (((isAlgebraic_algebraMap _).add he₂₃).mul hr₃)
  have hB₃ : IsAlgebraic F (twiceB₃ (toSpectrum (mapWeighted (algebraMap F L) w)) x.q x.v x.r₁ x.r₂ x.r₃) :=
    ((((isAlgebraic_algebraMap _).add he₁₃).mul hr₁).add
      (((isAlgebraic_algebraMap _).add he₂₃).mul hr₂)).add
      ((isAlgebraic_algebraMap _).mul hr₃)
  have hG : IsAlgebraic F ((mapWeighted (algebraMap F L) w).g1*x.r₁+
      (mapWeighted (algebraMap F L) w).g2*x.r₂+(mapWeighted (algebraMap F L) w).g3*x.r₃) :=
    (((isAlgebraic_algebraMap _).mul hr₁).add ((isAlgebraic_algebraMap _).mul hr₂)).add
      ((isAlgebraic_algebraMap _).mul hr₃)
  exact algebraic_div (((hr₁.mul hB₁).add (hr₂.mul hB₂)).add (hr₃.mul hB₃))
    ((isAlgebraic_natCast 2).mul (hG.pow 2))

end Algebraic
end W3.Weighted
