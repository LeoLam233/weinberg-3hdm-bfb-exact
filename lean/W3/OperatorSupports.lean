import W3.WeightedSpectrum

/-! Exact singleton and pair support candidate soundness and coverage. -/
noncomputable section
namespace W3.Weighted
open ComplexPair W3.Elimination
section Ordered
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

lemma branchSign_sq (s : Bool) : (branchSign s : K) ^ 2 = 1 := by cases s <;> norm_num [branchSign]

lemma pairPhase_correct (d : ComplexPair K) (ρ : K) (s : Bool)
    (hρ : ρ ^ 2 = normSq d) (hρ₀ : ρ ≠ 0) :
    normSq (pairPhase d ρ s) = 1 ∧ (mul d (pairPhase d ρ s)).im = 0 ∧
      (mul d (pairPhase d ρ s)).re = branchSign s * ρ := by
  cases s
  · have h := pair_phase_construct d (-ρ) (by simpa using hρ) (neg_ne_zero.mpr hρ₀)
    simpa [pairPhase, branchSign, div_neg, neg_div] using h
  · simpa [pairPhase, branchSign] using pair_phase_construct d ρ hρ hρ₀

lemma pairPoint_weight (w : WeightedData K) (ρ : Fin 3 → K) (i : Fin 3) (s : Bool) :
    spectrumWeight w (pairPoint w ρ i s) =
      (pairInput w i).g₁ * pairLeft (pairInput w i) (ρ i) s +
      (pairInput w i).g₂ * pairRight (pairInput w i) (ρ i) s := by
  fin_cases i <;> simp [pairPoint, pairInput, spectrumWeight]

lemma spectrumValue_pair12 (w : WeightedData K) (l r : K) (q : ComplexPair K) :
    spectrumValue w ⟨l,r,0,q,onePhase⟩ =
      ((w.alpha1/2)*l^2 + (w.e12 + (mul ⟨w.d12r,w.d12i⟩ q).re)*l*r + (w.alpha2/2)*r^2) /
        (w.g1*l+w.g2*r)^2 := by
  simp [spectrumValue, weightedQuotient, toSpectrum, twiceB₁, twiceB₂, twiceB₃, edge₁₂, edge₁₃, edge₂₃]
  rw [div_mul_eq_div_div]
  congr 1
  ring

lemma spectrumValue_pair13 (w : WeightedData K) (l r : K) (q : ComplexPair K) :
    spectrumValue w ⟨l,0,r,onePhase,q⟩ =
      ((w.alpha1/2)*l^2 + (w.e13 + (mul ⟨w.d13r,w.d13i⟩ q).re)*l*r + (w.alpha3/2)*r^2) /
        (w.g1*l+w.g3*r)^2 := by
  simp [spectrumValue, weightedQuotient, toSpectrum, twiceB₁, twiceB₂, twiceB₃, edge₁₂, edge₁₃, edge₂₃]
  rw [div_mul_eq_div_div]
  congr 1
  ring

lemma spectrumValue_pair23 (w : WeightedData K) (l r : K) (q : ComplexPair K) :
    spectrumValue w ⟨0,l,r,onePhase,q⟩ =
      ((w.alpha2/2)*l^2 + (w.e23 + (mul ⟨w.d23r,w.d23i⟩ q).re)*l*r + (w.alpha3/2)*r^2) /
        (w.g2*l+w.g3*r)^2 := by
  simp [spectrumValue, weightedQuotient, toSpectrum, twiceB₁, twiceB₂, twiceB₃,
    edge₁₂, edge₁₃, edge₂₃, onePhase, mul, conj]
  rw [div_mul_eq_div_div]
  congr 1
  ring

lemma pairPoint_value (w : WeightedData K) (ρ : Fin 3 → K) (i : Fin 3) (s : Bool)
    (hρ : (ρ i)^2 = normSq (pairInput w i).d) (hρ₀ : ρ i ≠ 0) :
    spectrumValue w (pairPoint w ρ i s) =
      (((pairInput w i).a/2)*(pairLeft (pairInput w i) (ρ i) s)^2 +
        2*pairH (pairInput w i) (ρ i) s*pairLeft (pairInput w i) (ρ i) s*pairRight (pairInput w i) (ρ i) s +
        ((pairInput w i).b/2)*(pairRight (pairInput w i) (ρ i) s)^2) /
      ((pairInput w i).g₁*pairLeft (pairInput w i) (ρ i) s+
       (pairInput w i).g₂*pairRight (pairInput w i) (ρ i) s)^2 := by
  have hp := (pairPhase_correct (pairInput w i).d (ρ i) s hρ hρ₀).2.2
  fin_cases i <;> dsimp [pairPoint, pairInput] at hp ⊢
  · rw [spectrumValue_pair12, hp]
    unfold pairH
    ring
  · rw [spectrumValue_pair13, hp]
    unfold pairH
    ring
  · rw [spectrumValue_pair23, hp]
    unfold pairH
    ring

/-- Every retained pair branch has exactly the printed energy and normalized
positive radii, including zero determinant/zero energy. -/
theorem retained_pair_formula (w : WeightedData K) (ρ : Fin 3 → K) (i : Fin 3) (s : Bool)
    (hρ : (ρ i)^2 = normSq (pairInput w i).d) (hr : PairRetained w ρ i s) :
    pairLeft (pairInput w i) (ρ i) s + pairRight (pairInput w i) (ρ i) s = 1 ∧
      spectrumValue w (pairPoint w ρ i s) =
        pairDet ((pairInput w i).a/2) ((pairInput w i).b/2) (pairH (pairInput w i) (ρ i) s) /
          pairW ((pairInput w i).a/2) ((pairInput w i).b/2) (pairH (pairInput w i) (ρ i) s)
            (pairInput w i).g₁ (pairInput w i).g₂ := by
  rcases hr with ⟨hρ₀,hW,hN,hl,hr,hG⟩
  constructor
  · unfold pairLeft pairRight
    rw [← add_div]
    exact div_self hN
  · rw [pairPoint_value w ρ i s hρ hρ₀]
    apply (pair_stationary_value _ _ _ _ _ _ _ _ ?_ ?_).symm
    · rwa [← pairPoint_weight]
    · exact pair_reconstruction_stationary _ _ _ _ _ hW hN

/-- Pair amplitude stationarity reconstructs an actual member of the finite
six-branch candidate set, including its phase and exact quotient value. -/
theorem pair_amplitude_candidate (w : WeightedData K) (ρ : Fin 3 → K) (i : Fin 3)
    (z₁ z₂ : ComplexPair K) (lam : K)
    (h₁ : 0 < normSq z₁) (h₂ : 0 < normSq z₂) (hn : normSq z₁+normSq z₂=1)
    (hG : (pairInput w i).g₁*normSq z₁+(pairInput w i).g₂*normSq z₂ ≠ 0)
    (hρ : (ρ i)^2 = normSq (pairInput w i).d) (hρ₀ : ρ i ≠ 0)
    (hW : ∀ s, pairW ((pairInput w i).a/2) ((pairInput w i).b/2)
      (pairH (pairInput w i) (ρ i) s) (pairInput w i).g₁ (pairInput w i).g₂ ≠ 0)
    (he : PairAmplitudeEquations (pairInput w i).a (pairInput w i).b (pairInput w i).e
      (pairInput w i).d z₁ z₂ (pairInput w i).g₁ (pairInput w i).g₂ lam) :
    ∃ s : Bool, pairPoint w ρ i s ∈ pairCandidates w ρ ∧
      pairLeft (pairInput w i) (ρ i) s = normSq z₁ ∧
      pairRight (pairInput w i) (ρ i) s = normSq z₂ ∧
      pairPhase (pairInput w i).d (ρ i) s = relativePhase z₁ z₂ ∧
      spectrumValue w (pairPoint w ρ i s) =
        lam/(2*((pairInput w i).g₁*normSq z₁+(pairInput w i).g₂*normSq z₂)) := by
  classical
  obtain ⟨hphase,hrad⟩ := pair_amplitude_radial _ _ _ _ z₁ z₂ _ _ lam h₁.ne' h₂.ne' hG he
  have finish (s : Bool) (hp : pairPhase (pairInput w i).d (ρ i) s = relativePhase z₁ z₂)
      (hv : (mul (pairInput w i).d (relativePhase z₁ z₂)).re = branchSign s * ρ i) :
      ∃ s : Bool, pairPoint w ρ i s ∈ pairCandidates w ρ ∧
        pairLeft (pairInput w i) (ρ i) s = normSq z₁ ∧
        pairRight (pairInput w i) (ρ i) s = normSq z₂ ∧
        pairPhase (pairInput w i).d (ρ i) s = relativePhase z₁ z₂ ∧
        spectrumValue w (pairPoint w ρ i s) =
          lam/(2*((pairInput w i).g₁*normSq z₁+(pairInput w i).g₂*normSq z₂)) := by
    rw [hv] at hrad
    obtain ⟨hN,hl,hr,hν⟩ := pair_stationary_reconstruction _ _ _ _ _ _ _ _ (hW s) hG hn hrad
    have hl' : pairLeft (pairInput w i) (ρ i) s = normSq z₁ := hl.symm
    have hr' : pairRight (pairInput w i) (ρ i) s = normSq z₂ := hr.symm
    have hret : PairRetained w ρ i s := by
      refine ⟨hρ₀,hW s,hN,?_,?_,?_⟩
      · rw [hl']; exact h₁
      · rw [hr']; exact h₂
      · rw [pairPoint_weight,hl',hr']; exact hG
    refine ⟨s,?_,hl',hr',hp,?_⟩
    · apply Finset.mem_image.mpr
      exact ⟨(i,s),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hret⟩,rfl⟩
    · exact (retained_pair_formula w ρ i s hρ hret).2.trans hν.symm
  rcases pair_phase_alignment (pairInput w i).d (relativePhase z₁ z₂) (ρ i)
      (relativePhase_norm z₁ z₂ h₁.ne' h₂.ne') hρ hρ₀ hphase with hp | hm
  · apply finish true
    · apply complexPair_ext <;> simp [pairPhase,branchSign,hp.1,hp.2.1]
    · simpa [branchSign] using hp.2.2
  · apply finish false
    · apply complexPair_ext <;> simp [pairPhase,branchSign,hm.1,hm.2.1]
    · simpa [branchSign] using hm.2.2

lemma singletonPoint_value (w : WeightedData K) (i : Fin 3) :
    spectrumValue w (singletonPoint i) =
      (![w.alpha1,w.alpha2,w.alpha3] i)/(2*(![w.g1,w.g2,w.g3] i)^2) := by
  fin_cases i <;> simp [spectrumValue, singletonPoint, weightedQuotient, toSpectrum,
    twiceB₁, twiceB₂, twiceB₃]

lemma singletonPoint_mem (w : WeightedData K) (i : Fin 3)
    (hg : ![w.g1,w.g2,w.g3] i ≠ 0) : singletonPoint i ∈ singletonCandidates w := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
  fin_cases i <;> simpa [spectrumWeight,singletonPoint] using hg

#print axioms pair_amplitude_candidate
#print axioms retained_pair_formula
end Ordered
end W3.Weighted
