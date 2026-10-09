import W3.FiniteInputRealization

/-! Finite amplitude-coordinate families and stationary witness refinement. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace W3.FiniteInput
open Polynomial W3.Elimination W3.Weighted W3.Infinitesimal W3.OperatorField W3.RealModel
open W3.PrimalFieldBridge W3.TransferOperator W3.StrataTransfer ComplexPair

section Algebra
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem squaredEntry_of_realizations (r s : K) (q v z w : ComplexPair K)
    (hz : conj (mul z z)=scale r q) (hw : conj (mul w w)=scale s v) :
    squaredEntry z w = scale (r*s) (mul v (conj q)) := by
  have hid : squaredEntry z w = mul (conj (conj (mul z z))) (conj (mul w w)) := by
    apply complexPair_ext <;> simp [squaredEntry,mul,conj] <;> ring
  rw [hid,hz,hw]
  apply complexPair_ext <;> simp [scale,mul,conj] <;> ring

theorem pointMatches_of_realizations (x : SpectrumPoint K) (a b c : ComplexPair K)
    (ha : normSq a=x.r₁ ∧ conj (mul a a)=scale x.r₁ onePhase)
    (hb : normSq b=x.r₂ ∧ conj (mul b b)=scale x.r₂ x.q)
    (hc : normSq c=x.r₃ ∧ conj (mul c c)=scale x.r₃ x.v) : PointMatches x a b c := by
  refine ⟨ha.1.symm,hb.1.symm,hc.1.symm,?_,?_,?_⟩
  · simpa [onePhase,mul,conj] using squaredEntry_of_realizations _ _ _ _ _ _ ha.2 hb.2
  · simpa [onePhase,mul,conj] using squaredEntry_of_realizations _ _ _ _ _ _ ha.2 hc.2
  · exact squaredEntry_of_realizations _ _ _ _ _ _ hb.2 hc.2

/-- Contracted stationarity depends only on the exact invariants in PointMatches. -/
theorem pointMatches_amplitude_invariant (k : SpectrumData K) (x : SpectrumPoint K)
    (a b c d e f : ComplexPair K)
    (hz : PointMatches x a b c) (hw : PointMatches x d e f)
    (g1 g2 g3 lam : K) :
    AmplitudeEquations k a b c g1 g2 g3 lam ↔ AmplitudeEquations k d e f g1 g2 g3 lam := by
  obtain ⟨ha,hb,hc,hab,hac,hbc⟩ := hz
  obtain ⟨hd,he,hf,hde,hdf,hef⟩ := hw
  have hab' : amplitudeEdge k.d₁₂ a b = amplitudeEdge k.d₁₂ d e :=
    congrArg (mul k.d₁₂) (hab.trans hde.symm)
  have hac' : amplitudeEdge k.d₁₃ a c = amplitudeEdge k.d₁₃ d f :=
    congrArg (mul k.d₁₃) (hac.trans hdf.symm)
  have hbc' : amplitudeEdge k.d₂₃ b c = amplitudeEdge k.d₂₃ e f :=
    congrArg (mul k.d₂₃) (hbc.trans hef.symm)
  simp only [AmplitudeEquations,amplitudeRow₁,amplitudeRow₂,amplitudeRow₃,
    hab',hac',hbc',← ha,← hb,← hc,← hd,← he,← hf]

end Algebra

variable {n : Nat}
def vectorCode (a b c : ComplexPair (Code n)) : Fin 6 → Code n :=
  ![a.re,a.im,b.re,b.im,c.re,c.im]

section Program
variable {F K : Type*} [Field F] [CharZero F] [DecidableEq F]
    [Field K] [Algebra F K] [LinearOrder K] [IsStrictOrderedRing K]
variable (input : Fin 15 → F) (epsilon : Fin n → F) (O : RealRootEnumeration K)

def runVector (z : Fin 6 → Code n) : RealVector K :=
  fun i => ((z i).run input epsilon O).value

@[simp] theorem run_vectorCode (a b c : ComplexPair (Code n)) :
    runVector input epsilon O (vectorCode a b c) = vectorOfPairs
      (runComplex input epsilon O a) (runComplex input epsilon O b) (runComplex input epsilon O c) := by
  funext i
  fin_cases i <;> rfl

def amplitudeProgram (x : SpectrumPoint (Code n)) : List (Fin 6 → Code n) :=
  (phaseRadiusProgram input epsilon O x.r₁ onePhaseCode).flatMap fun a =>
    (phaseRadiusProgram input epsilon O x.r₂ x.q).flatMap fun b =>
      (phaseRadiusProgram input epsilon O x.r₃ x.v).map fun c => vectorCode a b c

/-- Every output is a literal six-coordinate code vector matching its source point. -/
theorem amplitudeProgram_matches (x : SpectrumPoint (Code n))
    (h1 : 0 ≤ (x.r₁.run input epsilon O).value)
    (h2 : 0 ≤ (x.r₂.run input epsilon O).value)
    (h3 : 0 ≤ (x.r₃.run input epsilon O).value)
    (hq : normSq (runComplex input epsilon O x.q)=1)
    (hv : normSq (runComplex input epsilon O x.v)=1)
    (z : Fin 6 → Code n) (hz : z ∈ amplitudeProgram input epsilon O x) :
    PointMatches (runPoint input epsilon O x)
      (pairVector (runVector input epsilon O z) 0)
      (pairVector (runVector input epsilon O z) 1)
      (pairVector (runVector input epsilon O z) 2) := by
  obtain ⟨a,ha,b,hb,c,hc,rfl⟩ := (by simpa only [amplitudeProgram,List.mem_flatMap,List.mem_map] using hz)
  change PointMatches (runPoint input epsilon O x) (runComplex input epsilon O a)
    (runComplex input epsilon O b) (runComplex input epsilon O c)
  apply pointMatches_of_realizations
  · have h := (phaseRadiusProgram_correct input epsilon O x.r₁ onePhaseCode h1
      (by simp [onePhase,normSq]) (runComplex input epsilon O a)).mp (List.mem_map.mpr ⟨a,ha,rfl⟩)
    simpa only [runPoint,run_onePhase] using h
  · exact (phaseRadiusProgram_correct input epsilon O x.r₂ x.q h2 hq
      (runComplex input epsilon O b)).mp (List.mem_map.mpr ⟨b,hb,rfl⟩)
  · exact (phaseRadiusProgram_correct input epsilon O x.r₃ x.v h3 hv
      (runComplex input epsilon O c)).mp (List.mem_map.mpr ⟨c,hc,rfl⟩)

variable [IsRealClosed K]
theorem phaseRadiusProgram_nonempty (r : Code n) (q : ComplexPair (Code n))
    (hr : 0 ≤ (r.run input epsilon O).value)
    (hq : normSq (runComplex input epsilon O q)=1) :
    (phaseRadiusProgram input epsilon O r q) ≠ [] := by
  obtain ⟨z,hn,hs⟩ := phase_radius_realization (r.run input epsilon O).value
    (runComplex input epsilon O q) hr hq
  obtain ⟨c,hc,_⟩ := List.mem_map.mp ((phaseRadiusProgram_correct input epsilon O r q hr hq z).mpr ⟨hn,hs⟩)
  exact List.ne_nil_of_mem hc

theorem amplitudeProgram_nonempty (x : SpectrumPoint (Code n))
    (h1 : 0 ≤ (x.r₁.run input epsilon O).value)
    (h2 : 0 ≤ (x.r₂.run input epsilon O).value)
    (h3 : 0 ≤ (x.r₃.run input epsilon O).value)
    (hq : normSq (runComplex input epsilon O x.q)=1)
    (hv : normSq (runComplex input epsilon O x.v)=1) :
    amplitudeProgram input epsilon O x ≠ [] := by
  have ha := phaseRadiusProgram_nonempty input epsilon O x.r₁ onePhaseCode h1 (by simp [onePhase,normSq])
  have hb := phaseRadiusProgram_nonempty input epsilon O x.r₂ x.q h2 hq
  have hc := phaseRadiusProgram_nonempty input epsilon O x.r₃ x.v h3 hv
  obtain ⟨a,ham⟩ := List.exists_mem_of_ne_nil _ ha
  obtain ⟨b,hbm⟩ := List.exists_mem_of_ne_nil _ hb
  obtain ⟨c,hcm⟩ := List.exists_mem_of_ne_nil _ hc
  apply List.ne_nil_of_mem (a := vectorCode a b c)
  simp only [amplitudeProgram,List.mem_flatMap,List.mem_map]
  exact ⟨a,ham,b,hbm,c,hcm,rfl⟩

/-- Original candidate guards supply every condition needed by the square-root program. -/
theorem spectrumCandidate_shape (w : WeightedData K)
    (hex : completeWeightedExceptional w ≠ 0) (x : SpectrumPoint K)
    (hx : x ∈ spectrumCandidates w (canonicalMagnitudes w)) :
    0 ≤ x.r₁ ∧ 0 ≤ x.r₂ ∧ 0 ≤ x.r₃ ∧ normSq x.q=1 ∧ normSq x.v=1 ∧ x.r₁+x.r₂+x.r₃=1 := by
  classical
  obtain ⟨he,hel⟩ := mul_ne_zero_iff.mp hex
  have hg := (elementaryExceptional_properties w hel).2.1
  have hph : normSq x.q=1 ∧ normSq x.v=1 := by
    rcases Finset.mem_union.mp hx with hs | hf
    · rcases Finset.mem_union.mp hs with hs | hp
      · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hs
        fin_cases i <;> simp [singletonPoint,onePhase,normSq]
      · obtain ⟨⟨i,s⟩,hi,rfl⟩ := Finset.mem_image.mp hp
        have hr := (Finset.mem_filter.mp hi).2
        have hphase := (pairPhase_correct (pairInput w i).d (canonicalMagnitudes w i) s
          (canonicalMagnitudes_spec w i).2 hr.1).1
        fin_cases i
        · exact ⟨hphase,by simp [pairPoint,onePhase,normSq]⟩
        · exact ⟨by simp [pairPoint,onePhase,normSq],hphase⟩
        · exact ⟨by simp [pairPoint,onePhase,normSq],hphase⟩
    · exact ⟨(fullCandidates_sound w he hg x hf).1,(fullCandidates_sound w he hg x hf).2.1⟩
  obtain ⟨a,b,c,lam,hm,hn,_⟩ := spectrumCandidates_representable w (canonicalMagnitudes w)
    (fun i => (canonicalMagnitudes_spec w i).2) he hg x hx
  refine ⟨?_,?_,?_,hph.1,hph.2,?_⟩
  · rw [hm.1]; exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  · rw [hm.2.1]; exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  · rw [hm.2.2.1]; exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  · rw [hm.1,hm.2.1,hm.2.2.1]; exact hn

/-- The generated vector is a full stationary representation; existence is used
only to prove an invariant, never to choose code or runtime coordinates. -/
theorem amplitudeProgram_representation (w : WeightedData (CoefficientCode n))
    (hex : completeWeightedExceptional (runWeighted (K := K) input epsilon w) ≠ 0)
    (x : SpectrumPoint (Code n)) (hx : x ∈ spectrumProgram input epsilon O w)
    (z : Fin 6 → Code n) (hz : z ∈ amplitudeProgram input epsilon O x) :
    VectorRepresentation (runWeighted (K := K) input epsilon w) (runPoint input epsilon O x)
      (runVector input epsilon O z) := by
  let v := runWeighted (K := K) input epsilon w
  have he := (mul_ne_zero_iff.mp hex).1
  have hS := (phaseExceptional_properties (weightedP v) (weightedQ v) (weightedPole v) he).1
  have hxc := (spectrumProgram_correct input epsilon O w hS _).mp (List.mem_map.mpr ⟨x,hx,rfl⟩)
  obtain ⟨h1,h2,h3,hq,hv,hsum⟩ := spectrumCandidate_shape v hex _ hxc
  have hm := amplitudeProgram_matches input epsilon O x h1 h2 h3 hq hv z hz
  have hg := (elementaryExceptional_properties v (mul_ne_zero_iff.mp hex).2).2.1
  obtain ⟨a,b,c,lam,hm',hn',hG',hamp'⟩ := spectrumCandidates_representable v (canonicalMagnitudes v)
    (fun i => (canonicalMagnitudes_spec v i).2) he hg _ hxc
  refine ⟨hm,?_,?_,lam,?_⟩
  · rw [← pairVector_norm_sum,← hm.1,← hm.2.1,← hm.2.2.1]
    exact hsum
  · rwa [← hm.1,← hm.2.1,← hm.2.2.1,hm'.1,hm'.2.1,hm'.2.2.1]
  · exact (pointMatches_amplitude_invariant (toSpectrum v) _ a b c _ _ _ hm' hm
      v.g1 v.g2 v.g3 lam).mp hamp'

theorem amplitudeProgram_candidate_nonempty (w : WeightedData (CoefficientCode n))
    (hex : completeWeightedExceptional (runWeighted (K := K) input epsilon w) ≠ 0)
    (x : SpectrumPoint (Code n)) (hx : x ∈ spectrumProgram input epsilon O w) :
    amplitudeProgram input epsilon O x ≠ [] := by
  let v := runWeighted (K := K) input epsilon w
  have he := (mul_ne_zero_iff.mp hex).1
  have hS := (phaseExceptional_properties (weightedP v) (weightedQ v) (weightedPole v) he).1
  have hxc := (spectrumProgram_correct input epsilon O w hS _).mp (List.mem_map.mpr ⟨x,hx,rfl⟩)
  obtain ⟨h1,h2,h3,hq,hv,_⟩ := spectrumCandidate_shape v hex _ hxc
  exact amplitudeProgram_nonempty input epsilon O x h1 h2 h3 hq hv

#print axioms amplitudeProgram_representation
#print axioms amplitudeProgram_candidate_nonempty

end Program
end W3.FiniteInput
