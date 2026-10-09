import W3.WeightedAlgebraicityCanonical
import W3.InfinitesimalPresentedExpression

/-! Exact finite selected-root expressions for the actual common-spectrum
construction. Primitive equations are supplied directly, not chosen from
an abstract algebraicity existence proof. -/
noncomputable section
namespace W3.Weighted.Expression
open W3.Elimination W3.Infinitesimal Polynomial ComplexPair

lemma expr_algebraMap {R A : Type*} [Field R] [Field A] [Algebra R A] (a : R) :
    Presented R (algebraMap R A a) := presented_algebraMap a
lemma expr_natCast {R A : Type*} [Field R] [Field A] [Algebra R A] (n : ℕ) :
    Presented R (n : A) := by simpa only [map_natCast] using (presented_algebraMap (F:=R) (L:=A) (n : R))
lemma expr_one {R A : Type*} [Field R] [Field A] [Algebra R A] : Presented R (1 : A) :=
  Presented.one
lemma expr_zero {R A : Type*} [Field R] [Field A] [Algebra R A] : Presented R (0 : A) :=
  Presented.zero

section Presented
variable {F L : Type*} [Field F] [Field L] [Algebra F L]

lemma presented_div {x y : L} (hx : Presented F x) (hy : Presented F y) :
    Presented F (x/y) := by
  rw [div_eq_mul_inv]
  exact hx.mul hy.inv

lemma presented_eval₂ {x : L} (hx : Presented F x) (p : F[X]) :
    Presented F (p.eval₂ (algebraMap F L) x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.eval₂_add]; exact hp.add hq
  | monomial n a =>
    rw [Polynomial.eval₂_monomial]
    exact (expr_algebraMap a).mul (hx.pow n)

variable [LinearOrder L] [IsStrictOrderedRing L]

/-- Nonzero mapped sextic roots are presented over the genuine coefficient
field; the theorem does not silently enlarge that field to the ambient L. -/
theorem selected_phase_presented (p q : PhaseRow F) (t u : L)
    (hS : phaseSextic p q ≠ 0)
    (hm : (t,u) ∈ phaseCandidates (mapRow (algebraMap F L) p) (mapRow (algebraMap F L) q)) :
    Presented F t ∧ Presented F u := by
  classical
  unfold phaseCandidates at hm
  obtain ⟨v,hroot,heq⟩ := Finset.mem_image.mp hm
  have hvt : v = t := congrArg Prod.fst heq
  subst v
  have hroot' : ((phaseSextic p q).map (algebraMap F L)).eval t = 0 := by
    rw [map_phaseSextic]
    exact (mem_roots (by rw [← map_phaseSextic]; exact (Polynomial.map_ne_zero_iff (RingHom.injective _)).mpr hS)).mp
      (Multiset.mem_toFinset.mp hroot)
  have ht : Presented F t := presented_selectedRoot (phaseSextic p q) hS (by simpa only [Polynomial.aeval_def,Polynomial.eval_map] using hroot')
  have hu := (congrArg Prod.snd heq).symm
  change u = -(phaseLinearZero (mapRow (algebraMap F L) p) (mapRow (algebraMap F L) q)).eval t /
    (phaseLinearOne (mapRow (algebraMap F L) p) (mapRow (algebraMap F L) q)).eval t at hu
  rw [hu,← map_phaseLinearZero,← map_phaseLinearOne,Polynomial.eval_map,Polynomial.eval_map]
  exact ⟨ht,presented_div (presented_eval₂ ht _).neg (presented_eval₂ ht _)⟩


def PresentedPair (F : Type*) [Field F] [Algebra F L] (z : ComplexPair L) : Prop :=
  Presented F z.re ∧ Presented F z.im

def PresentedPoint (F : Type*) [Field F] [Algebra F L] (x : SpectrumPoint L) : Prop :=
  Presented F x.r₁ ∧ Presented F x.r₂ ∧ Presented F x.r₃ ∧
  PresentedPair F x.q ∧ PresentedPair F x.v

lemma presentedPair_mul {z w : ComplexPair L} (hz : PresentedPair F z) (hw : PresentedPair F w) :
    PresentedPair F (ComplexPair.mul z w) :=
  ⟨(hz.1.mul hw.1).sub (hz.2.mul hw.2),(hz.1.mul hw.2).add (hz.2.mul hw.1)⟩
lemma presentedPair_conj {z : ComplexPair L} (hz : PresentedPair F z) :
    PresentedPair F (ComplexPair.conj z) := ⟨hz.1,hz.2.neg⟩
lemma presentedPair_scale {a : L} {z : ComplexPair L} (ha : Presented F a) (hz : PresentedPair F z) :
    PresentedPair F (ComplexPair.scale a z) := ⟨ha.mul hz.1,ha.mul hz.2⟩
lemma presented_onePhase : PresentedPair F (onePhase : ComplexPair L) :=
  ⟨expr_one,expr_zero⟩

lemma presented_circlePoint {x y : L} (hx : Presented F x) (hy : Presented F y) :
    PresentedPair F (circlePoint x y) := by
  have hd := (hx.pow 2).add (hy.pow 2)
  exact ⟨presented_div ((hx.pow 2).sub (hy.pow 2)) hd,
    presented_div (((expr_natCast 2).mul hx).mul hy) hd⟩

/-- All rational full-support reconstruction coordinates are presented over
F once the selected sextic/root-recovery coordinates are presented over F. -/
theorem fullPoint_presented (w : WeightedData F) (t u : L)
    (ht : Presented F t) (hu : Presented F u) :
    PresentedPoint F (fullPoint (mapWeighted (algebraMap F L) w) t u) := by
  have hq := presented_circlePoint (expr_one (R:=F) (A:=L)) ht
  have hv := presented_circlePoint (expr_one (R:=F) (A:=L)) hu
  have hd₁₂ : PresentedPair F (toSpectrum (mapWeighted (algebraMap F L) w)).d₁₂ :=
    ⟨expr_algebraMap _,expr_algebraMap _⟩
  have hd₁₃ : PresentedPair F (toSpectrum (mapWeighted (algebraMap F L) w)).d₁₃ :=
    ⟨expr_algebraMap _,expr_algebraMap _⟩
  have hd₂₃ : PresentedPair F (toSpectrum (mapWeighted (algebraMap F L) w)).d₂₃ :=
    ⟨expr_algebraMap _,expr_algebraMap _⟩
  have hs₁₂ := (presentedPair_mul hd₁₂ hq).2
  have hs₁₃ := (presentedPair_mul hd₁₃ hv).2
  have hs₂₃ := (presentedPair_mul hd₂₃ (presentedPair_mul hv (presentedPair_conj hq))).2
  have hD := (hs₂₃.sub hs₁₃).add hs₁₂
  exact ⟨presented_div hs₂₃ hD,presented_div hs₁₃.neg hD,presented_div hs₁₂ hD,hq,hv⟩

/-- Direct actual-list version: sextic membership supplies both root finite-expression representability
hypotheses, including the recovered second coordinate. -/
theorem selected_fullPoint_presented (w : WeightedData F) (t u : L)
    (hS : phaseSextic (weightedP w) (weightedQ w) ≠ 0)
    (hm : (t,u) ∈ phaseCandidates (weightedP (mapWeighted (algebraMap F L) w))
      (weightedQ (mapWeighted (algebraMap F L) w))) :
    PresentedPoint F (fullPoint (mapWeighted (algebraMap F L) w) t u) := by
  rw [← map_weightedP,← map_weightedQ] at hm
  obtain ⟨ht,hu⟩ := selected_phase_presented (weightedP w) (weightedQ w) t u hS hm
  exact fullPoint_presented w t u ht hu

end Presented

section Presented
variable {F L : Type*} [Field F] [Field L] [Algebra F L] [LinearOrder L] [IsStrictOrderedRing L]

lemma presented_branchSign (s : Bool) : Presented F (branchSign s : L) := by
  cases s
  · exact (expr_one (R:=F) (A:=L)).neg
  · exact expr_one

def PresentedPairInput (F : Type*) [Field F] [Algebra F L] (p : PairInput L) : Prop :=
  Presented F p.a ∧ Presented F p.b ∧ Presented F p.e ∧
    PresentedPair F p.d ∧ Presented F p.g₁ ∧ Presented F p.g₂

lemma presented_mapped_pairInput (w : WeightedData F) (i : Fin 3) :
    PresentedPairInput F (pairInput (mapWeighted (algebraMap F L) w) i) := by
  fin_cases i <;> exact ⟨expr_algebraMap _,expr_algebraMap _,expr_algebraMap _,
    ⟨expr_algebraMap _,expr_algebraMap _⟩,expr_algebraMap _,expr_algebraMap _⟩

lemma presented_pair_parameters (p : PairInput L) (hp : PresentedPairInput F p) (ρ : L)
    (hρ : Presented F ρ) (s : Bool) :
    Presented F (pairLeft p ρ s) ∧ Presented F (pairRight p ρ s) ∧
      PresentedPair F (pairPhase p.d ρ s) := by
  obtain ⟨ha,hb,he,hd,hg₁,hg₂⟩ := hp
  have h2 : Presented F (2 : L) := expr_natCast 2
  have hs := presented_branchSign (F:=F) (L:=L) s
  have hh : Presented F (pairH p ρ s) := presented_div (he.add (hs.mul hρ)) h2
  have hn₁ : Presented F (pairN₁ (p.a/2) (p.b/2) (pairH p ρ s) p.g₁ p.g₂) :=
    ((presented_div hb h2).mul hg₁).sub (hh.mul hg₂)
  have hn₂ : Presented F (pairN₂ (p.a/2) (p.b/2) (pairH p ρ s) p.g₁ p.g₂) :=
    ((presented_div ha h2).mul hg₂).sub (hh.mul hg₁)
  have hN : Presented F (pairSum p ρ s) := hn₁.add hn₂
  exact ⟨presented_div hn₁ hN,presented_div hn₂ hN,
    presented_div (hs.mul hd.1) hρ,presented_div (hs.mul hd.2).neg hρ⟩

theorem pairPoint_presented (w : WeightedData F) (ρ : Fin 3 → L) (i : Fin 3) (s : Bool)
    (hρ : Presented F (ρ i)) :
    PresentedPoint F (pairPoint (mapWeighted (algebraMap F L) w) ρ i s) := by
  obtain ⟨hl,hr,hq⟩ := presented_pair_parameters _ (presented_mapped_pairInput w i) (ρ i) hρ s
  fin_cases i
  · exact ⟨hl,hr,expr_zero,hq,presented_onePhase⟩
  · exact ⟨hl,expr_zero,hr,presented_onePhase,hq⟩
  · exact ⟨expr_zero,hl,hr,presented_onePhase,hq⟩

theorem singletonPoint_presented (i : Fin 3) : PresentedPoint F (singletonPoint (K:=L) i) := by
  fin_cases i
  · exact ⟨expr_one,expr_zero,expr_zero,presented_onePhase,presented_onePhase⟩
  · exact ⟨expr_zero,expr_one,expr_zero,presented_onePhase,presented_onePhase⟩
  · exact ⟨expr_zero,expr_zero,expr_one,presented_onePhase,presented_onePhase⟩

/-- A supplied exact magnitude is presented from its defining quadratic;
its finite-expression representability is not a premise of the selected-candidate theorem. -/
theorem exact_magnitude_presented (w : WeightedData F) (i : Fin 3) (ρ : L)
    (hρ : ρ^2 = ComplexPair.normSq (pairInput (mapWeighted (algebraMap F L) w) i).d) :
    Presented F ρ := by
  have hp := presented_mapped_pairInput (F:=F) (L:=L) w i
  exact ((hp.2.2.2.1.1.pow 2).add (hp.2.2.2.1.2.pow 2)).squareRoot hρ

/-- Every point in the actual finite spectrum has presented radii and phase
coordinates over the coefficient presentation F. -/
theorem spectrumCandidates_presented (w : WeightedData F)
    (hS : phaseSextic (weightedP w) (weightedQ w) ≠ 0)
    (ρ : Fin 3 → L) (hρ : ∀ i, (ρ i)^2 = ComplexPair.normSq (pairInput (mapWeighted (algebraMap F L) w) i).d)
    (x : SpectrumPoint L) (hm : x ∈ spectrumCandidates (mapWeighted (algebraMap F L) w) ρ) :
    PresentedPoint F x := by
  classical
  simp only [spectrumCandidates,Finset.mem_union] at hm
  rcases hm with (hs | hp) | hf
  · unfold singletonCandidates at hs
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hs
    exact singletonPoint_presented i
  · unfold pairCandidates at hp
    obtain ⟨⟨i,s⟩,_,rfl⟩ := Finset.mem_image.mp hp
    exact pairPoint_presented w ρ i s (exact_magnitude_presented w i (ρ i) (hρ i))
  · unfold fullCandidates at hf
    obtain ⟨⟨t,u⟩,hfilter,rfl⟩ := Finset.mem_image.mp hf
    exact selected_fullPoint_presented w t u hS (Finset.mem_filter.mp hfilter).1

/-- The actual weighted quotient values are presented as well. -/
theorem spectrumValue_presented (w : WeightedData F) (x : SpectrumPoint L)
    (hx : PresentedPoint F x) :
    Presented F (spectrumValue (mapWeighted (algebraMap F L) w) x) := by
  obtain ⟨hr₁,hr₂,hr₃,hq,hv⟩ := hx
  have hd₁₂ : PresentedPair F (toSpectrum (mapWeighted (algebraMap F L) w)).d₁₂ :=
    ⟨expr_algebraMap _,expr_algebraMap _⟩
  have hd₁₃ : PresentedPair F (toSpectrum (mapWeighted (algebraMap F L) w)).d₁₃ :=
    ⟨expr_algebraMap _,expr_algebraMap _⟩
  have hd₂₃ : PresentedPair F (toSpectrum (mapWeighted (algebraMap F L) w)).d₂₃ :=
    ⟨expr_algebraMap _,expr_algebraMap _⟩
  have he₁₂ := (presentedPair_mul hd₁₂ hq).1
  have he₁₃ := (presentedPair_mul hd₁₃ hv).1
  have he₂₃ := (presentedPair_mul hd₂₃ (presentedPair_mul hv (presentedPair_conj hq))).1
  have hB₁ : Presented F (twiceB₁ (toSpectrum (mapWeighted (algebraMap F L) w)) x.q x.v x.r₁ x.r₂ x.r₃) :=
    (((expr_algebraMap _).mul hr₁).add
      (((expr_algebraMap _).add he₁₂).mul hr₂)).add
      (((expr_algebraMap _).add he₁₃).mul hr₃)
  have hB₂ : Presented F (twiceB₂ (toSpectrum (mapWeighted (algebraMap F L) w)) x.q x.v x.r₁ x.r₂ x.r₃) :=
    ((((expr_algebraMap _).add he₁₂).mul hr₁).add
      ((expr_algebraMap _).mul hr₂)).add
      (((expr_algebraMap _).add he₂₃).mul hr₃)
  have hB₃ : Presented F (twiceB₃ (toSpectrum (mapWeighted (algebraMap F L) w)) x.q x.v x.r₁ x.r₂ x.r₃) :=
    ((((expr_algebraMap _).add he₁₃).mul hr₁).add
      (((expr_algebraMap _).add he₂₃).mul hr₂)).add
      ((expr_algebraMap _).mul hr₃)
  have hG : Presented F ((mapWeighted (algebraMap F L) w).g1*x.r₁+
      (mapWeighted (algebraMap F L) w).g2*x.r₂+(mapWeighted (algebraMap F L) w).g3*x.r₃) :=
    (((expr_algebraMap _).mul hr₁).add ((expr_algebraMap _).mul hr₂)).add
      ((expr_algebraMap _).mul hr₃)
  exact presented_div (((hr₁.mul hB₁).add (hr₂.mul hB₂)).add (hr₃.mul hB₃))
    ((expr_natCast 2).mul (hG.pow 2))

end Presented

section Presented
variable {F L : Type*} [Field F] [Field L] [Algebra F L] [LinearOrder L] [IsStrictOrderedRing L]

/-- A complex pair is presented coordinatewise if its norm and the real part
of its square are presented. This is a pair of explicit quadratic equations. -/
theorem presentedPair_of_norm_square (z : ComplexPair L)
    (hn : Presented F (normSq z)) (hs : Presented F (mul z z).re) : PresentedPair F z := by
  have h2 : Presented F (2 : L) := expr_natCast 2
  have hr : z.re ^ 2 = (normSq z + (mul z z).re) / 2 := by
    simp only [normSq,mul]
    ring
  have hi : z.im ^ 2 = (normSq z - (mul z z).re) / 2 := by
    simp only [normSq,mul]
    ring
  exact ⟨(presented_div (hn.add hs) h2).squareRoot hr,
    (presented_div (hn.sub hs) h2).squareRoot hi⟩

/-- The squared-amplitude witnesses constructed in Section 2 and Section 8
are presented over F, including the phase −1 branch and zero radius. -/
theorem realized_amplitude_presented (r : L) (q z : ComplexPair L)
    (hr : Presented F r) (hq : PresentedPair F q)
    (hn : normSq z = r) (hs : conj (mul z z) = scale r q) : PresentedPair F z := by
  apply presentedPair_of_norm_square z
  · rwa [hn]
  · have he := congrArg ComplexPair.re hs
    change (mul z z).re = r*q.re at he
    rw [he]
    exact hr.mul hq.1

/-- Every representative of a matched rank-one projector has presented entries,
even if its irrelevant common amplitude phase is transcendental over F. -/
theorem matched_projector_presented (x : SpectrumPoint L) (hx : PresentedPoint F x)
    (z₁ z₂ z₃ : ComplexPair L) (hm : PointMatches x z₁ z₂ z₃) :
    Presented F (normSq z₁) ∧ Presented F (normSq z₂) ∧ Presented F (normSq z₃) ∧
    PresentedPair F (mul z₁ (conj z₂)) ∧ PresentedPair F (mul z₁ (conj z₃)) ∧
    PresentedPair F (mul z₂ (conj z₃)) := by
  obtain ⟨hr₁,hr₂,hr₃,hq,hv⟩ := hx
  obtain ⟨hn₁,hn₂,hn₃,hs₁₂,hs₁₃,hs₂₃⟩ := hm
  have hz₁ : Presented F (normSq z₁) := hn₁ ▸ hr₁
  have hz₂ : Presented F (normSq z₂) := hn₂ ▸ hr₂
  have hz₃ : Presented F (normSq z₃) := hn₃ ▸ hr₃
  have finish (z w : ComplexPair L) (r s : L) (v : ComplexPair L)
      (hnz : Presented F (normSq z)) (hnw : Presented F (normSq w))
      (hr : Presented F r) (hs : Presented F s) (hv : PresentedPair F v)
      (hmatch : squaredEntry z w = scale (r*s) v) :
      PresentedPair F (mul z (conj w)) := by
    apply presentedPair_of_norm_square
    · rw [complex_norm_mul,complexPair_norm_conj]
      exact hnz.mul hnw
    · change Presented F (squaredEntry z w).re
      rw [hmatch]
      exact (hr.mul hs).mul hv.1
  exact ⟨hz₁,hz₂,hz₃,finish _ _ _ _ _ hz₁ hz₂ hr₁ hr₂ hq hs₁₂,
    finish _ _ _ _ _ hz₁ hz₃ hr₁ hr₃ hv hs₁₃,
    finish _ _ _ _ _ hz₂ hz₃ hr₂ hr₃ (presentedPair_mul hv (presentedPair_conj hq)) hs₂₃⟩

/-- Actual selected candidates imply finite-expression representability of the physical projector;
there is no assumed annihilator at this endpoint. -/
theorem selected_projector_presented (w : WeightedData F)
    (hS : phaseSextic (weightedP w) (weightedQ w) ≠ 0)
    (ρ : Fin 3 → L) (hρ : ∀ i, (ρ i)^2 = normSq (pairInput (mapWeighted (algebraMap F L) w) i).d)
    (x : SpectrumPoint L) (hm : x ∈ spectrumCandidates (mapWeighted (algebraMap F L) w) ρ)
    (z₁ z₂ z₃ : ComplexPair L) (hmatch : PointMatches x z₁ z₂ z₃) :
    Presented F (normSq z₁) ∧ Presented F (normSq z₂) ∧ Presented F (normSq z₃) ∧
    PresentedPair F (mul z₁ (conj z₂)) ∧ PresentedPair F (mul z₁ (conj z₃)) ∧
    PresentedPair F (mul z₂ (conj z₃)) :=
  matched_projector_presented x (spectrumCandidates_presented w hS ρ hρ x hm) z₁ z₂ z₃ hmatch

variable [IsRealClosed L]

theorem phase_radius_presented_realization (r : L) (q : ComplexPair L)
    (hr : 0 ≤ r) (hq : normSq q = 1) (har : Presented F r) (haq : PresentedPair F q) :
    ∃ z : ComplexPair L, PresentedPair F z ∧ normSq z = r ∧ conj (mul z z) = scale r q := by
  obtain ⟨z,hn,hs⟩ := phase_radius_realization r q hr hq
  exact ⟨z,realized_amplitude_presented r q z har haq hn hs,hn,hs⟩

#print axioms selected_projector_presented
#print axioms phase_radius_presented_realization
end Presented

section Presented
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
theorem selected_value_presented (w : WeightedData F)
    (he : weightedExceptional (mapWeighted (algebraMap F L) w) ≠ 0)
    (ρ : Fin 3 → L) (hρ : ∀ i, (ρ i)^2 = ComplexPair.normSq (pairInput (mapWeighted (algebraMap F L) w) i).d)
    (ν : L) (hm : ν ∈ spectrumValues (mapWeighted (algebraMap F L) w) ρ) : Presented F ν := by
  classical
  unfold spectrumValues at hm
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hm
  exact spectrumValue_presented w x
    (spectrumCandidates_presented w (base_sextic_ne_zero_of_mapped_generic w he) ρ hρ x hx)

/-- All physical projector coordinates from the actual selected spectrum are
presented over its coefficient field, with genericity supplying nonzero sextic. -/
theorem selected_matched_projector_presented (w : WeightedData F)
    (he : weightedExceptional (mapWeighted (algebraMap F L) w) ≠ 0)
    (ρ : Fin 3 → L) (hρ : ∀ i, (ρ i)^2 = ComplexPair.normSq (pairInput (mapWeighted (algebraMap F L) w) i).d)
    (x : SpectrumPoint L) (hm : x ∈ spectrumCandidates (mapWeighted (algebraMap F L) w) ρ)
    (z₁ z₂ z₃ : ComplexPair L) (hmatch : PointMatches x z₁ z₂ z₃) :
    Presented F (ComplexPair.normSq z₁) ∧ Presented F (ComplexPair.normSq z₂) ∧
    Presented F (ComplexPair.normSq z₃) ∧
    PresentedPair F (ComplexPair.mul z₁ (ComplexPair.conj z₂)) ∧
    PresentedPair F (ComplexPair.mul z₁ (ComplexPair.conj z₃)) ∧
    PresentedPair F (ComplexPair.mul z₂ (ComplexPair.conj z₃)) :=
  selected_projector_presented w (base_sextic_ne_zero_of_mapped_generic w he) ρ hρ x hm z₁ z₂ z₃ hmatch

variable [IsRealClosed L]

/-- Canonical magnitude root selection and duplicate-value removal preserve
finite-expression representability of every selected common-spectrum value. -/
theorem exactCommonSpectrum_presented (w : WeightedData F)
    (he : weightedExceptional (mapWeighted (algebraMap F L) w) ≠ 0)
    (ν : L) (hm : ν ∈ exactCommonSpectrum (mapWeighted (algebraMap F L) w)) : Presented F ν :=
  selected_value_presented w he _ (fun i => (canonicalMagnitudes_spec _ i).2) ν hm

#print axioms exactCommonSpectrum_presented
#print axioms selected_matched_projector_presented
end Presented

end W3.Weighted.Expression
