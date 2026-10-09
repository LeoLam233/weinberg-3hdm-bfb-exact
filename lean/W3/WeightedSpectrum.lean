import W3.WeightedSupports
import W3.EliminationStationary

/-! Concrete common-spectrum candidate set: three vertices, six pair branches,
and at most six selected sextic roots, with exact physical support filters. -/
noncomputable section
namespace W3.Weighted
open W3.Elimination

structure SpectrumPoint (K : Type*) where
  r₁ : K
  r₂ : K
  r₃ : K
  q : ComplexPair K
  v : ComplexPair K

structure PairInput (K : Type*) where
  a : K
  b : K
  e : K
  d : ComplexPair K
  g₁ : K
  g₂ : K

section Ordered
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def onePhase : ComplexPair K := ⟨1, 0⟩

def spectrumWeight (w : WeightedData K) (x : SpectrumPoint K) : K := w.g1 * x.r₁ + w.g2 * x.r₂ + w.g3 * x.r₃

def spectrumValue (w : WeightedData K) (x : SpectrumPoint K) : K :=
  weightedQuotient (toSpectrum w) x.q x.v w.g1 w.g2 w.g3 x.r₁ x.r₂ x.r₃

def singletonPoint (i : Fin 3) : SpectrumPoint K :=
  ![⟨1, 0, 0, onePhase, onePhase⟩, ⟨0, 1, 0, onePhase, onePhase⟩,
    ⟨0, 0, 1, onePhase, onePhase⟩] i

def singletonCandidates (w : WeightedData K) : Finset (SpectrumPoint K) := by
  classical
  exact ((Finset.univ : Finset (Fin 3)).filter (fun i => spectrumWeight w (singletonPoint i) ≠ 0)).image singletonPoint

def pairInput (w : WeightedData K) (i : Fin 3) : PairInput K :=
  ![⟨w.alpha1, w.alpha2, w.e12, ⟨w.d12r, w.d12i⟩, w.g1, w.g2⟩,
    ⟨w.alpha1, w.alpha3, w.e13, ⟨w.d13r, w.d13i⟩, w.g1, w.g3⟩,
    ⟨w.alpha2, w.alpha3, w.e23, ⟨w.d23r, w.d23i⟩, w.g2, w.g3⟩] i

def branchSign (s : Bool) : K := if s then 1 else -1

def pairPhase (d : ComplexPair K) (ρ : K) (s : Bool) : ComplexPair K :=
  ⟨branchSign s * d.re / ρ, -(branchSign s * d.im) / ρ⟩

def pairH (p : PairInput K) (ρ : K) (s : Bool) : K := (p.e + branchSign s * ρ) / 2

def pairSum (p : PairInput K) (ρ : K) (s : Bool) : K :=
  pairN₁ (p.a / 2) (p.b / 2) (pairH p ρ s) p.g₁ p.g₂ +
  pairN₂ (p.a / 2) (p.b / 2) (pairH p ρ s) p.g₁ p.g₂

def pairLeft (p : PairInput K) (ρ : K) (s : Bool) : K :=
  pairN₁ (p.a / 2) (p.b / 2) (pairH p ρ s) p.g₁ p.g₂ / pairSum p ρ s

def pairRight (p : PairInput K) (ρ : K) (s : Bool) : K :=
  pairN₂ (p.a / 2) (p.b / 2) (pairH p ρ s) p.g₁ p.g₂ / pairSum p ρ s

/-- Pair support reconstruction, including the 23 face where q₂=1 is a gauge choice. -/
def pairPoint (w : WeightedData K) (ρ : Fin 3 → K) (i : Fin 3) (s : Bool) : SpectrumPoint K :=
  let p := pairInput w i
  let l := pairLeft p (ρ i) s
  let r := pairRight p (ρ i) s
  let q := pairPhase p.d (ρ i) s
  ![⟨l, r, 0, q, onePhase⟩, ⟨l, 0, r, onePhase, q⟩,
    ⟨0, l, r, onePhase, q⟩] i

def PairRetained (w : WeightedData K) (ρ : Fin 3 → K) (i : Fin 3) (s : Bool) : Prop :=
  let p := pairInput w i
  ρ i ≠ 0 ∧ pairW (p.a / 2) (p.b / 2) (pairH p (ρ i) s) p.g₁ p.g₂ ≠ 0 ∧
    pairSum p (ρ i) s ≠ 0 ∧ 0 < pairLeft p (ρ i) s ∧ 0 < pairRight p (ρ i) s ∧
    spectrumWeight w (pairPoint w ρ i s) ≠ 0

def pairCandidates (w : WeightedData K) (ρ : Fin 3 → K) : Finset (SpectrumPoint K) := by
  classical
  exact ((Finset.univ : Finset (Fin 3 × Bool)).filter (fun e => PairRetained w ρ e.1 e.2)).image
    (fun e => pairPoint w ρ e.1 e.2)

/-- Direct Eq. (11) reconstruction from the actual selected sextic root pair. -/
def fullPoint (w : WeightedData K) (t u : K) : SpectrumPoint K :=
  let q := circlePoint 1 t
  let v := circlePoint 1 u
  let k := toSpectrum w
  let D := currentDen k q v
  ⟨(edge₂₃ k q v).im / D, -(edge₁₃ k v).im / D, (edge₁₂ k q).im / D, q, v⟩

def FullRetained (w : WeightedData K) (t u : K) : Prop :=
  let x := fullPoint w t u
  currentDen (toSpectrum w) x.q x.v ≠ 0 ∧
    0 < x.r₁ ∧ 0 < x.r₂ ∧ 0 < x.r₃ ∧ spectrumWeight w x ≠ 0

def fullCandidates (w : WeightedData K) : Finset (SpectrumPoint K) := by
  classical
  exact ((phaseCandidates (weightedP w) (weightedQ w)).filter
    (fun e => FullRetained w e.1 e.2)).image (fun e => fullPoint w e.1 e.2)

/-- The complete common spectrum, before duplicate values are removed. -/
def spectrumCandidates (w : WeightedData K) (ρ : Fin 3 → K) : Finset (SpectrumPoint K) := by
  classical
  exact singletonCandidates w ∪ pairCandidates w ρ ∪ fullCandidates w

def spectrumValues (w : WeightedData K) (ρ : Fin 3 → K) : Finset K := by
  classical
  exact (spectrumCandidates w ρ).image (spectrumValue w)

theorem singletonCandidates_card (w : WeightedData K) : (singletonCandidates w).card ≤ 3 := by
  classical
  apply Finset.card_image_le.trans
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem pairCandidates_card (w : WeightedData K) (ρ : Fin 3 → K) : (pairCandidates w ρ).card ≤ 6 := by
  classical
  apply Finset.card_image_le.trans
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem fullCandidates_card (w : WeightedData K) : (fullCandidates w).card ≤ 6 := by
  classical
  exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans
    (phaseCandidates_card_le_six _ _))

/-- The exact 3+6+6 bound, with no assumption about numerical root counts. -/
theorem spectrumCandidates_card_le_fifteen (w : WeightedData K) (ρ : Fin 3 → K) :
    (spectrumCandidates w ρ).card ≤ 15 := by
  classical
  unfold spectrumCandidates
  have h₁ := singletonCandidates_card w
  have h₂ := pairCandidates_card w ρ
  have h₃ := fullCandidates_card w
  have h₁₂ := Finset.card_union_le (singletonCandidates w) (pairCandidates w ρ)
  have hall := Finset.card_union_le (singletonCandidates w ∪ pairCandidates w ρ) (fullCandidates w)
  omega

theorem spectrumValues_card_le_fifteen (w : WeightedData K) (ρ : Fin 3 → K) :
    (spectrumValues w ρ).card ≤ 15 :=
  Finset.card_image_le.trans (spectrumCandidates_card_le_fifteen w ρ)

theorem spectrumCandidates_nonempty (w : WeightedData K) (ρ : Fin 3 → K) (hg₁ : w.g1 ≠ 0) :
    (spectrumCandidates w ρ).Nonempty := by
  classical
  have hs : singletonPoint (K := K) 0 ∈ singletonCandidates w := by
    apply Finset.mem_image.mpr
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    simpa [spectrumWeight, singletonPoint] using hg₁
  exact ⟨_, Finset.mem_union_left _ (Finset.mem_union_left _ hs)⟩

theorem spectrumValues_nonempty (w : WeightedData K) (ρ : Fin 3 → K) (hg₁ : w.g1 ≠ 0) :
    (spectrumValues w ρ).Nonempty :=
  (spectrumCandidates_nonempty w ρ hg₁).image _

/-- Full-support retained roots are genuine normalized stationary points. -/
theorem fullPoint_stationary (w : WeightedData K) (he : weightedExceptional w ≠ 0)
    (hg₁ : w.g1 ≠ 0) (t u : K) (hm : (t,u) ∈ phaseCandidates (weightedP w) (weightedQ w))
    (hr : FullRetained w t u) :
    let x := fullPoint w t u
    x.r₁ + x.r₂ + x.r₃ = 1 ∧
    FullStationaryEquations (toSpectrum w) x.q x.v w.g1 w.g2 w.g3 x.r₁ x.r₂ x.r₃ := by
  let q := circlePoint (1 : K) t
  let v := circlePoint (1 : K) u
  have ht : (1 : K)^2 + t^2 ≠ 0 := circle_den_ne_zero 1 t (Or.inl one_ne_zero)
  have hu : (1 : K)^2 + u^2 ≠ 0 := circle_den_ne_zero 1 u (Or.inl one_ne_zero)
  have hq : ComplexPair.normSq q = 1 := circlePoint_norm 1 t ht
  have hv : ComplexPair.normSq v = 1 := circlePoint_norm 1 u hu
  have hred : ReducedRadialEquations (toSpectrum w) q v w.g1 w.g2 w.g3 := by
    apply (weighted_reduced_iff_candidates w he q v hq hv).mpr
    exact ⟨t, u, hm, rfl, rfl⟩
  rcases hr with ⟨hD, hp₁, hp₂, hp₃, hG⟩
  change currentDen (toSpectrum w) q v ≠ 0 at hD
  change w.g1 * _ + w.g2 * _ + w.g3 * _ ≠ 0 at hG
  constructor
  · change (edge₂₃ (toSpectrum w) q v).im / currentDen (toSpectrum w) q v +
      -(edge₁₃ (toSpectrum w) v).im / currentDen (toSpectrum w) q v +
      (edge₁₂ (toSpectrum w) q).im / currentDen (toSpectrum w) q v = 1
    rw [← add_div, ← add_div]
    apply (div_eq_one_iff_eq hD).mpr
    unfold currentDen
    ring
  · exact ⟨reconstructed_current_equations _ _ _,
      (reconstructed_radial_iff _ q v w.g1 w.g2 w.g3 _ hq hv hg₁ hD hG).mpr hred⟩


@[ext] theorem spectrumPoint_ext {x y : SpectrumPoint K}
    (h₁ : x.r₁ = y.r₁) (h₂ : x.r₂ = y.r₂) (h₃ : x.r₃ = y.r₃)
    (hq : x.q = y.q) (hv : x.v = y.v) : x = y := by
  cases x; cases y; cases h₁; cases h₂; cases h₃; cases hq; cases hv; rfl

/-- Every full-support stationary point occurs in the finite filtered list,
including its exact amplitudes and algebraic phases. -/
theorem full_stationary_mem_candidates (w : WeightedData K) (he : weightedExceptional w ≠ 0)
    (hg₁ : w.g1 ≠ 0) (x : SpectrumPoint K)
    (hq : ComplexPair.normSq x.q = 1) (hv : ComplexPair.normSq x.v = 1)
    (hloop : (ComplexPair.mul (ComplexPair.mul (toSpectrum w).d₁₂ (toSpectrum w).d₂₃)
      (ComplexPair.conj (toSpectrum w).d₁₃)).im ≠ 0)
    (hp₁ : 0 < x.r₁) (hp₂ : 0 < x.r₂) (hp₃ : 0 < x.r₃)
    (hsum : x.r₁ + x.r₂ + x.r₃ = 1) (hG : spectrumWeight w x ≠ 0)
    (hstat : FullStationaryEquations (toSpectrum w) x.q x.v w.g1 w.g2 w.g3 x.r₁ x.r₂ x.r₃) :
    x ∈ fullCandidates w := by
  classical
  obtain ⟨hD, h₁, h₂, h₃, t, u, hm, hq', hv'⟩ :=
    (full_stationary_iff_sextic w he x.q x.v x.r₁ x.r₂ x.r₃ hq hv hloop
      (ne_of_gt hp₁) (ne_of_gt hp₂) (ne_of_gt hp₃) hsum hg₁ hG).mp hstat
  have hx : fullPoint w t u = x := by
    apply spectrumPoint_ext
    · simpa [fullPoint, hq', hv'] using h₁.symm
    · simpa [fullPoint, hq', hv'] using h₂.symm
    · simpa [fullPoint, hq', hv'] using h₃.symm
    · exact hq'
    · exact hv'
  apply Finset.mem_image.mpr
  refine ⟨(t,u), Finset.mem_filter.mpr ⟨hm, ?_⟩, hx⟩
  change FullRetained w t u
  unfold FullRetained
  rw [hx]
  exact ⟨hD, hp₁, hp₂, hp₃, hG⟩

def amplitudePoint (z₁ z₂ z₃ : ComplexPair K) : SpectrumPoint K :=
  ⟨ComplexPair.normSq z₁, ComplexPair.normSq z₂, ComplexPair.normSq z₃,
    relativePhase z₁ z₂, relativePhase z₁ z₃⟩

/-- Direct full-support matrix/amplitude coverage: genericity proves the
weighted pole is absent before the quotient is ever divided by its weight. -/
theorem full_amplitude_mem_candidates (w : WeightedData K) (he : weightedExceptional w ≠ 0)
    (hg₁ : w.g1 ≠ 0) (z₁ z₂ z₃ : ComplexPair K) (lam : K)
    (hloop : (ComplexPair.mul (ComplexPair.mul (toSpectrum w).d₁₂ (toSpectrum w).d₂₃)
      (ComplexPair.conj (toSpectrum w).d₁₃)).im ≠ 0)
    (hp₁ : 0 < ComplexPair.normSq z₁) (hp₂ : 0 < ComplexPair.normSq z₂) (hp₃ : 0 < ComplexPair.normSq z₃)
    (hsum : ComplexPair.normSq z₁ + ComplexPair.normSq z₂ + ComplexPair.normSq z₃ = 1)
    (hamp : AmplitudeEquations (toSpectrum w) z₁ z₂ z₃ w.g1 w.g2 w.g3 lam) :
    amplitudePoint z₁ z₂ z₃ ∈ fullCandidates w := by
  have h₁ := ne_of_gt hp₁
  have h₂ := ne_of_gt hp₂
  have h₃ := ne_of_gt hp₃
  have hq := relativePhase_norm z₁ z₂ h₁ h₂
  have hv := relativePhase_norm z₁ z₃ h₁ h₃
  obtain ⟨hc, hr₁, hr₂, hr₃⟩ :=
    (amplitude_equations_iff (toSpectrum w) z₁ z₂ z₃ w.g1 w.g2 w.g3 lam h₁ h₂ h₃).mp hamp
  have hx₂ : w.g1 * twiceB₂ (toSpectrum w) (relativePhase z₁ z₂) (relativePhase z₁ z₃)
      (ComplexPair.normSq z₁) (ComplexPair.normSq z₂) (ComplexPair.normSq z₃) -
      w.g2 * twiceB₁ (toSpectrum w) (relativePhase z₁ z₂) (relativePhase z₁ z₃)
      (ComplexPair.normSq z₁) (ComplexPair.normSq z₂) (ComplexPair.normSq z₃) = 0 := by
    rw [hr₁, hr₂]; ring
  have hx₃ : w.g1 * twiceB₃ (toSpectrum w) (relativePhase z₁ z₂) (relativePhase z₁ z₃)
      (ComplexPair.normSq z₁) (ComplexPair.normSq z₂) (ComplexPair.normSq z₃) -
      w.g3 * twiceB₁ (toSpectrum w) (relativePhase z₁ z₂) (relativePhase z₁ z₃)
      (ComplexPair.normSq z₁) (ComplexPair.normSq z₂) (ComplexPair.normSq z₃) = 0 := by
    rw [hr₁, hr₃]; ring
  have hG := full_support_cross_excludes_pole w he _ _ _ _ _ hq hv hloop
    h₁ h₂ h₃ hsum hc hx₂ hx₃
  exact full_stationary_mem_candidates w he hg₁ (amplitudePoint z₁ z₂ z₃) hq hv hloop
    hp₁ hp₂ hp₃ hsum hG
    (amplitude_implies_full_stationary (toSpectrum w) z₁ z₂ z₃ w.g1 w.g2 w.g3 lam
      h₁ h₂ h₃ hg₁ hG hamp)

/-- Every retained full-support candidate has unit phases, normalized positive
radii, nonzero weight, and the actual full stationary equations. -/
theorem fullCandidates_sound (w : WeightedData K) (he : weightedExceptional w ≠ 0)
    (hg₁ : w.g1 ≠ 0) (x : SpectrumPoint K) (hm : x ∈ fullCandidates w) :
    ComplexPair.normSq x.q = 1 ∧ ComplexPair.normSq x.v = 1 ∧
    0 < x.r₁ ∧ 0 < x.r₂ ∧ 0 < x.r₃ ∧ x.r₁ + x.r₂ + x.r₃ = 1 ∧
    spectrumWeight w x ≠ 0 ∧
    FullStationaryEquations (toSpectrum w) x.q x.v w.g1 w.g2 w.g3 x.r₁ x.r₂ x.r₃ := by
  classical
  unfold fullCandidates at hm
  obtain ⟨⟨t,u⟩, hfilter, rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨hroot, hret⟩ := Finset.mem_filter.mp hfilter
  obtain ⟨hsum, hstat⟩ := fullPoint_stationary w he hg₁ t u hroot hret
  exact ⟨circlePoint_norm 1 t (circle_den_ne_zero 1 t (Or.inl one_ne_zero)),
    circlePoint_norm 1 u (circle_den_ne_zero 1 u (Or.inl one_ne_zero)),
    hret.2.1, hret.2.2.1, hret.2.2.2.1, hsum, hret.2.2.2.2, hstat⟩

end Ordered
end W3.Weighted
