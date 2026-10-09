import W3.EliminationDual
import W3.WeightedStationarity

noncomputable section
namespace W3.Elimination
open W3.Weighted
open Polynomial

section StationaryField
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem rowImag_scale (r : K) (p : PhaseRow K) (q v : ComplexPair K) :
    rowImag (scaleRow r p) q v = r * rowImag p q v := by
  unfold rowImag scaleRow
  ring

theorem circlePoint_normalize (x y : K) (hx : x ≠ 0) :
    circlePoint x y = circlePoint 1 (y / x) := by
  have hden := circle_den_ne_zero x y (Or.inl hx)
  have hden' := circle_den_ne_zero (1 : K) (y/x) (Or.inl one_ne_zero)
  apply congrArg₂ ComplexPair.mk <;> field_simp <;> ring

/-- Every actual unit-circle solution is in the sextic list, and every list entry is a solution. -/
theorem circle_phase_candidates (p s h : PhaseRow K) (he : phaseExceptional p s h ≠ 0)
    (q v : ComplexPair K) (hq : ComplexPair.normSq q = 1) (hv : ComplexPair.normSq v = 1) :
    (rowImag p q v = 0 ∧ rowImag s q v = 0) ↔
    ∃ t u : K, (t,u) ∈ phaseCandidates p s ∧ circlePoint 1 t = q ∧ circlePoint 1 u = v := by
  constructor
  · intro hr
    obtain ⟨x, y, z, w, ht, hu, hq', hv', heq⟩ := circle_phase_projective p s q v hq hv
    obtain ⟨hx, hz, hm⟩ := (generic_projective_candidates_exact p s h he x y z w ht hu).mp (heq.mp hr)
    exact ⟨y/x, w/z, hm, (circlePoint_normalize x y hx).symm.trans hq',
      (circlePoint_normalize z w hz).symm.trans hv'⟩
  · rintro ⟨t, u, hm, rfl, rfl⟩
    obtain ⟨hF, hG⟩ := (generic_phase_candidates_exact p s h he t u).1.mp hm
    have ht : 1+t^2 ≠ 0 := by simpa [circlePoly] using circle_eval_ne_zero t
    have hu : 1+u^2 ≠ 0 := by simpa [circlePoly] using circle_eval_ne_zero u
    rw [rowImag_halfAngle p t u ht hu, rowImag_halfAngle s t u ht hu, hF, hG]
    simp

/-- The extra pole equation has no actual unit-circle solution on the full-support phase spectrum. -/
theorem circle_phase_exclusion (p s h : PhaseRow K) (he : phaseExceptional p s h ≠ 0)
    (q v : ComplexPair K) (hq : ComplexPair.normSq q = 1) (hv : ComplexPair.normSq v = 1)
    (hp : rowImag p q v = 0) (hs : rowImag s q v = 0) : rowImag h q v ≠ 0 := by
  obtain ⟨t, u, hm, rfl, rfl⟩ := (circle_phase_candidates p s h he q v hq hv).mp ⟨hp, hs⟩
  have hh := (generic_phase_candidates_exact p s h he t u).2 hm
  have ht : 1+t^2 ≠ 0 := by simpa [circlePoly] using circle_eval_ne_zero t
  have hu : 1+u^2 ≠ 0 := by simpa [circlePoly] using circle_eval_ne_zero u
  rw [rowImag_halfAngle h t u ht hu]
  exact div_ne_zero hh (mul_ne_zero ht hu)

theorem weighted_reduced_iff_candidates (w : WeightedData K) (he : weightedExceptional w ≠ 0)
    (q v : ComplexPair K) (hq : ComplexPair.normSq q = 1) (hv : ComplexPair.normSq v = 1) :
    ReducedRadialEquations (toSpectrum w) q v w.g1 w.g2 w.g3 ↔
    ∃ t u : K, (t,u) ∈ phaseCandidates (weightedP w) (weightedQ w) ∧
      circlePoint 1 t = q ∧ circlePoint 1 u = v := by
  have h := circle_phase_candidates (weightedP w) (weightedQ w) (weightedPole w) he q v hq hv
  rw [weightedP, weightedQ, rowImag_scale, rowImag_scale] at h
  simpa only [weightedP, weightedQ, ReducedRadialEquations, ← weightedF_eq, ← weightedG_eq,
    mul_eq_zero, OfNat.ofNat_ne_zero, false_or] using h

theorem weighted_pole_row (w : WeightedData K) (q v : ComplexPair K) :
    rowImag (weightedH w) q v =
      w.g1 * (edge₂₃ (toSpectrum w) q v).im -
      w.g2 * (edge₁₃ (toSpectrum w) v).im +
      w.g3 * (edge₁₂ (toSpectrum w) q).im := by
  simp only [rowImag, weightedH, edge₂₃, edge₁₃, edge₁₂, toSpectrum,
    ComplexPair.mul, ComplexPair.conj]
  ring

/-- Concrete full-support exclusion: the weighted current cannot lie on the pole hyperplane. -/
theorem weighted_current_pole_ne_zero (w : WeightedData K) (he : weightedExceptional w ≠ 0)
    (q v : ComplexPair K) (hq : ComplexPair.normSq q = 1) (hv : ComplexPair.normSq v = 1)
    (hr : ReducedRadialEquations (toSpectrum w) q v w.g1 w.g2 w.g3) :
    w.g1 * (edge₂₃ (toSpectrum w) q v).im -
      w.g2 * (edge₁₃ (toSpectrum w) v).im +
      w.g3 * (edge₁₂ (toSpectrum w) q).im ≠ 0 := by
  have hp : rowImag (weightedP w) q v = 0 := by
    rw [weightedP, rowImag_scale, weightedF_eq]
    exact mul_eq_zero_of_right _ hr.1
  have hs : rowImag (weightedQ w) q v = 0 := by
    rw [weightedQ, rowImag_scale, weightedG_eq]
    exact mul_eq_zero_of_right _ hr.2
  have hh := circle_phase_exclusion (weightedP w) (weightedQ w) (weightedPole w) he q v hq hv hp hs
  rw [weightedPole, rowImag_scale, weighted_pole_row] at hh
  exact (mul_ne_zero_iff.mp hh).2

/-- Once the amplitudes are reconstructed, generic phase equations prove the
weighted normalization denominator nonzero; this is not assumed. -/
theorem weighted_reconstructed_weight_ne_zero (w : WeightedData K) (he : weightedExceptional w ≠ 0)
    (q v : ComplexPair K) (hq : ComplexPair.normSq q = 1) (hv : ComplexPair.normSq v = 1)
    (hr : ReducedRadialEquations (toSpectrum w) q v w.g1 w.g2 w.g3)
    (D : K) (hD : D ≠ 0) :
    w.g1*((edge₂₃ (toSpectrum w) q v).im/D) +
      w.g2*(-(edge₁₃ (toSpectrum w) v).im/D) +
      w.g3*((edge₁₂ (toSpectrum w) q).im/D) ≠ 0 := by
  have hh := weighted_current_pole_ne_zero w he q v hq hv hr
  have hid : w.g1*((edge₂₃ (toSpectrum w) q v).im/D) +
      w.g2*(-(edge₁₃ (toSpectrum w) v).im/D) +
      w.g3*((edge₁₂ (toSpectrum w) q).im/D) =
      (w.g1*(edge₂₃ (toSpectrum w) q v).im -
        w.g2*(edge₁₃ (toSpectrum w) v).im + w.g3*(edge₁₂ (toSpectrum w) q).im)/D := by
    ring
  rw [hid]
  exact div_ne_zero hh hD

/-- Radial cross equations make sense even on the weighted pole hyperplane. -/
theorem reconstructed_cross_implies_reduced (w : WeightedData K) (q v : ComplexPair K)
    (hq : ComplexPair.normSq q = 1) (hv : ComplexPair.normSq v = 1)
    (D : K) (hD : D ≠ 0)
    (h₂ : w.g1 * twiceB₂ (toSpectrum w) q v
        ((edge₂₃ (toSpectrum w) q v).im/D) (-(edge₁₃ (toSpectrum w) v).im/D) ((edge₁₂ (toSpectrum w) q).im/D) -
      w.g2 * twiceB₁ (toSpectrum w) q v
        ((edge₂₃ (toSpectrum w) q v).im/D) (-(edge₁₃ (toSpectrum w) v).im/D) ((edge₁₂ (toSpectrum w) q).im/D) = 0)
    (h₃ : w.g1 * twiceB₃ (toSpectrum w) q v
        ((edge₂₃ (toSpectrum w) q v).im/D) (-(edge₁₃ (toSpectrum w) v).im/D) ((edge₁₂ (toSpectrum w) q).im/D) -
      w.g3 * twiceB₁ (toSpectrum w) q v
        ((edge₂₃ (toSpectrum w) q v).im/D) (-(edge₁₃ (toSpectrum w) v).im/D) ((edge₁₂ (toSpectrum w) q).im/D) = 0) :
    ReducedRadialEquations (toSpectrum w) q v w.g1 w.g2 w.g3 := by
  rw [twiceB_reconstructed₂ _ _ _ _ hq, twiceB_reconstructed₁] at h₂
  rw [twiceB_reconstructed₃ _ _ _ _ hv, twiceB_reconstructed₁] at h₃
  unfold ReducedRadialEquations
  rw [rowDifference_imag, rowDifference_imag]
  field_simp at h₂ h₃
  constructor
  · linear_combination h₂
  · linear_combination h₃

/-- Explicit full-support generic pole exclusion, without dividing by g·r.
It applies to a stationary zero constrained to the pole once its radial multiplier
has been eliminated into the two displayed cross equations. -/
theorem full_support_cross_excludes_pole (w : WeightedData K) (he : weightedExceptional w ≠ 0)
    (q v : ComplexPair K) (r₁ r₂ r₃ : K)
    (hq : ComplexPair.normSq q = 1) (hv : ComplexPair.normSq v = 1)
    (hloop : (ComplexPair.mul (ComplexPair.mul (toSpectrum w).d₁₂ (toSpectrum w).d₂₃)
      (ComplexPair.conj (toSpectrum w).d₁₃)).im ≠ 0)
    (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0) (hr₃ : r₃ ≠ 0) (hsum : r₁+r₂+r₃=1)
    (hc : CurrentEquations r₁ r₂ r₃ (edge₁₂ (toSpectrum w) q).im
      (edge₁₃ (toSpectrum w) v).im (edge₂₃ (toSpectrum w) q v).im)
    (h₂ : w.g1 * twiceB₂ (toSpectrum w) q v r₁ r₂ r₃ -
      w.g2 * twiceB₁ (toSpectrum w) q v r₁ r₂ r₃ = 0)
    (h₃ : w.g1 * twiceB₃ (toSpectrum w) q v r₁ r₂ r₃ -
      w.g3 * twiceB₁ (toSpectrum w) q v r₁ r₂ r₃ = 0) :
    w.g1*r₁+w.g2*r₂+w.g3*r₃ ≠ 0 := by
  have hn := ComplexPair.nonreal_loop_excludes_zero (toSpectrum w).d₁₂ (toSpectrum w).d₁₃
    (toSpectrum w).d₂₃ q v hq hv hloop
  obtain ⟨hD, h1, h2, h3⟩ := current_reconstruction r₁ r₂ r₃
    (edge₁₂ (toSpectrum w) q).im (edge₁₃ (toSpectrum w) v).im (edge₂₃ (toSpectrum w) q v).im
    hr₁ hr₂ hr₃ hsum hc hn
  rw [h1, h2, h3] at h₂ h₃ ⊢
  exact weighted_reconstructed_weight_ne_zero w he q v hq hv
    (reconstructed_cross_implies_reduced w q v hq hv _ hD h₂ h₃) _ hD

/-- Complete full-support algebraic stationarity is equivalent to current reconstruction
plus an actual member of the finite sextic list. -/
theorem full_stationary_iff_sextic (w : WeightedData K) (he : weightedExceptional w ≠ 0)
    (q v : ComplexPair K) (r₁ r₂ r₃ : K)
    (hq : ComplexPair.normSq q = 1) (hv : ComplexPair.normSq v = 1)
    (hloop : (ComplexPair.mul (ComplexPair.mul (toSpectrum w).d₁₂ (toSpectrum w).d₂₃)
      (ComplexPair.conj (toSpectrum w).d₁₃)).im ≠ 0)
    (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0) (hr₃ : r₃ ≠ 0) (hsum : r₁+r₂+r₃=1)
    (hg₁ : w.g1 ≠ 0) (hG : w.g1*r₁+w.g2*r₂+w.g3*r₃ ≠ 0) :
    FullStationaryEquations (toSpectrum w) q v w.g1 w.g2 w.g3 r₁ r₂ r₃ ↔
    (currentDen (toSpectrum w) q v ≠ 0 ∧
      r₁ = (edge₂₃ (toSpectrum w) q v).im / currentDen (toSpectrum w) q v ∧
      r₂ = -(edge₁₃ (toSpectrum w) v).im / currentDen (toSpectrum w) q v ∧
      r₃ = (edge₁₂ (toSpectrum w) q).im / currentDen (toSpectrum w) q v ∧
      ∃ t u : K, (t,u) ∈ phaseCandidates (weightedP w) (weightedQ w) ∧
        circlePoint 1 t = q ∧ circlePoint 1 u = v) := by
  rw [full_stationary_iff_reduced (toSpectrum w) q v w.g1 w.g2 w.g3 r₁ r₂ r₃
    hq hv hloop hr₁ hr₂ hr₃ hsum hg₁ hG,
    weighted_reduced_iff_candidates w he q v hq hv]

end StationaryField
end W3.Elimination
