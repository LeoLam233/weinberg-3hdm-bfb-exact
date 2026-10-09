import W3.WeightedPhase
import W3.EliminationProjective

noncomputable section
namespace W3.Weighted
open W3.Elimination
open ComplexPair
section Field
variable {K : Type*} [Field K]

/-- Projective half-angle map, including the phase -1 at [0:1]. -/
def circlePoint (x y : K) : ComplexPair K :=
  ⟨(x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2), 2 * x * y / (x ^ 2 + y ^ 2)⟩

theorem circlePoint_norm (x y : K) (h : x ^ 2 + y ^ 2 ≠ 0) :
    normSq (circlePoint x y) = 1 := by
  unfold normSq circlePoint
  field_simp
  ring

/-- Exact projective denominator clearing, including all four affine charts. -/
theorem rowImag_circlePoint (p : PhaseRow K) (x y z w : K)
    (ht : x ^ 2 + y ^ 2 ≠ 0) (hu : z ^ 2 + w ^ 2 ≠ 0) :
    rowImag p (circlePoint x y) (circlePoint z w) =
      phaseHom p x y z w / ((x ^ 2 + y ^ 2) * (z ^ 2 + w ^ 2)) := by
  unfold rowImag circlePoint phaseHom mul conj
  field_simp
  ring

theorem rowImag_circlePoint_zero_iff (p : PhaseRow K) (x y z w : K)
    (ht : x ^ 2 + y ^ 2 ≠ 0) (hu : z ^ 2 + w ^ 2 ≠ 0) :
    rowImag p (circlePoint x y) (circlePoint z w) = 0 ↔ phaseHom p x y z w = 0 := by
  rw [rowImag_circlePoint p x y z w ht hu, div_eq_zero_iff]
  simp [ht, hu]

theorem rowImag_halfAngle (p : PhaseRow K) (t u : K)
    (ht : 1 + t ^ 2 ≠ 0) (hu : 1 + u ^ 2 ≠ 0) :
    rowImag p (circlePoint 1 t) (circlePoint 1 u) =
      phaseValue p t u / ((1 + t ^ 2) * (1 + u ^ 2)) := by
  have ht' : (1 : K) ^ 2 + t ^ 2 ≠ 0 := by simpa using ht
  have hu' : (1 : K) ^ 2 + u ^ 2 ≠ 0 := by simpa using hu
  rw [rowImag_circlePoint p 1 t 1 u ht' hu']
  simp only [one_pow, phaseHom, phaseValue, one_mul, mul_one]

end Field
section Ordered
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem circle_den_ne_zero (x y : K) (h : x ≠ 0 ∨ y ≠ 0) : x ^ 2 + y ^ 2 ≠ 0 := by
  intro hz
  have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  exact h.elim (fun h => h hx) (fun h => h hy)

/-- Every algebraic unit-circle point has real projective half-angle
coordinates. This covers the phase pi rather than assuming it away. -/
theorem circlePoint_surjective (q : ComplexPair K) (hq : normSq q = 1) :
    ∃ x y : K, (x ≠ 0 ∨ y ≠ 0) ∧ circlePoint x y = q := by
  have hn : q.re ^ 2 + q.im ^ 2 = 1 := hq
  by_cases hminus : q.re = -1
  · have hi : q.im = 0 := by rw [hminus] at hn; nlinarith [sq_nonneg q.im]
    refine ⟨0, 1, Or.inr one_ne_zero, ?_⟩
    cases q with
    | mk a b =>
      dsimp only at hminus hi
      subst a; subst b
      simp [circlePoint]
  · have hx : 1 + q.re ≠ 0 := by intro hz; apply hminus; linear_combination hz
    have hD := circle_den_ne_zero (1 + q.re) q.im (Or.inl hx)
    refine ⟨1 + q.re, q.im, Or.inl hx, ?_⟩
    cases q with
    | mk a b =>
      apply congrArg₂ ComplexPair.mk
      · dsimp only [circlePoint]
        apply (div_eq_iff hD).mpr
        dsimp only at hn
        linear_combination -(a + 1) * hn
      · dsimp only [circlePoint]
        apply (div_eq_iff hD).mpr
        dsimp only at hn
        linear_combination -b * hn

/-- Unit-circle phase equations are exactly their real projective polynomial
representation. Neither surjectivity nor clearing denominators is assumed. -/
theorem circle_phase_projective (p s : PhaseRow K) (q v : ComplexPair K)
    (hq : normSq q = 1) (hv : normSq v = 1) :
    ∃ x y z w : K, (x ≠ 0 ∨ y ≠ 0) ∧ (z ≠ 0 ∨ w ≠ 0) ∧
      circlePoint x y = q ∧ circlePoint z w = v ∧
      ((rowImag p q v = 0 ∧ rowImag s q v = 0) ↔
        (phaseHom p x y z w = 0 ∧ phaseHom s x y z w = 0)) := by
  obtain ⟨x, y, ht, hq'⟩ := circlePoint_surjective q hq
  obtain ⟨z, w, hu, hv'⟩ := circlePoint_surjective v hv
  refine ⟨x, y, z, w, ht, hu, hq', hv', ?_⟩
  rw [← hq', ← hv']
  exact and_congr
    (rowImag_circlePoint_zero_iff p x y z w (circle_den_ne_zero x y ht) (circle_den_ne_zero z w hu))
    (rowImag_circlePoint_zero_iff s x y z w (circle_den_ne_zero x y ht) (circle_den_ne_zero z w hu))
end Ordered
end W3.Weighted
