import W3.Elimination

noncomputable section

namespace W3.Elimination
open Polynomial

/-- Real and imaginary parts of the complex row (A,B,C) in equation (17). -/
structure PhaseRow (R : Type*) where
  ar : R
  ai : R
  br : R
  bi : R
  cr : R
  ci : R

section PhaseRing
variable {R : Type*} [CommRing R]

def phaseValue (p : PhaseRow R) (t u : R) : R :=
  (p.ai * (1 - t ^ 2) + 2 * p.ar * t) * (1 + u ^ 2) +
  (p.bi * (1 - u ^ 2) + 2 * p.br * u) * (1 + t ^ 2) +
  p.ci * ((1 - t ^ 2) * (1 - u ^ 2) + 4 * t * u) +
  2 * p.cr * (u * (1 - t ^ 2) - t * (1 - u ^ 2))

def phaseA (p : PhaseRow R) : R[X] :=
  quad (C (-p.ai - p.bi + p.ci)) (C (2 * (p.ar + p.cr)))
    (C (p.ai - p.bi - p.ci)) X

def phaseB (p : PhaseRow R) : R[X] :=
  quad (C (2 * (p.br - p.cr))) (C (4 * p.ci)) (C (2 * (p.br + p.cr))) X

def phaseC (p : PhaseRow R) : R[X] :=
  quad (C (-p.ai + p.bi - p.ci)) (C (2 * (p.ar - p.cr)))
    (C (p.ai + p.bi + p.ci)) X

def phaseDiagonal (p : PhaseRow R) : R[X] :=
  quad (C (-p.ai - p.bi + p.ci)) (C (2 * (p.ar + p.br)))
    (C (p.ai + p.bi + p.ci)) X

def circlePoly : R[X] := 1 + X ^ 2

theorem phaseValue_eq_quad (p : PhaseRow R) (t u : R) :
    phaseValue p t u = quad ((phaseA p).eval t) ((phaseB p).eval t)
      ((phaseC p).eval t) u := by
  simp only [phaseValue, phaseA, phaseB, phaseC, quad, eval_add, eval_mul,
    eval_pow, eval_C, eval_X]
  ring

theorem phase_diagonal_factor (p : PhaseRow R) :
    quad (phaseA p) (phaseB p) (phaseC p) X = circlePoly * phaseDiagonal p := by
  simp only [quad, phaseA, phaseB, phaseC, phaseDiagonal, circlePoly,
    map_add, map_sub, map_mul, map_neg, map_ofNat]
  ring

def phaseResultant (p q : PhaseRow R) : R[X] :=
  resultant₂ (phaseA p) (phaseB p) (phaseC p) (phaseA q) (phaseB q) (phaseC q)

/-- A division-free exact quotient of the phase resultant by 1+X². -/
def phaseSextic (p q : PhaseRow R) : R[X] :=
  circlePoly * (phaseA p * phaseDiagonal q - phaseA q * phaseDiagonal p) ^ 2 -
  (phaseA p * phaseB q - phaseA q * phaseB p) *
    ((phaseB p + 2 * phaseA p * X) * phaseDiagonal q -
      phaseDiagonal p * (phaseB q + 2 * phaseA q * X))

theorem phase_resultant_factor (p q : PhaseRow R) :
    phaseResultant p q = circlePoly * phaseSextic p q :=
  shifted_resultant_factor _ _ _ _ _ _ _ _ _ _
    (phase_diagonal_factor p) (phase_diagonal_factor q)

theorem circle_dvd_phase_resultant (p q : PhaseRow R) :
    circlePoly ∣ phaseResultant p q := ⟨phaseSextic p q, phase_resultant_factor p q⟩

theorem natDegree_quad_C (a b c : R) :
    (quad (C a) (C b) (C c) (X : R[X])).natDegree ≤ 2 := by
  unfold quad
  apply natDegree_add_le_of_degree_le
  · apply natDegree_add_le_of_degree_le
    · exact natDegree_C_mul_X_pow_le a 2
    · simpa only [pow_one] using (natDegree_C_mul_X_pow_le b 1).trans (show 1 ≤ 2 by decide)
  · simp

theorem phaseA_degree (p : PhaseRow R) : (phaseA p).natDegree ≤ 2 :=
  natDegree_quad_C _ _ _

theorem phaseB_degree (p : PhaseRow R) : (phaseB p).natDegree ≤ 2 :=
  natDegree_quad_C _ _ _

theorem phaseC_degree (p : PhaseRow R) : (phaseC p).natDegree ≤ 2 :=
  natDegree_quad_C _ _ _

theorem resultant₂_degree_le (a b c d e f : R[X])
    (ha : a.natDegree ≤ 2) (hb : b.natDegree ≤ 2) (hc : c.natDegree ≤ 2)
    (hd : d.natDegree ≤ 2) (he : e.natDegree ≤ 2) (hf : f.natDegree ≤ 2) :
    (resultant₂ a b c d e f).natDegree ≤ 8 := by
  have muldeg {v w : R[X]} (hv : v.natDegree ≤ 2) (hw : w.natDegree ≤ 2) :
      (v * w).natDegree ≤ 4 := natDegree_mul_le_of_le hv hw
  have subdeg {v w : R[X]} (hv : v.natDegree ≤ 4) (hw : w.natDegree ≤ 4) :
      (v - w).natDegree ≤ 4 := (natDegree_sub_le _ _).trans (max_le hv hw)
  unfold resultant₂
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact natDegree_pow_le_of_le 2 (subdeg (muldeg ha hf) (muldeg hc hd))
  · exact natDegree_mul_le_of_le (subdeg (muldeg ha he) (muldeg hb hd))
      (subdeg (muldeg hb hf) (muldeg hc he))

theorem phase_resultant_degree_le (p q : PhaseRow R) :
    (phaseResultant p q).natDegree ≤ 8 :=
  resultant₂_degree_le _ _ _ _ _ _ (phaseA_degree p) (phaseB_degree p)
    (phaseC_degree p) (phaseA_degree q) (phaseB_degree q) (phaseC_degree q)

end PhaseRing

section PhaseDomain
variable {R : Type*} [CommRing R] [IsDomain R]

theorem circlePoly_degree : (circlePoly : R[X]).natDegree = 2 := by
  unfold circlePoly
  rw [add_comm, natDegree_add_eq_left_of_natDegree_lt]
  · simp
  · simp

theorem circlePoly_ne_zero : (circlePoly : R[X]) ≠ 0 := by
  intro h
  have hd := circlePoly_degree (R := R)
  rw [h, natDegree_zero] at hd
  contradiction

theorem phase_sextic_degree_le (p q : PhaseRow R) :
    (phaseSextic p q).natDegree ≤ 6 := by
  by_cases hS : phaseSextic p q = 0
  · simp [hS]
  have hd := phase_resultant_degree_le p q
  rw [phase_resultant_factor, natDegree_mul circlePoly_ne_zero hS, circlePoly_degree] at hd
  omega

end PhaseDomain
end W3.Elimination
