import W3.EliminationPolynomial

noncomputable section
namespace W3.Elimination
open Polynomial
section Scaling
variable {R : Type*} [CommRing R]

def scaleWeighted (k : R) (w : WeightedData R) : WeightedData R :=
  ⟨k*w.alpha1, k*w.alpha2, k*w.alpha3, k*w.e12, k*w.e13, k*w.e23,
    k*w.d12r, k*w.d12i, k*w.d13r, k*w.d13i, k*w.d23r, k*w.d23i,
    k*w.g1, k*w.g2, k*w.g3⟩

@[simp] theorem phaseA_scale (r : R) (p : PhaseRow R) :
    phaseA (scaleRow r p) = C r * phaseA p := by
  simp only [phaseA, scaleRow, quad, map_add, map_mul, map_sub, map_neg, map_ofNat]
  ring

@[simp] theorem phaseB_scale (r : R) (p : PhaseRow R) :
    phaseB (scaleRow r p) = C r * phaseB p := by
  simp only [phaseB, scaleRow, quad, map_add, map_mul, map_sub, map_neg, map_ofNat]
  ring

@[simp] theorem phaseC_scale (r : R) (p : PhaseRow R) :
    phaseC (scaleRow r p) = C r * phaseC p := by
  simp only [phaseC, scaleRow, quad, map_add, map_mul, map_sub, map_neg, map_ofNat]
  ring

@[simp] theorem phaseDiagonal_scale (r : R) (p : PhaseRow R) :
    phaseDiagonal (scaleRow r p) = C r * phaseDiagonal p := by
  simp only [phaseDiagonal, scaleRow, quad, map_add, map_mul, map_sub, map_neg, map_ofNat]
  ring

theorem phaseSextic_scale (r s : R) (p q : PhaseRow R) :
    phaseSextic (scaleRow r p) (scaleRow s q) = C (r^2*s^2) * phaseSextic p q := by
  simp only [phaseSextic, phaseA_scale, phaseB_scale, phaseDiagonal_scale, map_mul, map_pow]
  ring

theorem phaseLinearOne_scale (r s : R) (p q : PhaseRow R) :
    phaseLinearOne (scaleRow r p) (scaleRow s q) = C (r*s) * phaseLinearOne p q := by
  simp only [phaseLinearOne, linearOne, phaseA_scale, phaseB_scale, map_mul]
  ring

theorem phaseLinearZero_scale (r s : R) (p q : PhaseRow R) :
    phaseLinearZero (scaleRow r p) (scaleRow s q) = C (r*s) * phaseLinearZero p q := by
  simp only [phaseLinearZero, linearZero, phaseA_scale, phaseC_scale, map_mul]
  ring

theorem substitutedPhase_scale (r s z : R) (p q h : PhaseRow R) :
    substitutedPhase (scaleRow r p) (scaleRow s q) (scaleRow z h) =
      C (z*r^2*s^2) * substitutedPhase p q h := by
  simp only [substitutedPhase, phaseLinearOne_scale, phaseLinearZero_scale,
    phaseA_scale, phaseB_scale, phaseC_scale, map_mul, map_pow]
  ring

theorem boundaryT_scale (r s : R) (p q : PhaseRow R) :
    boundaryT (scaleRow r p) (scaleRow s q) = r^2*s^2 * boundaryT p q := by
  simp only [boundaryT, scaleRow, resultant₂]
  ring

theorem boundaryU_scale (r s : R) (p q : PhaseRow R) :
    boundaryU (scaleRow r p) (scaleRow s q) = r^2*s^2 * boundaryU p q := by
  simp only [boundaryU, scaleRow, resultant₂]
  ring

theorem linearExceptional_scale (r s : R) (p q : PhaseRow R) :
    linearExceptional (scaleRow r p) (scaleRow s q) = r^14*s^14 * linearExceptional p q := by
  unfold linearExceptional
  rw [phaseSextic_scale, phaseLinearOne_scale, resultant_C_mul_left, resultant_C_mul_right]
  ring

theorem poleExceptional_scale (r s z : R) (p q h : PhaseRow R) :
    poleExceptional (scaleRow r p) (scaleRow s q) (scaleRow z h) =
      r^32*s^32*z^6 * poleExceptional p q h := by
  unfold poleExceptional
  rw [phaseSextic_scale, substitutedPhase_scale, resultant_C_mul_left, resultant_C_mul_right]
  ring

theorem phaseExceptional_scale (r s z : R) (p q h : PhaseRow R) :
    phaseExceptional (scaleRow r p) (scaleRow s q) (scaleRow z h) =
      r^52*s^52*z^6 * phaseExceptional p q h := by
  unfold phaseExceptional
  rw [phaseSextic_scale, coeff_C_mul, boundaryT_scale, boundaryU_scale,
    linearExceptional_scale, poleExceptional_scale]
  ring

theorem weightedP_scale (r : R) (w : WeightedData R) :
    weightedP (scaleWeighted r w) = scaleRow (r^3) (weightedP w) := by
  simp only [weightedP, weightedF, weightedC1, weightedC2, scaleWeighted, scaleRow, subRow]
  congr 1 <;> ring

theorem weightedQ_scale (r : R) (w : WeightedData R) :
    weightedQ (scaleWeighted r w) = scaleRow (r^3) (weightedQ w) := by
  simp only [weightedQ, weightedG, weightedC1, weightedC3, scaleWeighted, scaleRow, subRow]
  congr 1 <;> ring

theorem weightedPole_scale (r : R) (w : WeightedData R) :
    weightedPole (scaleWeighted r w) = scaleRow (r^2) (weightedPole w) := by
  simp only [weightedPole, weightedH, scaleWeighted, scaleRow]
  congr 1 <;> ring

/-- Total homogeneity degree of the explicit weighted exceptional scalar. -/
theorem weightedExceptional_scale (r : R) (w : WeightedData R) :
    weightedExceptional (scaleWeighted r w) = r^324 * weightedExceptional w := by
  unfold weightedExceptional
  rw [weightedP_scale, weightedQ_scale, weightedPole_scale, phaseExceptional_scale]
  ring

end Scaling
end W3.Elimination
