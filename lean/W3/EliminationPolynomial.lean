import W3.EliminationWeighted
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.AlgebraicIndependent.Defs

noncomputable section
namespace W3.Elimination
open Polynomial

section Naturality
variable {R S : Type*} [CommRing R] [CommRing S]

def mapRow (f : R →+* S) (p : PhaseRow R) : PhaseRow S :=
  ⟨f p.ar, f p.ai, f p.br, f p.bi, f p.cr, f p.ci⟩

def mapWeighted (f : R →+* S) (w : WeightedData R) : WeightedData S :=
  ⟨f w.alpha1, f w.alpha2, f w.alpha3, f w.e12, f w.e13, f w.e23,
    f w.d12r, f w.d12i, f w.d13r, f w.d13i, f w.d23r, f w.d23i, f w.g1, f w.g2, f w.g3⟩

@[simp] theorem map_phaseA (f : R →+* S) (p : PhaseRow R) :
    (phaseA p).map f = phaseA (mapRow f p) := by
  simp [phaseA, quad, mapRow, map_ofNat]

@[simp] theorem map_phaseB (f : R →+* S) (p : PhaseRow R) :
    (phaseB p).map f = phaseB (mapRow f p) := by
  simp [phaseB, quad, mapRow, map_ofNat]

@[simp] theorem map_phaseC (f : R →+* S) (p : PhaseRow R) :
    (phaseC p).map f = phaseC (mapRow f p) := by
  simp [phaseC, quad, mapRow, map_ofNat]

@[simp] theorem map_phaseDiagonal (f : R →+* S) (p : PhaseRow R) :
    (phaseDiagonal p).map f = phaseDiagonal (mapRow f p) := by
  simp [phaseDiagonal, quad, mapRow, map_ofNat]

@[simp] theorem map_circlePoly (f : R →+* S) :
    (circlePoly : R[X]).map f = circlePoly := by
  simp [circlePoly]

@[simp] theorem map_phaseSextic (f : R →+* S) (p q : PhaseRow R) :
    (phaseSextic p q).map f = phaseSextic (mapRow f p) (mapRow f q) := by
  simp [phaseSextic]

@[simp] theorem map_phaseLinearOne (f : R →+* S) (p q : PhaseRow R) :
    (phaseLinearOne p q).map f = phaseLinearOne (mapRow f p) (mapRow f q) := by
  simp [phaseLinearOne, linearOne]

@[simp] theorem map_phaseLinearZero (f : R →+* S) (p q : PhaseRow R) :
    (phaseLinearZero p q).map f = phaseLinearZero (mapRow f p) (mapRow f q) := by
  simp [phaseLinearZero, linearZero]

@[simp] theorem map_substitutedPhase (f : R →+* S) (p q h : PhaseRow R) :
    (substitutedPhase p q h).map f = substitutedPhase (mapRow f p) (mapRow f q) (mapRow f h) := by
  simp [substitutedPhase]

@[simp] theorem map_boundaryT (f : R →+* S) (p q : PhaseRow R) :
    f (boundaryT p q) = boundaryT (mapRow f p) (mapRow f q) := by
  simp [boundaryT, resultant₂, mapRow, map_ofNat]

@[simp] theorem map_boundaryU (f : R →+* S) (p q : PhaseRow R) :
    f (boundaryU p q) = boundaryU (mapRow f p) (mapRow f q) := by
  simp [boundaryU, resultant₂, mapRow, map_ofNat]

@[simp] theorem map_linearExceptional (f : R →+* S) (p q : PhaseRow R) :
    f (linearExceptional p q) = linearExceptional (mapRow f p) (mapRow f q) := by
  unfold linearExceptional
  rw [← resultant_map_map, map_phaseSextic, map_phaseLinearOne]

@[simp] theorem map_poleExceptional (f : R →+* S) (p q h : PhaseRow R) :
    f (poleExceptional p q h) = poleExceptional (mapRow f p) (mapRow f q) (mapRow f h) := by
  unfold poleExceptional
  rw [← resultant_map_map, map_phaseSextic, map_substitutedPhase]

@[simp] theorem map_phaseExceptional (f : R →+* S) (p q h : PhaseRow R) :
    f (phaseExceptional p q h) = phaseExceptional (mapRow f p) (mapRow f q) (mapRow f h) := by
  simp only [phaseExceptional, map_mul, map_boundaryT, map_boundaryU,
    map_linearExceptional, map_poleExceptional]
  rw [← coeff_map, map_phaseSextic]

@[simp] theorem map_weightedP (f : R →+* S) (w : WeightedData R) :
    mapRow f (weightedP w) = weightedP (mapWeighted f w) := by
  simp [mapRow, weightedP, weightedF, weightedC1, weightedC2, scaleRow, subRow, mapWeighted, map_ofNat]

@[simp] theorem map_weightedQ (f : R →+* S) (w : WeightedData R) :
    mapRow f (weightedQ w) = weightedQ (mapWeighted f w) := by
  simp [mapRow, weightedQ, weightedG, weightedC1, weightedC3, scaleRow, subRow, mapWeighted, map_ofNat]

@[simp] theorem map_weightedPole (f : R →+* S) (w : WeightedData R) :
    mapRow f (weightedPole w) = weightedPole (mapWeighted f w) := by
  simp [mapRow, weightedPole, weightedH, scaleRow, mapWeighted, map_ofNat]

@[simp] theorem map_weightedExceptional (f : R →+* S) (w : WeightedData R) :
    f (weightedExceptional w) = weightedExceptional (mapWeighted f w) := by
  simp [weightedExceptional]

end Naturality

/-- Variable order: α₁,α₂,α₃,e₁₂,e₁₃,e₂₃,Re d₁₂,Im d₁₂,Re d₁₃,Im d₁₃,Re d₂₃,Im d₂₃,g₁,g₂,g₃. -/
def universalWeighted : WeightedData (MvPolynomial (Fin 15) ℚ) :=
  ⟨MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2,
    MvPolynomial.X 3, MvPolynomial.X 4, MvPolynomial.X 5,
    MvPolynomial.X 6, MvPolynomial.X 7, MvPolynomial.X 8,
    MvPolynomial.X 9, MvPolynomial.X 10, MvPolynomial.X 11,
    MvPolynomial.X 12, MvPolynomial.X 13, MvPolynomial.X 14⟩

/-- An actual multivariate exceptional polynomial in all fifteen weighted coordinates. -/
def weightedExceptionalPolynomial : MvPolynomial (Fin 15) ℚ :=
  weightedExceptional universalWeighted

def weightedCoordinates {R : Type*} (w : WeightedData R) : Fin 15 → R :=
  ![w.alpha1, w.alpha2, w.alpha3, w.e12, w.e13, w.e23,
    w.d12r, w.d12i, w.d13r, w.d13i, w.d23r, w.d23i, w.g1, w.g2, w.g3]

section Evaluate
variable {K : Type*} [Field K] [CharZero K]

theorem universalWeighted_eval (w : WeightedData K) :
    mapWeighted (MvPolynomial.eval₂Hom (Rat.castHom K) (weightedCoordinates w)) universalWeighted = w := by
  cases w
  simp [mapWeighted, universalWeighted, weightedCoordinates]

theorem weightedExceptionalPolynomial_eval (w : WeightedData K) :
    MvPolynomial.eval₂ (Rat.castHom K) (weightedCoordinates w) weightedExceptionalPolynomial =
      weightedExceptional w := by
  change (MvPolynomial.eval₂Hom (Rat.castHom K) (weightedCoordinates w))
    (weightedExceptional universalWeighted) = _
  rw [map_weightedExceptional, universalWeighted_eval]

end Evaluate

theorem weightedExceptionalPolynomial_ne_zero : weightedExceptionalPolynomial ≠ 0 := by
  intro h
  have he := weightedExceptionalPolynomial_eval (weightedWitness : WeightedData ℚ)
  rw [h, MvPolynomial.eval₂_zero] at he
  exact weightedWitness_exceptional_ne_zero he.symm

/-- Primal specialization; the final three universal coordinates are unused. -/
def asPrimal {R : Type*} [One R] (w : WeightedData R) : WeightedData R :=
  { w with g1 := 1, g2 := 1, g3 := 1 }

def primalExceptionalPolynomial : MvPolynomial (Fin 15) ℚ :=
  weightedExceptional (asPrimal universalWeighted)

section PrimalEvaluate
variable {K : Type*} [Field K] [CharZero K]

theorem map_asPrimal {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (w : WeightedData R) :
    mapWeighted f (asPrimal w) = asPrimal (mapWeighted f w) := by
  simp [mapWeighted, asPrimal]

theorem primalExceptionalPolynomial_eval (w : WeightedData K) :
    MvPolynomial.eval₂ (Rat.castHom K) (weightedCoordinates w) primalExceptionalPolynomial =
      weightedExceptional (asPrimal w) := by
  change (MvPolynomial.eval₂Hom (Rat.castHom K) (weightedCoordinates w))
    (weightedExceptional (asPrimal universalWeighted)) = _
  rw [map_weightedExceptional, map_asPrimal, universalWeighted_eval]

theorem weightedExceptional_ne_zero_of_algebraicIndependent (w : WeightedData K)
    (h : AlgebraicIndependent ℚ (weightedCoordinates w)) : weightedExceptional w ≠ 0 := by
  intro hz
  apply weightedExceptionalPolynomial_ne_zero
  apply h.eq_zero_of_aeval_eq_zero
  change MvPolynomial.eval₂ (Rat.castHom K) (weightedCoordinates w) weightedExceptionalPolynomial = 0
  rw [weightedExceptionalPolynomial_eval, hz]

end PrimalEvaluate

theorem primalExceptionalPolynomial_ne_zero : primalExceptionalPolynomial ≠ 0 := by
  intro h
  have he := primalExceptionalPolynomial_eval (weightedWitness : WeightedData ℚ)
  rw [h, MvPolynomial.eval₂_zero] at he
  have hp : asPrimal (weightedWitness : WeightedData ℚ) = weightedWitness := rfl
  rw [hp] at he
  exact weightedWitness_exceptional_ne_zero he.symm

section PrimalIndependent
variable {K : Type*} [Field K] [CharZero K]

theorem primalExceptional_ne_zero_of_algebraicIndependent (w : WeightedData K)
    (h : AlgebraicIndependent ℚ (weightedCoordinates w)) : weightedExceptional (asPrimal w) ≠ 0 := by
  intro hz
  apply primalExceptionalPolynomial_ne_zero
  apply h.eq_zero_of_aeval_eq_zero
  change MvPolynomial.eval₂ (Rat.castHom K) (weightedCoordinates w) primalExceptionalPolynomial = 0
  rw [primalExceptionalPolynomial_eval, hz]

end PrimalIndependent

end W3.Elimination
