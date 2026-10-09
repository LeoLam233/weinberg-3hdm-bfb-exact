import W3.EliminationPolynomial

noncomputable section
namespace W3.Elimination
open Polynomial

section PrimalRing
variable {R : Type*} [CommRing R]

/-- Section-7 original order: a₁,a₂,a₃,b₁₂,b₁₃,b₂₃,c₁₂,c₁₃,c₂₃,
Re d₁₂,Im d₁₂,Re d₁₃,Im d₁₃,Re d₂₃,Im d₂₃. -/
def originalPrimal (x : Fin 15 → R) : WeightedData R :=
  ⟨x 0, x 1, x 2, x 3 + x 6, x 4 + x 7, x 5 + x 8,
    x 9, x 10, x 11, x 12, x 13, x 14, 1, 1, 1⟩

/-- The exceptional polynomial pulled back to all fifteen original quartic couplings. -/
def originalPrimalExceptionalPolynomial : MvPolynomial (Fin 15) R :=
  weightedExceptional (originalPrimal MvPolynomial.X)

@[simp] theorem map_originalPrimal {S : Type*} [CommRing S]
    (f : R →+* S) (x : Fin 15 → R) :
    mapWeighted f (originalPrimal x) = originalPrimal (fun i => f (x i)) := by
  simp [mapWeighted, originalPrimal]

theorem originalPrimalPolynomial_eval {S : Type*} [CommRing S]
    (f : R →+* S) (x : Fin 15 → S) :
    MvPolynomial.eval₂ f x (originalPrimalExceptionalPolynomial (R := R)) =
      weightedExceptional (originalPrimal x) := by
  change (MvPolynomial.eval₂Hom f x) (weightedExceptional (originalPrimal MvPolynomial.X)) = _
  rw [map_weightedExceptional, map_originalPrimal]
  simp only [MvPolynomial.eval₂Hom_X']

end PrimalRing

section PrimalWitness
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

def originalPrimalWitness : Fin 15 → R :=
  ![3/2, 5/3, 7/4, 1/3, -2/5, 3/7, 0, 0, 0, 2/3, 1/5, 3/5, -1/7, -4/7, 1/3]

theorem originalPrimal_witness_eq :
    originalPrimal (originalPrimalWitness : Fin 15 → R) = weightedWitness := by
  simp [originalPrimal, originalPrimalWitness, weightedWitness]

theorem originalPrimalExceptionalPolynomial_ne_zero :
    originalPrimalExceptionalPolynomial (R := R) ≠ 0 := by
  intro h
  have he := originalPrimalPolynomial_eval (RingHom.id R) (originalPrimalWitness : Fin 15 → R)
  rw [h, MvPolynomial.eval₂_zero, originalPrimal_witness_eq] at he
  exact weightedWitness_exceptional_ne_zero he.symm

end PrimalWitness

section AlgebraicSpecialization
variable {R K : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [CommRing K] [Algebra R K]

/-- Algebraic independence discharges the full primal phase exceptional condition.
No generic coverage proposition is assumed: the nonzero polynomial and witness are explicit. -/
theorem originalPrimalExceptional_ne_zero_of_independent (x : Fin 15 → K)
    (hx : AlgebraicIndependent R x) : weightedExceptional (originalPrimal x) ≠ 0 := by
  intro hz
  apply originalPrimalExceptionalPolynomial_ne_zero (R := R)
  apply hx.eq_zero_of_aeval_eq_zero
  change MvPolynomial.eval₂ (algebraMap R K) x (originalPrimalExceptionalPolynomial (R := R)) = 0
  rw [originalPrimalPolynomial_eval, hz]

end AlgebraicSpecialization
end W3.Elimination
