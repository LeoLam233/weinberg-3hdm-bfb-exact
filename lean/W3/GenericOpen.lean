import W3.EliminationOperator
import W3.OperatorTwoSpectrum
import Mathlib.Algebra.MvPolynomial.Funext

/-! A single nonzero exceptional polynomial and its nonempty principal-open
complement in the original fifteen real coefficient coordinates. -/
noncomputable section
namespace W3.Elimination
open MvPolynomial

def genericPolynomial : MvPolynomial (Fin 15) ℝ :=
  completePrimalPolynomial * completeDualPolynomial

lemma genericPolynomial_ne_zero : genericPolynomial ≠ 0 :=
  mul_ne_zero completePrimalPolynomial_ne_zero completeDualPolynomial_ne_zero

/-- A principal Zariski-open set, specified explicitly as the complement of one polynomial zero set. -/
def GenericLocus : Set (Fin 15 → ℝ) := {x | MvPolynomial.eval x genericPolynomial ≠ 0}

theorem genericLocus_nonempty : GenericLocus.Nonempty := by
  classical
  by_contra h
  apply genericPolynomial_ne_zero
  apply MvPolynomial.funext
  intro x
  have hx : MvPolynomial.eval x genericPolynomial = 0 := by
    by_contra hn
    exact h ⟨x,hn⟩
  simpa using hx

/-- The explicit proper-polynomial condition supplies all actual operator and
weighted spectrum exclusions simultaneously. -/
theorem genericLocus_conditions (x : Fin 15 → ℝ) (hx : x ∈ GenericLocus) :
    completeWeightedExceptional (originalPrimal x) ≠ 0 ∧ originalInverseDen x ≠ 0 ∧
      completeWeightedExceptional (originalDual x) ≠ 0 := by
  change MvPolynomial.eval x genericPolynomial ≠ 0 at hx
  rw [genericPolynomial,map_mul] at hx
  obtain ⟨hp,hd⟩ := mul_ne_zero_iff.mp hx
  change MvPolynomial.eval₂ (RingHom.id ℝ) x completePrimalPolynomial ≠ 0 at hp
  change MvPolynomial.eval₂ (RingHom.id ℝ) x completeDualPolynomial ≠ 0 at hd
  rw [completePrimalPolynomial_eval] at hp
  rw [completeDualPolynomial_eval] at hd
  obtain ⟨hinv,he⟩ := mul_ne_zero_iff.mp hd
  refine ⟨hp,hinv,?_⟩
  rw [originalDualNumerators_eq x hinv,completeWeightedExceptional_scale] at he
  exact (mul_ne_zero_iff.mp he).2

/-- In particular the ordinary, undeformed theorem is not vacuous. -/
theorem exists_real_simultaneously_regular : ∃ x : Fin 15 → ℝ,
    completeWeightedExceptional (originalPrimal x) ≠ 0 ∧ originalInverseDen x ≠ 0 ∧
      completeWeightedExceptional (originalDual x) ≠ 0 := by
  obtain ⟨x,hx⟩ := genericLocus_nonempty
  exact ⟨x,genericLocus_conditions x hx⟩

#print axioms genericLocus_nonempty
#print axioms genericLocus_conditions
end W3.Elimination
