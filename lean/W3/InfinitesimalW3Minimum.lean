import W3.InfinitesimalMinimumTransfer
import W3.InfinitesimalRealBase
import W3.RealModel

/-! # Actual normalized W3 minima in every stage of the constructed real-closed tower.
This instantiates proved polynomial transfer with the exact fifteen-parameter,
twelve-real-coordinate Weinberg potential and mass-one constraint.
It establishes extrema, not yet retained-spectrum coverage.
-/
noncomputable section
namespace W3.Infinitesimal
open W3.RealModel

def w3DomainPolynomials : Fin 1 → MvPolynomial (Fin 12) ℤ :=
  fun _ => massConstraintPolynomial

def w3NoExtraEquations : Fin 0 → MvPolynomial (Fin 15 ⊕ Fin 12) ℤ := Fin.elim0

lemma w3_potential_intEval {K : Type*} [CommRing K] (κ : Parameters K) (x : RealFields K) :
    intPolynomialEval potentialPolynomial (Sum.elim κ x) = twiceQuartic κ x :=
  potentialPolynomial_eval κ x

lemma w3_mass_intEval {K : Type*} [CommRing K] (x : RealFields K) :
    intPolynomialEval massConstraintPolynomial x = mass x - 1 :=
  massConstraintPolynomial_eval x

/-- The concrete real compactness theorem exactly inhabits the transfer interface. -/
theorem w3_real_minimum_property :
    PolynomialMinimumProperty potentialPolynomial w3DomainPolynomials w3NoExtraEquations ℝ := by
  intro κ
  obtain ⟨x, hx, hmin⟩ := real_minimum κ
  refine ⟨x, ?_, ?_, ?_⟩
  · intro j
    change intPolynomialEval massConstraintPolynomial x = 0
    rw [w3_mass_intEval, hx, sub_self]
  · intro j
    exact Fin.elim0 j
  · intro y hy
    have hmass : mass y = 1 := by
      have h := hy 0
      change intPolynomialEval massConstraintPolynomial y = 0 at h
      rw [w3_mass_intEval] at h
      exact sub_eq_zero.mp h
    rw [w3_potential_intEval, w3_potential_intEval]
    exact hmin y hmass

/-- Exact normalized minima exist for every fifteen-coordinate input in every
constructed tower stage, including non-Archimedean and singular inputs. -/
theorem w3_tower_minimum (k : ℕ) (κ : Parameters (Tower realModel k)) :
    ∃ x : RealFields (Tower realModel k), mass x = 1 ∧
      ∀ y : RealFields (Tower realModel k), mass y = 1 →
        twiceQuartic κ x ≤ twiceQuartic κ y := by
  have hprop := polynomialMinimumProperty_tower potentialPolynomial w3DomainPolynomials
    w3NoExtraEquations realModel w3_real_minimum_property k
  obtain ⟨x, hx, _, hmin⟩ := hprop κ
  refine ⟨x, ?_, ?_⟩
  · have h := hx 0
    change intPolynomialEval massConstraintPolynomial x = 0 at h
    rw [w3_mass_intEval] at h
    exact sub_eq_zero.mp h
  · intro y hy
    have h := hmin y (fun j => by
      change intPolynomialEval massConstraintPolynomial y = 0
      rw [w3_mass_intEval, hy, sub_self])
    simpa only [w3_potential_intEval] using h

/-- The field used for all sixteen perturbation variables has actual physical
normalized minima; no coverage or minimizer premise is assumed. -/
theorem w3_sixteen_level_minimum (κ : Parameters SixteenLevelField) :
    ∃ x : RealFields SixteenLevelField, mass x = 1 ∧
      ∀ y : RealFields SixteenLevelField, mass y = 1 →
        twiceQuartic κ x ≤ twiceQuartic κ y :=
  w3_tower_minimum 16 κ

#print axioms w3_sixteen_level_minimum
end W3.Infinitesimal
