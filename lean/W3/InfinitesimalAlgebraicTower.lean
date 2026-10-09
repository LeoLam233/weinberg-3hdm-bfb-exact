import W3.InfinitesimalAlgebraicHull
import W3.InfinitesimalRationalTower
import W3.InfinitesimalRealBase

/-! # The actual nested algebraic real-closed subfields
These are relative algebraic closures of the finite rational presentations,
inside the constructed ultrapower tower. The preceding stage embeds coherently,
and the new epsilon dominates every positive element of that whole stage.
-/
noncomputable section
namespace W3.Infinitesimal
open Polynomial
attribute [local instance] rationalTowerAlgebra

abbrev AlgebraicTower (n : ℕ) := AlgebraicHull (RationalTower n) (Tower realModel n)

lemma rationalTower_step_comp (n : ℕ) :
    (rationalTowerHom (n + 1)).comp (rationalStep n) =
      (stepEmbed realModel n).toRingHom.comp (rationalTowerHom n) :=
  RingHom.ext (rationalTowerHom_step n)

/-- Algebraic elements of the preceding stage stay algebraic after the extension embedding. -/
theorem algebraicTower_step_mem (n : ℕ) (x : AlgebraicTower n) :
    stepEmbed realModel n (x : Tower realModel n) ∈
      algebraicClosure (RationalTower (n + 1)) (Tower realModel (n + 1)) := by
  apply mem_algebraicClosure_iff.mpr
  obtain ⟨p, hp, hroot⟩ := mem_algebraicClosure_iff.mp x.property
  refine ⟨p.map (rationalStep n), (Polynomial.map_ne_zero_iff (rationalStep n).injective).mpr hp, ?_⟩
  change (p.map (rationalStep n)).eval₂ (rationalTowerHom (n + 1))
    (stepEmbed realModel n (x : Tower realModel n)) = 0
  rw [Polynomial.eval₂_map, rationalTower_step_comp]
  have h := Polynomial.hom_eval₂ p (rationalTowerHom n)
    (stepEmbed realModel n).toRingHom (x : Tower realModel n)
  change stepEmbed realModel n (Polynomial.aeval (x : Tower realModel n) p) = _ at h
  rw [hroot, map_zero] at h
  exact h.symm

/-- The source's successive algebraic fields, embedded without replacing the ambient carrier. -/
def algebraicTowerStep (n : ℕ) : AlgebraicTower n →+*o AlgebraicTower (n + 1) where
  toFun x := ⟨stepEmbed realModel n x, algebraicTower_step_mem n x⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)
  monotone' := fun _ _ h => (stepEmbed realModel n).monotone' h

/-- The new epsilon lies in the algebraic field because it is already a rational generator. -/
def algebraicTowerEpsilon (n : ℕ) : AlgebraicTower (n + 1) :=
  ⟨stepEpsilon realModel n, mem_algebraicClosure_iff.mpr (by
    rw [← rationalTowerHom_variable n]
    change IsAlgebraic (RationalTower (n + 1))
      (algebraMap (RationalTower (n + 1)) (Tower realModel (n + 1)) (rationalVariable n))
    exact isAlgebraic_algebraMap (R := RationalTower (n + 1))
      (A := Tower realModel (n + 1)) (rationalVariable n))⟩

/-- Every restricted stage is genuinely ordered and real closed. -/
theorem algebraicTower_realClosed (n : ℕ) : IsRealClosed (AlgebraicTower n) := inferInstance

/-- Dominance is relative to all positive elements of the preceding algebraic field,
not merely the rational or integer scales. -/
theorem algebraicTower_epsilon_dominance (n : ℕ) :
    PositiveInfinitesimal (algebraicTowerStep n) (algebraicTowerEpsilon n) := by
  refine ⟨epsilon_pos _, ?_⟩
  intro r hr
  exact epsilon_lt_embed (Tower realModel n) hr

#print axioms algebraicTower_epsilon_dominance
#print axioms algebraicTower_realClosed
end W3.Infinitesimal
