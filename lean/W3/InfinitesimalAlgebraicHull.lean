import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.Algebra.Order.Field.Subfield

/-! The relative algebraic hull inside an ordered real closed ambient field is
itself ordered real closed. This distinguishes the source's algebraic field from
the larger ultrapower used to construct and verify it. -/
noncomputable section
namespace W3.Infinitesimal
open Polynomial

variable (F K : Type*) [Field F] [Field K] [Algebra F K]
  [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]

abbrev AlgebraicHull := algebraicClosure F K

instance algebraicHullStrictOrder : IsStrictOrderedRing (AlgebraicHull F K) :=
  inferInstanceAs (IsStrictOrderedRing (algebraicClosure F K).toSubfield)

/-- Nonnegative square roots in the ambient field lie in the algebraic hull. -/
theorem algebraicHull_square_of_nonneg {a : AlgebraicHull F K} (ha : 0 ≤ a) : IsSquare a := by
  obtain ⟨r,hr⟩ := (IsSquare.of_nonneg (show 0 ≤ (a : K) from ha) : IsSquare (a : K))
  have ha_alg : IsAlgebraic F (a : K) := mem_algebraicClosure_iff.mp a.property
  have hr_alg : IsAlgebraic F r := IsAlgebraic.of_pow (by decide : 0 < 2)
    (by simpa only [pow_two,← hr] using ha_alg)
  refine ⟨⟨r,mem_algebraicClosure_iff.mpr hr_alg⟩,?_⟩
  apply Subtype.ext
  exact hr

/-- Every odd polynomial over the hull has an ambient root; algebraic
transitivity proves that root remains inside the hull. -/
theorem algebraicHull_odd_root {p : (AlgebraicHull F K)[X]} (hp : Odd p.natDegree) :
    ∃ x : AlgebraicHull F K, p.IsRoot x := by
  let f : AlgebraicHull F K →+* K := algebraMap (AlgebraicHull F K) K
  have hdeg : (p.map f).natDegree = p.natDegree :=
    Polynomial.natDegree_map_eq_of_injective f.injective p
  obtain ⟨r,hr⟩ := IsRealClosed.exists_isRoot_of_odd_natDegree (f := p.map f) (hdeg ▸ hp)
  have hp0 : p ≠ 0 := by
    intro hz
    simp only [hz,Polynomial.natDegree_zero] at hp
    exact Nat.not_odd_zero hp
  have hr_alg_hull : IsAlgebraic (AlgebraicHull F K) r :=
    ⟨p,hp0,by simpa only [Polynomial.IsRoot,Polynomial.eval_map,Polynomial.aeval_def] using hr⟩
  have hr_alg : IsAlgebraic F r := hr_alg_hull.restrictScalars F
  let r' : AlgebraicHull F K := ⟨r,mem_algebraicClosure_iff.mpr hr_alg⟩
  refine ⟨r',?_⟩
  change p.eval r' = 0
  apply f.injective
  rw [← Polynomial.eval_map_apply,map_zero]
  exact hr

/-- The source-compatible algebraic real closed subfield, actually constructed
inside the ambient real closed field, with no custom real-closure axiom. -/
instance algebraicHullIsRealClosed : IsRealClosed (AlgebraicHull F K) :=
  IsRealClosed.of_linearOrderedField (algebraicHull_square_of_nonneg F K)
    (algebraicHull_odd_root F K)

#print axioms algebraicHullIsRealClosed
end W3.Infinitesimal
