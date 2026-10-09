import W3.InfinitesimalAlgebraicTower

/-! # Exact root and sign invariance of the algebraic subfield
Every ambient root of a nonzero polynomial over the algebraic hull is already
in the hull. Its inclusion preserves all field operations and order comparisons,
so selected algebraic branches and finite sign filters do not change.
-/
noncomputable section
namespace W3.Infinitesimal
open Polynomial

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
  [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]

/-- Full root closure, not merely the odd-degree real-closedness criterion. -/
theorem algebraicHull_ambient_root_mem {p : (AlgebraicHull F K)[X]} (hp : p ≠ 0)
    {x : K} (hx : p.eval₂ (algebraMap (AlgebraicHull F K) K) x = 0) :
    x ∈ AlgebraicHull F K := by
  have h : IsAlgebraic (AlgebraicHull F K) x := ⟨p, hp, hx⟩
  exact mem_algebraicClosure_iff.mpr (h.restrictScalars F)

/-- Restriction gives exactly the complete ambient root set, with no extra roots
created by performing the root computation in the larger ultrapower. -/
theorem algebraicHull_root_set_exact {p : (AlgebraicHull F K)[X]} (hp : p ≠ 0)
    (x : K) :
    p.eval₂ (algebraMap (AlgebraicHull F K) K) x = 0 ↔
      ∃ q : AlgebraicHull F K, p.IsRoot q ∧ (q : K) = x := by
  constructor
  · intro hx
    let q : AlgebraicHull F K := ⟨x, algebraicHull_ambient_root_mem hp hx⟩
    refine ⟨q, ?_, rfl⟩
    change p.eval q = 0
    apply (algebraMap (AlgebraicHull F K) K).injective
    rw [← Polynomial.eval_map_apply, Polynomial.eval_map, map_zero]
    exact hx
  · rintro ⟨q, hq, rfl⟩
    change p.eval₂ (algebraMap (AlgebraicHull F K) K)
      (algebraMap (AlgebraicHull F K) K q) = 0
    rw [← Polynomial.eval_map, Polynomial.eval_map_apply, hq, map_zero]

/-- Root comparisons use exactly the same order in the restricted field. -/
theorem algebraicHull_comparison (a b : AlgebraicHull F K) :
    ((a : K) < (b : K) ↔ a < b) ∧
    ((a : K) ≤ (b : K) ↔ a ≤ b) ∧
    ((a : K) = (b : K) ↔ a = b) :=
  ⟨Iff.rfl, Iff.rfl, Subtype.ext_iff.symm⟩

/-- A square-root branch selected in the ambient field remains in the hull,
including zero and repeated roots; its sign selection is unchanged. -/
theorem algebraicHull_squareRoot_mem {r : AlgebraicHull F K} {x : K}
    (hx : x ^ 2 = (r : K)) : x ∈ AlgebraicHull F K := by
  apply mem_algebraicClosure_iff.mpr
  apply IsAlgebraic.of_pow (n := 2) (by decide)
  rw [hx]
  exact mem_algebraicClosure_iff.mp r.property

/-- Arbitrary finite polynomial root lists computed in the ambient model can
therefore be interpreted, branch-for-branch and order-for-order, in the source
algebraic real-closed field. -/
theorem algebraicTower_root_set_exact (n : ℕ) {p : (AlgebraicTower n)[X]} (hp : p ≠ 0)
    (x : Tower realModel n) :
    p.eval₂ (algebraMap (AlgebraicTower n) (Tower realModel n)) x = 0 ↔
      ∃ q : AlgebraicTower n, p.IsRoot q ∧ (q : Tower realModel n) = x := by
  letI := rationalTowerAlgebra n
  exact algebraicHull_root_set_exact hp x

#print axioms algebraicTower_root_set_exact
#print axioms algebraicHull_squareRoot_mem
end W3.Infinitesimal
