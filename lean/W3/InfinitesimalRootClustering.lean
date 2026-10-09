import W3.InfinitesimalAlgebraicResidue
import Mathlib.Analysis.Polynomial.Order
import Mathlib.Topology.Order.Compact

/-! # Real compact root-clustering, the base theorem for relative algebraic residue.
No simplicity, distinct-root separation, or nonzero derivative assumption occurs.
-/
noncomputable section
namespace W3.Infinitesimal
open Polynomial

/-- On a bounded real interval, sufficiently small polynomial value forces the
point to be within any prescribed positive distance of some real root.
Repeated roots and the zero polynomial are included. -/
theorem real_polynomial_root_clustering (p : ℝ[X]) (B δ : ℝ) (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ y : ℝ, |y| ≤ B → |p.eval y| < η →
      ∃ q : ℝ, p.IsRoot q ∧ |y - q| < δ := by
  classical
  let A : Set ℝ := Set.Icc (-B) B ∩ {y | ∀ q : ℝ, p.IsRoot q → δ ≤ |y - q|}
  have hclosed : IsClosed {y : ℝ | ∀ q : ℝ, p.IsRoot q → δ ≤ |y - q|} := by
    have hh : IsClosed (⋂ q : ℝ, ⋂ (_ : p.IsRoot q), {y : ℝ | δ ≤ |y - q|}) :=
      isClosed_iInter (fun q => isClosed_iInter (fun _ =>
        isClosed_le continuous_const (continuous_id.sub continuous_const).abs))
    convert hh using 1
    ext y
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
  have hcompact : IsCompact A := isCompact_Icc.inter_right hclosed
  have hmem {y : ℝ} (hy : |y| ≤ B)
      (hn : ¬∃ q : ℝ, p.IsRoot q ∧ |y - q| < δ) : y ∈ A := by
    refine ⟨abs_le.mp hy, ?_⟩
    intro q hq
    exact le_of_not_gt (fun h => hn ⟨q, hq, h⟩)
  by_cases hA : A.Nonempty
  · obtain ⟨y₀, hy₀, hmin⟩ := hcompact.exists_isMinOn hA p.continuous.abs.continuousOn
    have hp₀ : p.eval y₀ ≠ 0 := by
      intro h
      have hh := hy₀.2 y₀ h
      have hz : δ ≤ 0 := by simpa only [sub_self, abs_zero] using hh
      exact hδ.not_ge hz
    refine ⟨|p.eval y₀|, abs_pos.mpr hp₀, ?_⟩
    intro y hy hsmall
    by_contra hn
    exact (hmin (hmem hy hn)).not_gt hsmall
  · refine ⟨1, zero_lt_one, ?_⟩
    intro y hy _
    by_contra hn
    exact hA ⟨y, hmem hy hn⟩

#print axioms real_polynomial_root_clustering
end W3.Infinitesimal
