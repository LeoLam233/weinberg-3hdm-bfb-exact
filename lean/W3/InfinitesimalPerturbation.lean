import W3.InfinitesimalHierarchy
import W3.InfinitesimalResidue
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-! # The explicit fifteen-coordinate perturbation estimate and actual-field sign tests. -/
noncomputable section
namespace W3.Infinitesimal
open scoped BigOperators

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Source order: three diagonal monomials of bound one-half, followed by twelve
cross/complex monomials of bound one-quarter. -/
def monomialBound (i : Fin 15) : F := if i.val < 3 then 1 / 2 else 1 / 4

theorem fifteen_coordinate_bound (e M : Fin 15 → F) {u : F} (hu : 0 ≤ u)
    (he0 : ∀ i, 0 ≤ e i) (heu : ∀ i, e i ≤ u)
    (hM : ∀ i, |M i| ≤ monomialBound i) :
    |∑ i : Fin 15, e i * M i| ≤ (9 / 2) * u := by
  calc
    |∑ i : Fin 15, e i * M i| ≤ ∑ i : Fin 15, |e i * M i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 15, u * monomialBound i := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (he0 i)]
      exact mul_le_mul (heu i) (hM i) (abs_nonneg _) hu
    _ = (9 / 2) * u := by
      norm_num [monomialBound, Fin.sum_univ_succ]
      ring

/-- The fifteen subordinate perturbations in the original coefficient order. -/
def coefficientEpsilon (i : Fin 15) : SixteenLevelField := chronologicalEpsilon i.succ

theorem coefficientEpsilon_nonneg (i : Fin 15) : 0 ≤ coefficientEpsilon i :=
  (chronologicalEpsilon_infinitesimal i.succ).1.le

theorem coefficientEpsilon_le_one (i : Fin 15) : coefficientEpsilon i ≤ chronologicalEpsilon 1 := by
  have hle : (1 : Fin 16) ≤ i.succ := Nat.succ_le_succ (Nat.zero_le i.val)
  rcases eq_or_lt_of_le hle with h | h
  · rw [coefficientEpsilon, ← h]
  · have hh := towerCoordinates_scaled_lt realModel 16 i.succ.rev (1 : Fin 16).rev
      (Fin.rev_lt_rev.mpr h) 1 (by norm_num)
    have hlt : coefficientEpsilon i < chronologicalEpsilon 1 := by
      simpa only [coefficientEpsilon, chronologicalEpsilon, map_one, one_mul] using hh
    exact hlt.le

/-- Equation (39) in the actually constructed ordered field, with the stated
fifteen numerical monomial bounds left as explicit inputs from Gram geometry. -/
theorem actual_fifteen_coordinate_bound (M : Fin 15 → SixteenLevelField)
    (hM : ∀ i, |M i| ≤ monomialBound i) :
    |∑ i : Fin 15, coefficientEpsilon i * M i| ≤
      (9 / 2) * chronologicalEpsilon 1 :=
  fifteen_coordinate_bound coefficientEpsilon M
    (chronologicalEpsilon_infinitesimal 1).1.le
    coefficientEpsilon_nonneg coefficientEpsilon_le_one hM

/-- All four scalar signs plus the real residue, in the actual field rather than
an assumed extension. Only the exact minimum estimate remains as the premise. -/
theorem actual_signs_and_residue {m : ℝ} {y : SixteenLevelField}
    (hy : |y - realEmbedding16 m - chronologicalEpsilon 0| ≤
      (9 / 2) * chronologicalEpsilon 1) :
    (0 ≤ m ↔ 0 < y) ∧ (0 < m ↔ 2 * chronologicalEpsilon 0 < y) ∧
    (m < 0 ↔ y < 0) ∧
    (m = 0 ↔ 0 < y ∧ y < 2 * chronologicalEpsilon 0) ∧
    ArchimedeanClass.stdPart y = m := by
  rcases sign_thresholds realEmbedding16 (chronologicalEpsilon_infinitesimal 0)
    nine_halves_epsilon_one_lt_zero hy with ⟨h₁, h₂, h₃, h₄⟩
  exact ⟨h₁, h₂, h₃, h₄, stdPart_of_perturbation_bound realEmbedding16
    (chronologicalEpsilon_infinitesimal 0) nine_halves_epsilon_one_lt_zero hy⟩

#print axioms actual_fifteen_coordinate_bound
#print axioms actual_signs_and_residue
end W3.Infinitesimal
