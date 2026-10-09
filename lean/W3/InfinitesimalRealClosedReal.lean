import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.Analysis.Polynomial.Order
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Lightweight proof that the real numbers satisfy the pinned real-closed interface. -/
noncomputable section
namespace W3.Infinitesimal
open Polynomial

/-- A direct proof for the real base, filling the TODO in the pinned basic interface. -/
instance realIsRealClosed : IsRealClosed ℝ := by
  apply IsRealClosed.of_linearOrderedField
  · intro x hx
    exact ⟨Real.sqrt x, (Real.mul_self_sqrt hx).symm⟩
  · intro p hp
    by_contra hn
    have hroot : ∀ x : ℝ, ¬p.IsRoot x := not_exists.mp hn
    have hpar : Int.negOnePow (p.natDegree : ℤ) = -1 :=
      Int.negOnePow_odd _ (by simpa using hp)
    rcases le_total 0 p.leadingCoeff with hl | hl
    · have hpos := Polynomial.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
        (P := p) (x := 0) (fun y hy => (hroot y hy).elim) hl
      have hneg := Polynomial.zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg
        (P := p) (x := 0) (fun y hy => (hroot y hy).elim) hl
      rw [hpar] at hneg
      norm_num at hneg
      linarith
    · have hneg := Polynomial.eval_lt_zero_of_roots_lt_of_leadingCoeff_nonpos
        (P := p) (x := 0) (fun y hy => (hroot y hy).elim) hl
      have hpos := Polynomial.negOnePow_mul_eval_lt_zero_of_lt_roots_of_leadingCoeff_nonpos
        (P := p) (x := 0) (fun y hy => (hroot y hy).elim) hl
      rw [hpar] at hpos
      norm_num at hpos
      linarith

#print axioms realIsRealClosed
end W3.Infinitesimal
