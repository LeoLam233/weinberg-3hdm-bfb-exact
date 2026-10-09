import W3.InfinitesimalRootPresentation

/-! # Certified finite algebraic expression syntax
Selected roots carry their actual finite polynomial equations. Arithmetic and
square-root constructors retain a finite expression tree; they do not replace
the selected branch by an arbitrary algebraicity witness.
-/
noncomputable section
namespace W3.Infinitesimal
open Polynomial
universe u v
variable (F : Type u) (L : Type v) [Field F] [Field L] [Algebra F L]

inductive RootExpression : L → Type (max u v)
  | constant (a : F) : RootExpression (algebraMap F L a)
  | add {x y : L} : RootExpression x → RootExpression y → RootExpression (x + y)
  | mul {x y : L} : RootExpression x → RootExpression y → RootExpression (x * y)
  | neg {x : L} : RootExpression x → RootExpression (-x)
  | inverse {x : L} : RootExpression x → x ≠ 0 → RootExpression x⁻¹
  | selectedRoot (p : F[X]) (hp : p ≠ 0) (x : L) (hx : Polynomial.aeval x p = 0) :
      RootExpression x
  | squareRoot {r : L} : RootExpression r → (x : L) → x ^ 2 = r → RootExpression x

variable {L}

/-- Existence of a finite selected-root/arithmetic expression, stronger data than
an unstructured existential annihilator claim. -/
def Presented (x : L) : Prop := Nonempty (RootExpression F L x)

variable {F}

theorem presented_algebraMap (a : F) : Presented F (algebraMap F L a) :=
  ⟨RootExpression.constant a⟩

theorem presented_selectedRoot (p : F[X]) (hp : p ≠ 0) {x : L}
    (hx : Polynomial.aeval x p = 0) : Presented F x :=
  ⟨RootExpression.selectedRoot p hp x hx⟩

namespace Presented

variable {x y r : L}

theorem add (hx : Presented F x) (hy : Presented F y) : Presented F (x + y) := by
  obtain ⟨ex⟩ := hx
  obtain ⟨ey⟩ := hy
  exact ⟨.add ex ey⟩

theorem mul (hx : Presented F x) (hy : Presented F y) : Presented F (x * y) := by
  obtain ⟨ex⟩ := hx
  obtain ⟨ey⟩ := hy
  exact ⟨.mul ex ey⟩

theorem neg (hx : Presented F x) : Presented F (-x) := by
  obtain ⟨ex⟩ := hx
  exact ⟨.neg ex⟩

theorem sub (hx : Presented F x) (hy : Presented F y) : Presented F (x - y) := by
  simpa only [sub_eq_add_neg] using hx.add hy.neg

theorem zero : Presented F (0 : L) := by
  simpa only [map_zero] using presented_algebraMap (L := L) (0 : F)

theorem one : Presented F (1 : L) := by
  simpa only [map_one] using presented_algebraMap (L := L) (1 : F)

theorem inv (hx : Presented F x) : Presented F x⁻¹ := by
  by_cases h : x = 0
  · simpa only [h, inv_zero] using (zero (F := F) (L := L))
  · obtain ⟨ex⟩ := hx
    exact ⟨.inverse ex h⟩

theorem div (hx : Presented F x) (hy : Presented F y) : Presented F (x / y) := by
  simpa only [div_eq_mul_inv] using hx.mul hy.inv

theorem pow (hx : Presented F x) (n : ℕ) : Presented F (x ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using (one (F := F) (L := L))
  | succ n ih => simpa only [pow_succ] using ih.mul hx

theorem squareRoot (hr : Presented F r) (hx : x ^ 2 = r) : Presented F x := by
  obtain ⟨er⟩ := hr
  exact ⟨.squareRoot er x hx⟩

end Presented
#print axioms Presented.squareRoot
end W3.Infinitesimal
