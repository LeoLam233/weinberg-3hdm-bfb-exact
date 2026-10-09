import W3.FiniteInputSyntax

/-! Finite arithmetic on coefficient programs. No field element is admitted as
an extra constant: all operations preserve the original rational/input/epsilon leaves. -/
namespace W3.FiniteInput.CoefficientCode
variable {n : Nat}
instance : Add (CoefficientCode n) := ⟨CoefficientCode.add⟩
instance : Mul (CoefficientCode n) := ⟨CoefficientCode.mul⟩
instance : Neg (CoefficientCode n) := ⟨CoefficientCode.neg⟩
instance : Inv (CoefficientCode n) := ⟨CoefficientCode.inv⟩
instance : Sub (CoefficientCode n) := ⟨fun a b => a + -b⟩
instance : Div (CoefficientCode n) := ⟨fun a b => a * b⁻¹⟩
instance (k : Nat) : OfNat (CoefficientCode n) k := ⟨.rational k⟩

def arithmeticPower (a : CoefficientCode n) : Nat → CoefficientCode n
  | 0 => 1
  | k+1 => arithmeticPower a k * a
instance : Pow (CoefficientCode n) Nat := ⟨arithmeticPower⟩

variable {F : Type*} [Field F] [CharZero F]
variable (input : Fin 15 → F) (epsilon : Fin n → F)
@[simp] theorem eval_nat (k : Nat) :
    (OfNat.ofNat k : CoefficientCode n).eval input epsilon = (k : F) := by
  simp [OfNat.ofNat, eval]
@[simp] theorem eval_add (a b : CoefficientCode n) :
    (a+b).eval input epsilon = a.eval input epsilon + b.eval input epsilon := rfl
@[simp] theorem eval_mul (a b : CoefficientCode n) :
    (a*b).eval input epsilon = a.eval input epsilon * b.eval input epsilon := rfl
@[simp] theorem eval_neg (a : CoefficientCode n) :
    (-a).eval input epsilon = -a.eval input epsilon := rfl
@[simp] theorem eval_inv (a : CoefficientCode n) :
    (a⁻¹).eval input epsilon = (a.eval input epsilon)⁻¹ := rfl
@[simp] theorem eval_sub (a b : CoefficientCode n) :
    (a-b).eval input epsilon = a.eval input epsilon - b.eval input epsilon := by
  change (a + -b).eval input epsilon = _
  simp [sub_eq_add_neg]
@[simp] theorem eval_div (a b : CoefficientCode n) :
    (a/b).eval input epsilon = a.eval input epsilon / b.eval input epsilon := by
  change (a * b⁻¹).eval input epsilon = _
  simp [div_eq_mul_inv]
@[simp] theorem eval_pow (a : CoefficientCode n) (k : Nat) :
    (a^k).eval input epsilon = (a.eval input epsilon)^k := by
  induction k with
  | zero =>
    change (1 : CoefficientCode n).eval input epsilon = (a.eval input epsilon)^0
    rw [pow_zero]
    simpa only [Nat.cast_one] using eval_nat input epsilon 1
  | succ k ih =>
    change ((a^k)*a).eval input epsilon = _
    simp [ih,pow_succ]
@[simp] theorem eval_input (i : Fin 15) :
    (CoefficientCode.input i : CoefficientCode n).eval input epsilon = input i := rfl
@[simp] theorem eval_epsilon (i : Fin n) :
    (CoefficientCode.epsilon i).eval input epsilon = epsilon i := rfl
end W3.FiniteInput.CoefficientCode
