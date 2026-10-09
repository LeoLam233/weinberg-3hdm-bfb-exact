import W3.FiniteInputResidueDenominators
import W3.InfinitesimalCoefficientResidueProgram

/-! # Coded denominator clearing, variable swap, and initial normalization
Every polynomial transformation acts on finite lists of finite-input coefficient
codes. The semantic equalities below certify those actual lists. -/
noncomputable section
namespace W3.FiniteInput
open Polynomial W3.Infinitesimal
set_option backward.isDefEq.respectTransparency false

abbrev BivariateCode (n : Nat) := List (List (CoefficientCode n))

def bivariatePolynomial (u : Fin 15 → ℝ) {n : Nat} (cs : BivariateCode n) :
    (RationalTower n)[X][X] := polynomialOfList (cs.map (stagePolynomial u))

namespace BivariateCode
variable {n : Nat}

def add : BivariateCode n → BivariateCode n → BivariateCode n
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => PolynomialCode.add a b :: add as bs

def scale (a : List (CoefficientCode n)) (bs : BivariateCode n) : BivariateCode n :=
  bs.map (PolynomialCode.mul a)

def innerX (bs : BivariateCode n) : BivariateCode n :=
  bs.map (fun b => .rational 0 :: b)

def outer (a : List (CoefficientCode n)) : BivariateCode n := a.map (fun c => [c])

def swap : BivariateCode n → BivariateCode n
  | [] => []
  | a :: as => add (outer a) (innerX (swap as))

@[simp] theorem eval_nil (u : Fin 15 → ℝ) :
    bivariatePolynomial u ([] : BivariateCode n) = 0 := rfl

@[simp] theorem eval_cons (u : Fin 15 → ℝ) (a : List (CoefficientCode n)) (as : BivariateCode n) :
    bivariatePolynomial u (a :: as) = C (stagePolynomial u a) + X * bivariatePolynomial u as := rfl

@[simp] theorem eval_add (u : Fin 15 → ℝ) (as bs : BivariateCode n) :
    bivariatePolynomial u (add as bs) = bivariatePolynomial u as + bivariatePolynomial u bs := by
  induction as generalizing bs with
  | nil => simp [add]
  | cons a as ih =>
    cases bs with
    | nil => simp [add]
    | cons b bs =>
      simp only [add, eval_cons, stagePolynomial, PolynomialCode.eval_add, map_add, ih]
      ring

@[simp] theorem eval_scale (u : Fin 15 → ℝ) (a : List (CoefficientCode n)) (bs : BivariateCode n) :
    bivariatePolynomial u (scale a bs) = C (stagePolynomial u a) * bivariatePolynomial u bs := by
  induction bs with
  | nil => simp [scale]
  | cons b bs ih =>
    change bivariatePolynomial u (PolynomialCode.mul a b :: scale a bs) = _
    simp only [eval_cons, stagePolynomial, PolynomialCode.eval_mul, map_mul] at *
    rw [ih]
    ring

@[simp] theorem eval_innerX (u : Fin 15 → ℝ) (bs : BivariateCode n) :
    bivariatePolynomial u (innerX bs) = C X * bivariatePolynomial u bs := by
  induction bs with
  | nil => simp [innerX]
  | cons b bs ih =>
    change bivariatePolynomial u ((.rational 0 :: b) :: innerX bs) = _
    simp only [eval_cons, stagePolynomial, PolynomialCode.eval_cons, CoefficientCode.eval,
      Rat.cast_zero, map_zero, zero_add, map_mul] at *
    rw [ih]
    ring

@[simp] theorem eval_outer (u : Fin 15 → ℝ) (a : List (CoefficientCode n)) :
    bivariatePolynomial u (outer a) = (stagePolynomial u a).map C := by
  induction a with
  | nil => simp [outer, stagePolynomial]
  | cons a as ih =>
    change bivariatePolynomial u ([a] :: outer as) = _
    simp only [eval_cons, FractionCode.stagePolynomial_singleton, ih,
      stagePolynomial, PolynomialCode.eval_cons, Polynomial.map_add,
      Polynomial.map_C, Polynomial.map_mul, Polynomial.map_X, PolynomialCode.eval_nil, mul_zero, add_zero]

@[simp] theorem eval_swap (u : Fin 15 → ℝ) (cs : BivariateCode n) :
    bivariatePolynomial u (swap cs) = Polynomial.Bivariate.swap (bivariatePolynomial u cs) := by
  induction cs with
  | nil => simp [swap]
  | cons c cs ih =>
    simp only [swap, eval_add, eval_outer, eval_innerX, ih, eval_cons,
      map_add, map_mul, Polynomial.Bivariate.swap_C, Polynomial.Bivariate.swap_Y]

variable [DecidableEq (RationalTower n)]

/-- This recursion uses the same finite equality tests and fuel as stripInitial. -/
def strip (u : Fin 15 → ℝ) : Nat → BivariateCode n → Nat × BivariateCode n
  | 0, cs => (0, cs)
  | fuel+1, cs =>
    if stagePolynomial u (cs.headD []) = 0 then
      let out := strip u fuel cs.tail
      (out.1+1, out.2)
    else (0, cs)

@[simp] theorem eval_head (u : Fin 15 → ℝ) (cs : BivariateCode n) :
    stagePolynomial u (cs.headD []) = (bivariatePolynomial u cs).coeff 0 := by
  cases cs with
  | nil => simp [stagePolynomial]
  | cons c cs => simp [eval_cons, Polynomial.coeff_X_mul]

@[simp] theorem eval_tail (u : Fin 15 → ℝ) (cs : BivariateCode n) :
    bivariatePolynomial u cs.tail = (bivariatePolynomial u cs).divX := by
  cases cs with
  | nil => simp
  | cons c cs =>
    simp only [List.tail_cons, eval_cons, Polynomial.divX_add, Polynomial.divX_C, zero_add]
    ext i
    simp [Polynomial.coeff_divX, Polynomial.coeff_X_mul]

@[simp] theorem eval_strip (u : Fin 15 → ℝ) (fuel : Nat) (cs : BivariateCode n) :
    bivariatePolynomial u (strip u fuel cs).2 =
      (stripInitial fuel (bivariatePolynomial u cs)).2 := by
  induction fuel generalizing cs with
  | zero => rfl
  | succ fuel ih =>
    simp only [strip, stripInitial, eval_head]
    split_ifs with h
    · simpa only [ih, eval_tail]
    · rfl

def normalize (u : Fin 15 → ℝ) (cs : BivariateCode n) : List (CoefficientCode n) :=
  ((strip u ((bivariatePolynomial u cs).natDegree+1) cs).2).headD []

@[simp] theorem eval_normalize (u : Fin 15 → ℝ) (cs : BivariateCode n) :
    stagePolynomial u (normalize u cs) =
      (normalizeInitial (bivariatePolynomial u cs)).2.coeff 0 := by
  rw [normalize, eval_head, eval_strip]
  rfl
end BivariateCode

end W3.FiniteInput
