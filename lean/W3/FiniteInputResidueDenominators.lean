import W3.FiniteInputSyntax
import W3.InfinitesimalRationalTower

/-! # Structural numerator/denominator extraction from finite input codes
The rational-expression syntax is decoded relative to its newest epsilon. Every
coefficient of both resulting polynomials remains an explicit smaller-stage
input code. Inversion branches only on exact equality of its coded numerator. -/
noncomputable section
namespace W3.FiniteInput
open Polynomial W3.Infinitesimal
set_option backward.isDefEq.respectTransparency false

namespace PolynomialCode
variable {n : Nat}

def add : List (CoefficientCode n) → List (CoefficientCode n) → List (CoefficientCode n)
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => .add a b :: add as bs

def scale (a : CoefficientCode n) (bs : List (CoefficientCode n)) : List (CoefficientCode n) :=
  bs.map (.mul a)

def mul : List (CoefficientCode n) → List (CoefficientCode n) → List (CoefficientCode n)
  | [], _ => []
  | a :: as, bs => add (scale a bs) (.rational 0 :: mul as bs)

def neg (as : List (CoefficientCode n)) : List (CoefficientCode n) := as.map .neg

variable {F : Type*} [Field F] [CharZero F]

@[simp] theorem eval_nil (input : Fin 15 → F) (epsilon : Fin n → F) :
    coefficientPolynomial input epsilon [] = 0 := rfl

@[simp] theorem eval_cons (input : Fin 15 → F) (epsilon : Fin n → F)
    (a : CoefficientCode n) (as : List (CoefficientCode n)) :
    coefficientPolynomial input epsilon (a :: as) =
      C (a.eval input epsilon) + X * coefficientPolynomial input epsilon as := rfl

@[simp] theorem eval_add (input : Fin 15 → F) (epsilon : Fin n → F)
    (as bs : List (CoefficientCode n)) :
    coefficientPolynomial input epsilon (add as bs) =
      coefficientPolynomial input epsilon as + coefficientPolynomial input epsilon bs := by
  induction as generalizing bs with
  | nil => simp [add]
  | cons a as ih =>
    cases bs with
    | nil => simp [add]
    | cons b bs =>
      simp only [add, eval_cons, CoefficientCode.eval, map_add, ih]
      ring

@[simp] theorem eval_scale (input : Fin 15 → F) (epsilon : Fin n → F)
    (a : CoefficientCode n) (bs : List (CoefficientCode n)) :
    coefficientPolynomial input epsilon (scale a bs) =
      C (a.eval input epsilon) * coefficientPolynomial input epsilon bs := by
  induction bs with
  | nil => simp [scale]
  | cons b bs ih =>
    change coefficientPolynomial input epsilon (.mul a b :: scale a bs) = _
    simp only [eval_cons, CoefficientCode.eval, map_mul, ih]
    ring

@[simp] theorem eval_mul (input : Fin 15 → F) (epsilon : Fin n → F)
    (as bs : List (CoefficientCode n)) :
    coefficientPolynomial input epsilon (mul as bs) =
      coefficientPolynomial input epsilon as * coefficientPolynomial input epsilon bs := by
  induction as with
  | nil => simp [mul]
  | cons a as ih =>
    simp only [mul, eval_add, eval_scale, eval_cons, CoefficientCode.eval, Rat.cast_zero,
      map_zero, zero_add, ih]
    ring

@[simp] theorem eval_neg (input : Fin 15 → F) (epsilon : Fin n → F)
    (as : List (CoefficientCode n)) :
    coefficientPolynomial input epsilon (neg as) =
      -coefficientPolynomial input epsilon as := by
  induction as with
  | nil => simp [neg]
  | cons a as ih =>
    change coefficientPolynomial input epsilon (.neg a :: neg as) = _
    simp only [eval_cons, CoefficientCode.eval, map_neg, ih]
    ring
end PolynomialCode

instance rationalTowerCharZero (n : Nat) : CharZero (RationalTower n) :=
  (RingHom.charZero_iff (rationalTowerHom n).injective).mpr inferInstance

/-- The fifteen real leaves embedded in the n-th rational presentation. -/
def stageInput (u : Fin 15 → ℝ) (n : Nat) : Fin 15 → RationalTower n :=
  fun i => rationalBase n (u i)

def stagePolynomial (u : Fin 15 → ℝ) {n : Nat} (cs : List (CoefficientCode n)) :
    (RationalTower n)[X] := coefficientPolynomial (stageInput u n) (rationalCoordinates n) cs

structure FractionCode (n : Nat) where
  numerator : List (CoefficientCode n)
  denominator : List (CoefficientCode n)

namespace FractionCode
variable {n : Nat} [DecidableEq (RationalTower n)]

def constant (a : CoefficientCode n) : FractionCode n := ⟨[a], [.rational 1]⟩
def indeterminate : FractionCode n := ⟨[.rational 0, .rational 1], [.rational 1]⟩
def add (a b : FractionCode n) : FractionCode n :=
  ⟨PolynomialCode.add (PolynomialCode.mul a.numerator b.denominator)
    (PolynomialCode.mul b.numerator a.denominator),
    PolynomialCode.mul a.denominator b.denominator⟩
def mul (a b : FractionCode n) : FractionCode n :=
  ⟨PolynomialCode.mul a.numerator b.numerator,
    PolynomialCode.mul a.denominator b.denominator⟩
def neg (a : FractionCode n) : FractionCode n :=
  ⟨PolynomialCode.neg a.numerator, a.denominator⟩
def inv (u : Fin 15 → ℝ) (a : FractionCode n) : FractionCode n := by
  exact if stagePolynomial u a.numerator = 0 then constant (.rational 0)
    else ⟨a.denominator, a.numerator⟩

/-- Exact interpretation into the next rational-function field. -/
def value (u : Fin 15 → ℝ) (a : FractionCode n) : RationalTower (n+1) :=
  algebraMap (RationalTower n)[X] (RatFunc (RationalTower n)) (stagePolynomial u a.numerator) /
    algebraMap (RationalTower n)[X] (RatFunc (RationalTower n)) (stagePolynomial u a.denominator)
end FractionCode

/-- The newest epsilon is X; all older epsilons and real inputs become explicit
constant-polynomial coefficient codes. -/
def CoefficientCode.fraction (u : Fin 15 → ℝ) {n : Nat} [DecidableEq (RationalTower n)] :
    CoefficientCode (n+1) → FractionCode n
  | .rational q => .constant (.rational q)
  | .input i => .constant (.input i)
  | .epsilon i => Fin.cases FractionCode.indeterminate (fun j => .constant (.epsilon j)) i
  | .add a b => (a.fraction u).add (b.fraction u)
  | .mul a b => (a.fraction u).mul (b.fraction u)
  | .neg a => (a.fraction u).neg
  | .inv a => (a.fraction u).inv u

namespace FractionCode
variable {n : Nat} [DecidableEq (RationalTower n)]

@[simp] theorem stagePolynomial_singleton (u : Fin 15 → ℝ) (a : CoefficientCode n) :
    stagePolynomial u [a] = C (a.eval (stageInput u n) (rationalCoordinates n)) := by
  simp [stagePolynomial]

@[simp] theorem constant_denominator (u : Fin 15 → ℝ) (a : CoefficientCode n) :
    stagePolynomial u (constant a).denominator = 1 := by
  simp [constant, stagePolynomial, CoefficientCode.eval]

@[simp] theorem constant_value (u : Fin 15 → ℝ) (a : CoefficientCode n) :
    (constant a).value u = rationalStep n (a.eval (stageInput u n) (rationalCoordinates n)) := by
  simp [value, constant, rationalStep, stagePolynomial, CoefficientCode.eval]
  rfl

@[simp] theorem indeterminate_denominator (u : Fin 15 → ℝ) :
    stagePolynomial u (indeterminate (n := n)).denominator = 1 := by
  simp [indeterminate, stagePolynomial, CoefficientCode.eval]

@[simp] theorem indeterminate_value (u : Fin 15 → ℝ) :
    (indeterminate (n := n)).value u = rationalVariable n := by
  simp [value, indeterminate, stagePolynomial, CoefficientCode.eval, rationalVariable]

@[simp] theorem add_denominator (u : Fin 15 → ℝ) (a b : FractionCode n) :
    stagePolynomial u (a.add b).denominator =
      stagePolynomial u a.denominator * stagePolynomial u b.denominator := by
  simp [add, stagePolynomial]

@[simp] theorem mul_denominator (u : Fin 15 → ℝ) (a b : FractionCode n) :
    stagePolynomial u (a.mul b).denominator =
      stagePolynomial u a.denominator * stagePolynomial u b.denominator := by
  simp [mul, stagePolynomial]

@[simp] theorem neg_denominator (u : Fin 15 → ℝ) (a : FractionCode n) :
    stagePolynomial u a.neg.denominator = stagePolynomial u a.denominator := rfl

theorem add_value (u : Fin 15 → ℝ) (a b : FractionCode n)
    (ha : stagePolynomial u a.denominator ≠ 0)
    (hb : stagePolynomial u b.denominator ≠ 0) :
    (a.add b).value u = a.value u + b.value u := by
  have ha' := RatFunc.algebraMap_ne_zero ha
  have hb' := RatFunc.algebraMap_ne_zero hb
  simp only [value, add, stagePolynomial, PolynomialCode.eval_add,
    PolynomialCode.eval_mul, map_add, map_mul]
  dsimp only [stagePolynomial] at ha' hb'
  field_simp [ha', hb']

theorem mul_value (u : Fin 15 → ℝ) (a b : FractionCode n) :
    (a.mul b).value u = a.value u * b.value u := by
  simp only [value, mul, stagePolynomial, PolynomialCode.eval_mul, map_mul]
  exact mul_div_mul_comm _ _ _ _

theorem neg_value (u : Fin 15 → ℝ) (a : FractionCode n) :
    a.neg.value u = -a.value u := by
  simp [value, neg, stagePolynomial, neg_div]

theorem inv_denominator (u : Fin 15 → ℝ) (a : FractionCode n)
    (ha : stagePolynomial u a.denominator ≠ 0) :
    stagePolynomial u (a.inv u).denominator ≠ 0 := by
  classical
  unfold inv
  split_ifs with h
  · simp
  · exact h

theorem inv_value (u : Fin 15 → ℝ) (a : FractionCode n) :
    (a.inv u).value u = (a.value u)⁻¹ := by
  classical
  unfold inv
  split_ifs with h
  · simp only [constant_value, CoefficientCode.eval, Rat.cast_zero, map_zero]
    simp [value, h]
  · simp [value, inv_div]
end FractionCode

/-- Every rational-expression node has an actual finite numerator/denominator
program over the previous stage, with a nonzero interpreted denominator. -/
theorem CoefficientCode.fraction_spec (u : Fin 15 → ℝ) {n : Nat} [DecidableEq (RationalTower n)]
    (c : CoefficientCode (n+1)) :
    stagePolynomial u (c.fraction u).denominator ≠ 0 ∧
    (c.fraction u).value u = c.eval (stageInput u (n+1)) (rationalCoordinates (n+1)) := by
  induction c with
  | rational q =>
    simp only [fraction, FractionCode.constant_denominator, ne_eq, one_ne_zero, not_false_eq_true,
      FractionCode.constant_value, CoefficientCode.eval, map_ratCast, and_self]
  | input i =>
    simp only [fraction, FractionCode.constant_denominator, ne_eq, one_ne_zero, not_false_eq_true,
      FractionCode.constant_value, CoefficientCode.eval, true_and]
    rfl
  | epsilon i =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [fraction, CoefficientCode.eval, rationalCoordinates]
    · simp [fraction, CoefficientCode.eval, rationalCoordinates]
  | add a b ha hb =>
    refine ⟨?_, ?_⟩
    · simpa only [fraction, FractionCode.add_denominator] using mul_ne_zero ha.1 hb.1
    · simpa only [fraction, CoefficientCode.eval, ha.2, hb.2] using
        FractionCode.add_value u (a.fraction u) (b.fraction u) ha.1 hb.1
  | mul a b ha hb =>
    refine ⟨?_, ?_⟩
    · simpa only [fraction, FractionCode.mul_denominator] using mul_ne_zero ha.1 hb.1
    · simpa only [fraction, CoefficientCode.eval, ha.2, hb.2] using
        FractionCode.mul_value u (a.fraction u) (b.fraction u)
  | neg a ha =>
    refine ⟨ha.1, ?_⟩
    simpa only [fraction, CoefficientCode.eval, ha.2] using
      FractionCode.neg_value u (a.fraction u)
  | inv a ha =>
    refine ⟨FractionCode.inv_denominator u (a.fraction u) ha.1, ?_⟩
    simpa only [fraction, CoefficientCode.eval, ha.2] using
      FractionCode.inv_value u (a.fraction u)

#print axioms CoefficientCode.fraction_spec
end W3.FiniteInput
