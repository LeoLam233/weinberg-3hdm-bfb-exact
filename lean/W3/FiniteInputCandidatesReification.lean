import W3.FiniteInputSyntax
import W3.EliminationPolynomial

/-! Structural compilation of rational multivariate polynomials into finite-input
coefficient syntax. The polynomial is a fixed symbolic expression, never an
ambient field element, and only rational coefficients become literal leaves. -/
noncomputable section
namespace W3.FiniteInput
open Polynomial W3.Elimination
namespace CoefficientCode
variable {n : Nat}

def sum : List (CoefficientCode n) → CoefficientCode n
  | [] => .rational 0
  | a :: as => .add a (sum as)

def product : List (CoefficientCode n) → CoefficientCode n
  | [] => .rational 1
  | a :: as => .mul a (product as)

def power (a : CoefficientCode n) : Nat → CoefficientCode n
  | 0 => .rational 1
  | k+1 => .mul (power a k) a

def compilePolynomial (vars : Fin 15 → CoefficientCode n)
    (p : MvPolynomial (Fin 15) ℚ) : CoefficientCode n :=
  sum (p.support.toList.map fun d =>
    .mul (.rational (p.coeff d))
      (product (d.support.toList.map fun i => power (vars i) (d i))))

variable {F : Type*} [Field F] [CharZero F]
variable (input : Fin 15 → F) (epsilon : Fin n → F)

@[simp] theorem eval_sum (xs : List (CoefficientCode n)) :
    (sum xs).eval input epsilon = (xs.map (fun a => a.eval input epsilon)).sum := by
  induction xs with
  | nil => simp [sum, eval]
  | cons a as ih => simp [sum, eval, ih]

@[simp] theorem eval_product (xs : List (CoefficientCode n)) :
    (product xs).eval input epsilon = (xs.map (fun a => a.eval input epsilon)).prod := by
  induction xs with
  | nil => simp [product, eval]
  | cons a as ih => simp [product, eval, ih]

@[simp] theorem eval_power (a : CoefficientCode n) (k : Nat) :
    (power a k).eval input epsilon = (a.eval input epsilon)^k := by
  induction k with
  | zero => simp [power, eval]
  | succ k ih => simp [power, eval, ih, pow_succ]

@[simp] theorem eval_compilePolynomial (vars : Fin 15 → CoefficientCode n)
    (p : MvPolynomial (Fin 15) ℚ) :
    (compilePolynomial vars p).eval input epsilon =
      MvPolynomial.eval₂ (Rat.castHom F) (fun i => (vars i).eval input epsilon) p := by
  classical
  simp only [compilePolynomial, eval_sum, List.map_map, Function.comp_def,
    eval, eval_product, eval_power, MvPolynomial.eval₂_eq]
  simp only [← List.sum_toFinset _ p.support.nodup_toList, Finset.toList_toFinset,
    ← List.prod_toFinset _ (Finsupp.support _).nodup_toList]
  simp
end CoefficientCode
end W3.FiniteInput
