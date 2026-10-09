import W3.FiniteInputSyntax
import Mathlib.Algebra.MvPolynomial.Eval

/-! Finite arithmetic syntax is a coefficient language for a free commutative
ring. Every free-ring element is lowered by its literal finite monomial sum.
No generated-field membership witness or choice of an expression is used. -/
noncomputable section
namespace W3.FiniteInput
open Polynomial
namespace CoefficientCode
variable {n : Nat}
def tracePow (c : CoefficientCode n) : Nat → CoefficientCode n
  | 0 => .rational 1
  | k+1 => .mul (tracePow c k) c

def traceSum : List (CoefficientCode n) → CoefficientCode n
  | [] => .rational 0
  | a :: as => .add a (traceSum as)

def traceProd : List (CoefficientCode n) → CoefficientCode n
  | [] => .rational 1
  | a :: as => .mul a (traceProd as)

variable {F : Type*} [Field F] [CharZero F]
variable (input : Fin 15 → F) (epsilon : Fin n → F)
@[simp] theorem eval_tracePow (c : CoefficientCode n) (k : Nat) :
    (c.tracePow k).eval input epsilon = (c.eval input epsilon)^k := by
  induction k with
  | zero => simp [tracePow, eval]
  | succ k ih => simp [tracePow, eval, ih, pow_succ]

@[simp] theorem eval_traceSum (cs : List (CoefficientCode n)) :
    (traceSum cs).eval input epsilon = (cs.map (·.eval input epsilon)).sum := by
  induction cs with
  | nil => simp [traceSum, eval]
  | cons c cs ih => simp [traceSum, eval, ih]

@[simp] theorem eval_traceProd (cs : List (CoefficientCode n)) :
    (traceProd cs).eval input epsilon = (cs.map (·.eval input epsilon)).prod := by
  induction cs with
  | nil => simp [traceProd, eval]
  | cons c cs ih => simp [traceProd, eval, ih]
end CoefficientCode

abbrev FreeCoefficientRing (n : Nat) := MvPolynomial (CoefficientCode n) ℚ
theorem polynomialOfList_coeff {R : Type*} [Semiring R] (cs : List R) (i : Nat) :
    (polynomialOfList cs).coeff i = cs[i]?.getD 0 := by
  induction cs generalizing i with
  | nil => simp [polynomialOfList]
  | cons c cs ih =>
    cases i with
    | zero => simp [polynomialOfList]
    | succ i => simp [polynomialOfList, coeff_X_mul, ih]

namespace FreeCoefficientRing
variable {n : Nat}

def lower (p : FreeCoefficientRing n) : CoefficientCode n :=
  CoefficientCode.traceSum (p.support.toList.map fun d =>
    .mul (.rational (p.coeff d))
      (CoefficientCode.traceProd (d.support.toList.map fun c => c.tracePow (d c))))

def specialize {F : Type*} [Field F] [CharZero F]
    (input : Fin 15 → F) (epsilon : Fin n → F) : FreeCoefficientRing n →+* F :=
  MvPolynomial.eval₂Hom (algebraMap ℚ F) (fun c => c.eval input epsilon)

variable {F : Type*} [Field F] [CharZero F]
variable (input : Fin 15 → F) (epsilon : Fin n → F)
@[simp] theorem specialize_X (c : CoefficientCode n) :
    specialize input epsilon (MvPolynomial.X c) = c.eval input epsilon := by
  simp [specialize]

@[simp] theorem lower_correct (p : FreeCoefficientRing n) :
    p.lower.eval input epsilon = specialize input epsilon p := by
  classical
  simp only [lower, CoefficientCode.eval_traceSum, List.map_map,
    Function.comp_def, CoefficientCode.eval, CoefficientCode.eval_traceProd,
    CoefficientCode.eval_tracePow]
  simp only [specialize, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
  simp only [Finset.sum_map_toList, Finset.prod_map_toList]
  rfl

/-- Encode the complete finite coefficient array, retaining all zero slots. -/
def polynomialCodes (p : (FreeCoefficientRing n)[X]) : List (CoefficientCode n) :=
  List.ofFn (fun i : Fin (p.natDegree+1) => lower (p.coeff i))

@[simp] theorem polynomialCodes_correct (p : (FreeCoefficientRing n)[X]) :
    coefficientPolynomial input epsilon (polynomialCodes p) =
      p.map (specialize input epsilon) := by
  classical
  ext i
  simp only [coefficientPolynomial, polynomialOfList_coeff, polynomialCodes,
    List.map_ofFn, Polynomial.coeff_map]
  by_cases hi : i < p.natDegree+1
  · rw [List.getElem?_ofFn]
    simp only [dif_pos hi, Option.getD_some, Function.comp_def, lower_correct]
  · have hz : p.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [List.getElem?_ofFn]
    simp only [dif_neg hi, Option.getD_none, hz, map_zero]

end FreeCoefficientRing
end W3.FiniteInput
