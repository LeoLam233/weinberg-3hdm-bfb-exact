import W3.FiniteInputCandidatesReification
import W3.FiniteInputCandidatesArithmetic

/-! Fixed universal coefficient programs for the sextic and its linear recovery. -/
noncomputable section
namespace W3.FiniteInput
open Polynomial W3.Elimination W3.Weighted W3.Infinitesimal

variable {n : Nat}
def polynomialCodes (w : WeightedData (CoefficientCode n))
    (p : Polynomial (MvPolynomial (Fin 15) ℚ)) : List (CoefficientCode n) :=
  List.ofFn (fun i : Fin (p.natDegree+1) =>
    CoefficientCode.compilePolynomial (weightedCoordinates w) (p.coeff i))

def sexticCodes (w : WeightedData (CoefficientCode n)) : List (CoefficientCode n) :=
  polynomialCodes w (phaseSextic (weightedP universalWeighted) (weightedQ universalWeighted))
def linearOneCodes (w : WeightedData (CoefficientCode n)) : List (CoefficientCode n) :=
  polynomialCodes w (phaseLinearOne (weightedP universalWeighted) (weightedQ universalWeighted))
def linearZeroCodes (w : WeightedData (CoefficientCode n)) : List (CoefficientCode n) :=
  polynomialCodes w (phaseLinearZero (weightedP universalWeighted) (weightedQ universalWeighted))

def polynomialAtCode (cs : List (CoefficientCode n)) (t : Code n) : Code n :=
  match cs with
  | [] => 0
  | a :: as => .coefficient a + t * polynomialAtCode as t

def recoveredCode (w : WeightedData (CoefficientCode n)) (t : Code n) : Code n :=
  -(polynomialAtCode (linearZeroCodes w) t) / polynomialAtCode (linearOneCodes w) t

section Evaluate
variable {F K : Type*} [Field F] [CharZero F] [DecidableEq F]
    [Field K] [Algebra F K] [LinearOrder K] [IsStrictOrderedRing K]
variable (input : Fin 15 → F) (epsilon : Fin n → F) (O : RealRootEnumeration K)

theorem candidatePolynomialOfList_coeff (xs : List F) (i : Nat) :
    (polynomialOfList xs).coeff i = (xs[i]?).getD 0 := by
  induction xs generalizing i with
  | nil => simp [polynomialOfList]
  | cons a as ih =>
    cases i with
    | zero => simp [polynomialOfList,coeff_add]
    | succ i => simp [polynomialOfList,coeff_add,coeff_X_mul,ih]

theorem polynomialOfList_coefficients (p : F[X]) (m : Nat) (h : p.natDegree < m) :
    polynomialOfList (List.ofFn (fun i : Fin m => p.coeff i)) = p := by
  ext i
  rw [candidatePolynomialOfList_coeff]
  by_cases hi : i < m
  · simp [List.getElem?_ofFn,hi]
  · have hp : p.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le h (Nat.le_of_not_gt hi))
    simp [List.getElem?_ofFn,hi,hp]

theorem eval_coordinates (w : WeightedData (CoefficientCode n)) :
    (fun i => (weightedCoordinates w i).eval input epsilon) =
      weightedCoordinates (evalWeighted input epsilon w) := by
  funext i
  fin_cases i <;> rfl

theorem polynomialCodes_correct (w : WeightedData (CoefficientCode n))
    (p : Polynomial (MvPolynomial (Fin 15) ℚ)) :
    coefficientPolynomial input epsilon (polynomialCodes w p) =
      p.map (MvPolynomial.eval₂Hom (Rat.castHom F)
        (weightedCoordinates (evalWeighted input epsilon w))) := by
  unfold coefficientPolynomial polynomialCodes
  rw [List.map_ofFn]
  simp only [Function.comp_def,CoefficientCode.eval_compilePolynomial,eval_coordinates]
  let f := MvPolynomial.eval₂Hom (Rat.castHom F) (weightedCoordinates (evalWeighted input epsilon w))
  have hmap : (p.map f).natDegree < p.natDegree+1 :=
    lt_of_le_of_lt natDegree_map_le (Nat.lt_succ_self _)
  simpa only [coeff_map,f,MvPolynomial.coe_eval₂Hom] using polynomialOfList_coefficients (p.map f) (p.natDegree+1) hmap

@[simp] theorem sexticCodes_correct (w : WeightedData (CoefficientCode n)) :
    coefficientPolynomial input epsilon (sexticCodes w) =
      phaseSextic (weightedP (evalWeighted input epsilon w)) (weightedQ (evalWeighted input epsilon w)) := by
  rw [sexticCodes,polynomialCodes_correct]
  simp only [map_phaseSextic,map_weightedP,map_weightedQ,universalWeighted_eval]

@[simp] theorem linearOneCodes_correct (w : WeightedData (CoefficientCode n)) :
    coefficientPolynomial input epsilon (linearOneCodes w) =
      phaseLinearOne (weightedP (evalWeighted input epsilon w)) (weightedQ (evalWeighted input epsilon w)) := by
  rw [linearOneCodes,polynomialCodes_correct]
  simp only [map_phaseLinearOne,map_weightedP,map_weightedQ,universalWeighted_eval]

@[simp] theorem linearZeroCodes_correct (w : WeightedData (CoefficientCode n)) :
    coefficientPolynomial input epsilon (linearZeroCodes w) =
      phaseLinearZero (weightedP (evalWeighted input epsilon w)) (weightedQ (evalWeighted input epsilon w)) := by
  rw [linearZeroCodes,polynomialCodes_correct]
  simp only [map_phaseLinearZero,map_weightedP,map_weightedQ,universalWeighted_eval]

@[simp] theorem run_polynomialAt (cs : List (CoefficientCode n)) (t : Code n) :
    ((polynomialAtCode cs t).run input epsilon O).value =
      ((coefficientPolynomial input epsilon cs).map (algebraMap F K)).eval (t.run input epsilon O).value := by
  induction cs with
  | nil => simp [polynomialAtCode,coefficientPolynomial,polynomialOfList]
  | cons a as ih => simp [polynomialAtCode,coefficientPolynomial,polynomialOfList,ih]

@[simp] theorem run_recovered (w : WeightedData (CoefficientCode n)) (t : Code n) :
    ((recoveredCode w t).run input epsilon O).value =
      -(phaseLinearZero (weightedP (runWeighted input epsilon w))
        (weightedQ (runWeighted input epsilon w))).eval (t.run input epsilon O).value /
      (phaseLinearOne (weightedP (runWeighted input epsilon w))
        (weightedQ (runWeighted input epsilon w))).eval (t.run input epsilon O).value := by
  simp [recoveredCode,runWeighted]

end Evaluate
end W3.FiniteInput
