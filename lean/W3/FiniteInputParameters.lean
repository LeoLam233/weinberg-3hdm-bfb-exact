import W3.FiniteInputResidueDenominators
import W3.FiniteInputCoefficientArithmetic
import W3.FiniteInputCandidatesArithmetic
import W3.WeightedAlgebraicityActual

/-! Literal finite input programs for the actual deformation and both operator
coefficient lists. Only the supplied fifteen coefficients, rational numbers and
sixteen epsilon variables occur; no semantic scalar is inserted as a constant. -/
noncomputable section
namespace W3.FiniteInput
open W3.Elimination W3.Infinitesimal W3.Weighted
variable {n : Nat}

def primalParameterCode (x : Fin 15 → CoefficientCode n) : WeightedData (CoefficientCode n) :=
  ⟨x 0,x 1,x 2,x 3+x 6,x 4+x 7,x 5+x 8,
    x 9,x 10,x 11,x 12,x 13,x 14,1,1,1⟩

def parameterDetCode (x : Fin 15 → CoefficientCode n) : CoefficientCode n :=
  x 0*x 1*x 2+2*x 3*x 4*x 5-x 0*(x 5)^2-x 1*(x 4)^2-x 2*(x 3)^2

def parameterAdjCode (x : Fin 15 → CoefficientCode n) : Fin 6 → CoefficientCode n :=
  ![x 1*x 2-(x 5)^2,x 0*x 2-(x 4)^2,x 0*x 1-(x 3)^2,
    x 4*x 5-x 2*x 3,x 3*x 5-x 1*x 4,x 3*x 4-x 0*x 5]

def parameterDelta12Code (x : Fin 15 → CoefficientCode n) : CoefficientCode n :=
  (x 6)^2-(x 9)^2-(x 10)^2
def parameterDelta13Code (x : Fin 15 → CoefficientCode n) : CoefficientCode n :=
  (x 7)^2-(x 11)^2-(x 12)^2
def parameterDelta23Code (x : Fin 15 → CoefficientCode n) : CoefficientCode n :=
  (x 8)^2-(x 13)^2-(x 14)^2

def dualParameterCode (x : Fin 15 → CoefficientCode n) : WeightedData (CoefficientCode n) :=
  let a := parameterAdjCode x
  let d := parameterDetCode x
  let d12 := parameterDelta12Code x
  let d13 := parameterDelta13Code x
  let d23 := parameterDelta23Code x
  ⟨2*(a 0/d),2*(a 1/d),2*(a 2/d),
    2*(a 3/d+x 6/d12),2*(a 4/d+x 7/d13),2*(a 5/d+x 8/d23),
    -2*x 9/d12,-2*x 10/d12,-2*x 11/d13,-2*x 12/d13,-2*x 13/d23,-2*x 14/d23,
    (a 0+a 3+a 4)/d,(a 3+a 1+a 5)/d,(a 4+a 5+a 2)/d⟩

section Evaluate
variable {F : Type*} [Field F] [CharZero F]
variable (input : Fin 15 → F) (epsilon : Fin n → F)
variable (x : Fin 15 → CoefficientCode n)

@[simp] theorem primalParameterCode_eval :
    evalWeighted input epsilon (primalParameterCode x) =
      originalPrimal (fun i => (x i).eval input epsilon) := by
  simp [primalParameterCode,evalWeighted,originalPrimal,CoefficientCode.eval]

@[simp] theorem parameterDetCode_eval :
    (parameterDetCode x).eval input epsilon =
      originalMatrixDet (fun i => (x i).eval input epsilon) := by
  simp [parameterDetCode,originalMatrixDet,CoefficientCode.eval]

@[simp] theorem parameterAdjCode_eval (i : Fin 6) :
    (parameterAdjCode x i).eval input epsilon =
      originalAdj (fun j => (x j).eval input epsilon) i := by
  fin_cases i <;> simp [parameterAdjCode,originalAdj,CoefficientCode.eval]

@[simp] theorem dualParameterCode_eval :
    evalWeighted input epsilon (dualParameterCode x) =
      originalDual (fun i => (x i).eval input epsilon) := by
  simp [dualParameterCode,evalWeighted,originalDual,parameterDelta12Code,
    parameterDelta13Code,parameterDelta23Code,originalDelta12,originalDelta13,
    originalDelta23,CoefficientCode.eval]
end Evaluate

/-- Newest-first epsilon indices agree with the recursive residue tower. -/
def actualParameterCode (i : Fin 15) : CoefficientCode 16 :=
  .input i + (if i.val < 6 then 2 * .epsilon (0 : Fin 16).rev else 0) +
    .epsilon i.succ.rev

def originalInput (κ : Fin 15 → ℝ) : Fin 15 → RationalTower 16 :=
  fun i => rationalBase 16 (κ i)

@[simp] theorem actualParameterCode_eval (κ : Fin 15 → ℝ) (i : Fin 15) :
    (actualParameterCode i).eval (originalInput κ) (rationalCoordinates 16) =
      rationalActualParameters κ i := by
  unfold actualParameterCode rationalActualParameters originalInput rationalChronologicalEpsilon
  split_ifs <;> simp [CoefficientCode.eval]

def actualPrimalCode : WeightedData (CoefficientCode 16) := primalParameterCode actualParameterCode
def actualDualCode : WeightedData (CoefficientCode 16) := dualParameterCode actualParameterCode

@[simp] theorem actualPrimalCode_eval (κ : Fin 15 → ℝ) :
    evalWeighted (originalInput κ) (rationalCoordinates 16) actualPrimalCode =
      originalPrimal (rationalActualParameters κ) := by
  rw [actualPrimalCode,primalParameterCode_eval]
  simp only [actualParameterCode_eval]

@[simp] theorem actualDualCode_eval (κ : Fin 15 → ℝ) :
    evalWeighted (originalInput κ) (rationalCoordinates 16) actualDualCode =
      originalDual (rationalActualParameters κ) := by
  rw [actualDualCode,dualParameterCode_eval]
  simp only [actualParameterCode_eval]

@[simp] theorem actualPrimalCode_run (κ : Fin 15 → ℝ) :
    letI := rationalTowerAlgebra 16
    runWeighted (K := SixteenLevelField) (originalInput κ) (rationalCoordinates 16) actualPrimalCode =
      originalPrimal (actualParameters κ) := by
  letI := rationalTowerAlgebra 16
  change mapWeighted (rationalTowerHom 16)
    (evalWeighted (originalInput κ) (rationalCoordinates 16) actualPrimalCode) = _
  rw [actualPrimalCode_eval]
  exact actualPrimal_presentation κ

@[simp] theorem actualDualCode_run (κ : Fin 15 → ℝ) :
    letI := rationalTowerAlgebra 16
    runWeighted (K := SixteenLevelField) (originalInput κ) (rationalCoordinates 16) actualDualCode =
      originalDual (actualParameters κ) := by
  letI := rationalTowerAlgebra 16
  change mapWeighted (rationalTowerHom 16)
    (evalWeighted (originalInput κ) (rationalCoordinates 16) actualDualCode) = _
  rw [actualDualCode_eval]
  exact actualDual_presentation κ

#print axioms actualPrimalCode_run
#print axioms actualDualCode_run
end W3.FiniteInput
