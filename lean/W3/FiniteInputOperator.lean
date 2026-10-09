import W3.FiniteInputParameters
import W3.OperatorFieldCandidates

/-! Explicit coefficient/projector/inverse/reconstruction programs. The supplied
codes are retained through every scalar and matrix operation, including p=0. -/
noncomputable section
namespace W3.FiniteInput
open W3.Elimination W3.Weighted W3.OperatorField W3.TransferOperator
open W3.StrataTransfer W3.RealModel W3.Infinitesimal
variable {n : Nat}

def inverseParameterCode (k : Fin 15 → CoefficientCode n) : Fin 15 → CoefficientCode n :=
  let a := parameterAdjCode k
  let d := parameterDetCode k
  ![a 0/d,a 1/d,a 2/d,a 3/d,a 4/d,a 5/d,
    k 6/parameterDelta12Code k,k 7/parameterDelta13Code k,k 8/parameterDelta23Code k,
    -k 9/parameterDelta12Code k,-k 10/parameterDelta12Code k,
    -k 11/parameterDelta13Code k,-k 12/parameterDelta13Code k,
    -k 13/parameterDelta23Code k,-k 14/parameterDelta23Code k]

def identityCode : Fin 9 → Code n := ![1,1,1,0,0,0,0,0,0]

def projectorCode (z : Fin 6 → Code n) : Fin 9 → Code n :=
  ![Code.sq (z 0)+Code.sq (z 1),Code.sq (z 2)+Code.sq (z 3),Code.sq (z 4)+Code.sq (z 5),
    z 0*z 2+z 1*z 3,z 1*z 2-z 0*z 3,
    z 0*z 4+z 1*z 5,z 1*z 4-z 0*z 5,
    z 2*z 4+z 3*z 5,z 3*z 4-z 2*z 5]

def operatorCode (k : Fin 15 → Code n) (y : Fin 9 → Code n) : Fin 9 → Code n :=
  ![k 0*y 0+k 3*y 1+k 4*y 2,k 3*y 0+k 1*y 1+k 5*y 2,k 4*y 0+k 5*y 1+k 2*y 2,
    (k 6+k 9)*y 3-k 10*y 4,(k 6-k 9)*y 4-k 10*y 3,
    (k 7+k 11)*y 5-k 12*y 6,(k 7-k 11)*y 6-k 12*y 5,
    (k 8+k 13)*y 7-k 14*y 8,(k 8-k 13)*y 8-k 14*y 7]

def inverseCode (k : Fin 15 → CoefficientCode n) (y : Fin 9 → Code n) : Fin 9 → Code n :=
  operatorCode (fun i => .coefficient (inverseParameterCode k i)) y

def pairCode (y w : Fin 9 → Code n) : Code n :=
  y 0*w 0+y 1*w 1+y 2*w 2+2*(y 3*w 3+y 4*w 4+y 5*w 5+y 6*w 6+y 7*w 7+y 8*w 8)

def purityCode (y : Fin 9 → Code n) : Code n :=
  Code.sq (y 0)+Code.sq (y 1)+Code.sq (y 2)+
    2*(Code.sq (y 3)+Code.sq (y 4)+Code.sq (y 5)+Code.sq (y 6)+Code.sq (y 7)+Code.sq (y 8))

def energyCode (k : Fin 15 → Code n) (y : Fin 9 → Code n) : Code n :=
  pairCode y (operatorCode k y)/2

def dualBetaCode (k : Fin 15 → CoefficientCode n) : Code n :=
  pairCode identityCode (inverseCode k identityCode)
def dualACode (k : Fin 15 → CoefficientCode n) (z : Fin 6 → Code n) : Code n :=
  pairCode (projectorCode z) (inverseCode k identityCode)
def dualPCode (k : Fin 15 → CoefficientCode n) (z : Fin 6 → Code n) : Code n :=
  pairCode (projectorCode z) (inverseCode k (projectorCode z))
def dualDenCode (k : Fin 15 → CoefficientCode n) (z : Fin 6 → Code n) : Code n :=
  dualBetaCode k*dualPCode k z-Code.sq (dualACode k z)
def dualCoordinatesCode (k : Fin 15 → CoefficientCode n) (z : Fin 6 → Code n) : Fin 9 → Code n :=
  fun i => (dualPCode k z/dualDenCode k z)*inverseCode k identityCode i-
    (dualACode k z/dualDenCode k z)*inverseCode k (projectorCode z) i
def dualPurityCode (k : Fin 15 → CoefficientCode n) (z : Fin 6 → Code n) : Code n :=
  purityCode (dualCoordinatesCode k z)
def dualEnergyCode (k : Fin 15 → CoefficientCode n) (z : Fin 6 → Code n) : Code n :=
  dualPCode k z/(2*dualDenCode k z)

section Evaluate
variable {F K : Type*} [Field F] [CharZero F] [DecidableEq F]
    [Field K] [Algebra F K] [LinearOrder K] [IsStrictOrderedRing K]
variable (input : Fin 15 → F) (epsilon : Fin n → F) (O : RealRootEnumeration K)

def runCodes {m : Nat} (y : Fin m → Code n) : Fin m → K :=
  fun i => (y i |>.run input epsilon O).value

def runParameters (k : Fin 15 → CoefficientCode n) : Fin 15 → K :=
  fun i => algebraMap F K ((k i).eval input epsilon)

@[simp] theorem inverseParameterCode_run (k : Fin 15 → CoefficientCode n) :
    runParameters (K := K) input epsilon (inverseParameterCode k) =
      inverseParameters (runParameters (K := K) input epsilon k) := by
  funext i
  fin_cases i <;> simp [runParameters,inverseParameterCode,inverseParameters,
    parameterAdjCode,parameterDetCode,parameterDelta12Code,parameterDelta13Code,
    parameterDelta23Code,originalAdj,originalMatrixDet,originalDelta12,
    originalDelta13,originalDelta23,map_div₀,map_ofNat,CoefficientCode.eval]

@[simp] theorem identityCode_run :
    runCodes input epsilon O (identityCode : Fin 9 → Code n) = hermitianIdentity := by
  funext i
  fin_cases i <;> simp [runCodes,identityCode,hermitianIdentity]

@[simp] theorem projectorCode_run (z : Fin 6 → Code n) :
    runCodes input epsilon O (projectorCode z) = hermitianProjector (runCodes input epsilon O z) := by
  funext i
  fin_cases i <;> simp [runCodes,projectorCode,hermitianProjector,projectorRe,projectorIm,zRe,zIm]

@[simp] theorem operatorCode_run (k : Fin 15 → Code n) (y : Fin 9 → Code n) :
    runCodes input epsilon O (operatorCode k y) =
      hermitianOperator (runCodes input epsilon O k) (runCodes input epsilon O y) := by
  funext i
  fin_cases i <;> simp [runCodes,operatorCode,hermitianOperator]

@[simp] theorem liftParameters_run (k : Fin 15 → CoefficientCode n) :
    runCodes input epsilon O (fun i => Code.coefficient (k i)) = runParameters (K := K) input epsilon k := rfl

@[simp] theorem inverseCode_run (k : Fin 15 → CoefficientCode n) (y : Fin 9 → Code n) :
    runCodes input epsilon O (inverseCode k y) =
      hermitianInverse (runParameters (K := K) input epsilon k) (runCodes input epsilon O y) := by
  simp only [inverseCode,operatorCode_run,liftParameters_run,inverseParameterCode_run,hermitianInverse]

@[simp] theorem pairCode_run (y w : Fin 9 → Code n) :
    (pairCode y w |>.run input epsilon O).value =
      hermitianPair (runCodes input epsilon O y) (runCodes input epsilon O w) := by
  simp [pairCode,hermitianPair,runCodes]

@[simp] theorem purityCode_run (y : Fin 9 → Code n) :
    (purityCode y |>.run input epsilon O).value = hermitianPurity (runCodes input epsilon O y) := by
  simp [purityCode,hermitianPurity,runCodes]

@[simp] theorem energyCode_run (k : Fin 15 → Code n) (y : Fin 9 → Code n) :
    (energyCode k y |>.run input epsilon O).value =
      hermitianEnergy (runCodes input epsilon O k) (runCodes input epsilon O y)/2 := by
  simp [energyCode,hermitianEnergy_eq_pair]

@[simp] theorem dualBetaCode_run (k : Fin 15 → CoefficientCode n) :
    (dualBetaCode k |>.run input epsilon O).value = dualBeta (runParameters (K := K) input epsilon k) := by
  simp [dualBetaCode,dualBeta]
@[simp] theorem dualACode_run (k : Fin 15 → CoefficientCode n) (z : Fin 6 → Code n) :
    (dualACode k z |>.run input epsilon O).value =
      dualA (runParameters (K := K) input epsilon k) (runCodes input epsilon O z) := by
  simp [dualACode,dualA]
@[simp] theorem dualPCode_run (k : Fin 15 → CoefficientCode n) (z : Fin 6 → Code n) :
    (dualPCode k z |>.run input epsilon O).value =
      dualP (runParameters (K := K) input epsilon k) (runCodes input epsilon O z) := by
  simp [dualPCode,dualP]
@[simp] theorem dualDenCode_run (k : Fin 15 → CoefficientCode n) (z : Fin 6 → Code n) :
    (dualDenCode k z |>.run input epsilon O).value =
      dualDen (runParameters (K := K) input epsilon k) (runCodes input epsilon O z) := by
  simp [dualDenCode,dualDen,denominator]
@[simp] theorem run_mul_code (a b : Code n) :
    ((a*b).run input epsilon O).value =
      (a.run input epsilon O).value * (b.run input epsilon O).value := rfl

@[simp] theorem inverseCode_run_apply (k : Fin 15 → CoefficientCode n)
    (y : Fin 9 → Code n) (i : Fin 9) :
    ((inverseCode k y i).run input epsilon O).value =
      hermitianInverse (runParameters (K := K) input epsilon k) (runCodes input epsilon O y) i :=
  congrFun (inverseCode_run input epsilon O k y) i

@[simp] theorem dualCoordinatesCode_run (k : Fin 15 → CoefficientCode n) (z : Fin 6 → Code n) :
    runCodes input epsilon O (dualCoordinatesCode k z) =
      dualCoordinates (runParameters (K := K) input epsilon k) (runCodes input epsilon O z) := by
  funext i
  change ((dualCoordinatesCode k z i).run input epsilon O).value = _
  simp only [dualCoordinatesCode,run_sub,run_mul_code,run_div,dualPCode_run,
    dualDenCode_run,dualACode_run,inverseCode_run_apply,identityCode_run,projectorCode_run]
  rfl
@[simp] theorem dualPurityCode_run (k : Fin 15 → CoefficientCode n) (z : Fin 6 → Code n) :
    (dualPurityCode k z |>.run input epsilon O).value =
      dualPurity (runParameters (K := K) input epsilon k) (runCodes input epsilon O z) := by
  simp [dualPurityCode,dualPurity]
@[simp] theorem dualEnergyCode_run (k : Fin 15 → CoefficientCode n) (z : Fin 6 → Code n) :
    (dualEnergyCode k z |>.run input epsilon O).value =
      dualEnergy (runParameters (K := K) input epsilon k) (runCodes input epsilon O z) := by
  simp [dualEnergyCode,dualEnergy]
end Evaluate
end W3.FiniteInput
