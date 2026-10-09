import W3.TransferOperatorEnergy
import W3.EliminationDual
import W3.OperatorFieldLinear

/-! The actual inverse operator over every ordered field, in the source's nine
independent real Hermitian coordinates. -/
set_option maxHeartbeats 800000
noncomputable section
namespace W3.OperatorField
open W3.TransferOperator W3.Elimination W3.RealModel W3.StrataTransfer
open scoped BigOperators
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Original-format coefficients of the inverse real-linear operator. -/
def inverseParameters (k : Parameters K) : Parameters K :=
  let a := originalAdj k
  let d := originalMatrixDet k
  ![a 0/d,a 1/d,a 2/d,a 3/d,a 4/d,a 5/d,
    k 6/originalDelta12 k,k 7/originalDelta13 k,k 8/originalDelta23 k,
    -k 9/originalDelta12 k,-k 10/originalDelta12 k,
    -k 11/originalDelta13 k,-k 12/originalDelta13 k,
    -k 13/originalDelta23 k,-k 14/originalDelta23 k]

def hermitianInverse (k : Parameters K) : HermitianCoordinates K → HermitianCoordinates K :=
  hermitianOperator (inverseParameters k)

/-- Genuine two-sided inversion, requiring precisely the block denominators. -/
theorem hermitianInverse_left (k : Parameters K) (h : originalInverseDen k ≠ 0)
    (y : HermitianCoordinates K) : hermitianInverse k (hermitianOperator k y) = y := by
  obtain ⟨hd,h12,h13,h23⟩ := originalInverseDen_nonzero_factors k h
  funext i
  fin_cases i <;>
    simp [hermitianInverse,inverseParameters,hermitianOperator,originalAdj] <;>
    field_simp [hd,h12,h13,h23] <;>
    simp only [originalMatrixDet,originalDelta12,originalDelta13,originalDelta23] <;> ring

theorem hermitianInverse_right (k : Parameters K) (h : originalInverseDen k ≠ 0)
    (y : HermitianCoordinates K) : hermitianOperator k (hermitianInverse k y) = y := by
  obtain ⟨hd,h12,h13,h23⟩ := originalInverseDen_nonzero_factors k h
  funext i
  fin_cases i <;>
    simp [hermitianInverse,inverseParameters,hermitianOperator,originalAdj] <;>
    field_simp [hd,h12,h13,h23] <;>
    simp only [originalMatrixDet,originalDelta12,originalDelta13,originalDelta23] <;> ring

/-- The actual operator as a linear map. -/
def operatorLinear (k : Parameters K) : HermitianCoordinates K →ₗ[K] HermitianCoordinates K where
  toFun := hermitianOperator k
  map_add' y w := by funext i; fin_cases i <;> simp [hermitianOperator] <;> ring
  map_smul' a y := by funext i; fin_cases i <;> simp [hermitianOperator] <;> ring

def inverseLinear (k : Parameters K) : HermitianCoordinates K →ₗ[K] HermitianCoordinates K :=
  operatorLinear (inverseParameters k)

def operatorEquiv (k : Parameters K) (h : originalInverseDen k ≠ 0) :
    HermitianCoordinates K ≃ₗ[K] HermitianCoordinates K where
  toLinearMap := operatorLinear k
  invFun := hermitianInverse k
  left_inv := hermitianInverse_left k h
  right_inv := hermitianInverse_right k h

@[simp] theorem operatorEquiv_apply (k : Parameters K) (h : originalInverseDen k ≠ 0)
    (y : HermitianCoordinates K) : operatorEquiv k h y = hermitianOperator k y := rfl
@[simp] theorem operatorEquiv_symm_apply (k : Parameters K) (h : originalInverseDen k ≠ 0)
    (y : HermitianCoordinates K) : (operatorEquiv k h).symm y = hermitianInverse k y := rfl

theorem hermitianInverse_selfadjoint (k : Parameters K) (y w : HermitianCoordinates K) :
    hermitianPair y (hermitianInverse k w) = hermitianPair (hermitianInverse k y) w :=
  hermitianOperator_selfadjoint _ _ _

def pairLinear : HermitianCoordinates K →ₗ[K] HermitianCoordinates K →ₗ[K] K where
  toFun y := {
    toFun := hermitianPair y
    map_add' w v := by simp [hermitianPair]; ring
    map_smul' a w := by simp [hermitianPair]; ring }
  map_add' y w := by ext v; simp [hermitianPair]; ring
  map_smul' a y := by ext v; simp [hermitianPair]; ring

def traceLinear : HermitianCoordinates K →ₗ[K] K where
  toFun := hermitianTrace
  map_add' y w := by simp [hermitianTrace]; ring
  map_smul' a y := by simp [hermitianTrace]; ring

/-- Real and imaginary components of multiplication by a fixed kernel vector. -/
def actionLinear (z : RealVector K) : HermitianCoordinates K →ₗ[K] RealVector K where
  toFun y := ![actionRe (hermitianRe y) (hermitianIm y) z 0,
    actionIm (hermitianRe y) (hermitianIm y) z 0,
    actionRe (hermitianRe y) (hermitianIm y) z 1,
    actionIm (hermitianRe y) (hermitianIm y) z 1,
    actionRe (hermitianRe y) (hermitianIm y) z 2,
    actionIm (hermitianRe y) (hermitianIm y) z 2]
  map_add' y w := by
    funext i; fin_cases i <;>
      simp [actionRe,actionIm,hermitianRe,hermitianIm,Fin.sum_univ_three] <;> ring
  map_smul' a y := by
    funext i; fin_cases i <;>
      simp [actionRe,actionIm,hermitianRe,hermitianIm,Fin.sum_univ_three] <;> ring

#print axioms hermitianInverse_left
#print axioms hermitianInverse_right
end W3.OperatorField
