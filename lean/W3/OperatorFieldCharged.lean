import W3.OperatorField
import W3.PrimalFieldBridge
import W3.OperatorPoles

/-! The charged reconstruction in arbitrary ordered fields. -/
set_option maxHeartbeats 1000000
noncomputable section
namespace W3.OperatorField
open W3.TransferOperator W3.Elimination W3.RealModel W3.StrataTransfer W3.PrimalFieldBridge W3.Weighted
open scoped BigOperators
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def dualBeta (k : Parameters K) : K := hermitianPair hermitianIdentity (hermitianInverse k hermitianIdentity)
def dualA (k : Parameters K) (z : RealVector K) : K :=
  hermitianPair (hermitianProjector z) (hermitianInverse k hermitianIdentity)
def dualP (k : Parameters K) (z : RealVector K) : K :=
  hermitianPair (hermitianProjector z) (hermitianInverse k (hermitianProjector z))
def dualDen (k : Parameters K) (z : RealVector K) : K := denominator (dualBeta k) (dualA k z) (dualP k z)
def dualCoordinates (k : Parameters K) (z : RealVector K) : HermitianCoordinates K :=
  reconstruction (dualBeta k) (dualA k z) (dualP k z)
    (hermitianInverse k hermitianIdentity) (hermitianInverse k (hermitianProjector z))
def dualPurity (k : Parameters K) (z : RealVector K) : K := hermitianPurity (dualCoordinates k z)
def dualEnergy (k : Parameters K) (z : RealVector K) : K := dualP k z/(2*dualDen k z)

@[simp] lemma pairLinear_apply (y w : HermitianCoordinates K) : pairLinear y w = hermitianPair y w := rfl
@[simp] lemma traceLinear_apply (y : HermitianCoordinates K) : traceLinear y = hermitianTrace y := rfl
@[simp] lemma inverseLinear_apply (k : Parameters K) (y : HermitianCoordinates K) : inverseLinear k y = hermitianInverse k y := rfl

lemma actionLinear_zero_iff (z : RealVector K) (y : HermitianCoordinates K) :
    actionLinear z y = 0 ↔ ∀ i, actionRe (hermitianRe y) (hermitianIm y) z i = 0 ∧
      actionIm (hermitianRe y) (hermitianIm y) z i = 0 := by
  constructor
  · intro h i
    fin_cases i
    · exact ⟨congrFun h 0,congrFun h 1⟩
    · exact ⟨congrFun h 2,congrFun h 3⟩
    · exact ⟨congrFun h 4,congrFun h 5⟩
  · intro h
    funext i; fin_cases i
    · exact (h 0).1
    · exact (h 0).2
    · exact (h 1).1
    · exact (h 1).2
    · exact (h 2).1
    · exact (h 2).2

lemma pair_projector_of_action_zero (y : HermitianCoordinates K) (z : RealVector K)
    (h : actionLinear z y = 0) : hermitianPair (hermitianProjector z) y = 0 :=
  hermitianPair_projector_of_kernel y z ((actionLinear_zero_iff z y).mp h)

lemma inverse_trace_projector (k : Parameters K) (z : RealVector K) :
    hermitianTrace (hermitianInverse k (hermitianProjector z)) = dualA k z := by
  rw [← hermitianPair_identity_left,hermitianInverse_selfadjoint,hermitianPair_comm]
  rfl

lemma normal_inverse (k : Parameters K) (hk : originalInverseDen k ≠ 0)
    (y : HermitianCoordinates K) (z : RealVector K) (lam mu : K)
    (hn : hermitianOperator k y = lam • hermitianIdentity + mu • hermitianProjector z) :
    y = lam • hermitianInverse k hermitianIdentity + mu • hermitianInverse k (hermitianProjector z) := by
  have h := congrArg (inverseLinear k) hn
  simpa only [map_add,map_smul,inverseLinear_apply,hermitianInverse_left k hk] using h

lemma normal_equations (k : Parameters K) (hk : originalInverseDen k ≠ 0)
    (y : HermitianCoordinates K) (z : RealVector K) (lam mu : K)
    (ht : hermitianTrace y = 1) (hz : actionLinear z y = 0)
    (hn : hermitianOperator k y = lam • hermitianIdentity + mu • hermitianProjector z) :
    ChargedEquations (dualBeta k) (dualA k z) (dualP k z) lam mu := by
  have hr := normal_inverse k hk y z lam mu hn
  have h1 := congrArg traceLinear hr
  simp only [map_add,map_smul,traceLinear_apply,smul_eq_mul,ht,inverse_trace_projector] at h1
  have h2 := congrArg (pairLinear (hermitianProjector z)) hr
  simp only [map_add,map_smul,pairLinear_apply,smul_eq_mul,pair_projector_of_action_zero y z hz] at h2
  constructor
  · dsimp [dualBeta]; rw [hermitianPair_identity_left]; nlinarith [h1]
  · dsimp [dualA,dualP] at *; nlinarith [h2]

lemma normal_reconstruction (k : Parameters K) (hk : originalInverseDen k ≠ 0)
    (y : HermitianCoordinates K) (z : RealVector K) (lam mu : K)
    (ht : hermitianTrace y = 1) (hz : actionLinear z y = 0)
    (hn : hermitianOperator k y = lam • hermitianIdentity + mu • hermitianProjector z)
    (hD : dualDen k z ≠ 0) : y = dualCoordinates k z := by
  exact charged_reconstruction_unique (operatorEquiv k hk) hermitianIdentity (hermitianProjector z) y
    (dualBeta k) (dualA k z) (dualP k z) lam mu hD (normal_equations k hk y z lam mu ht hz hn) hn

lemma dual_trace (k : Parameters K) (z : RealVector K) (hD : dualDen k z ≠ 0) :
    hermitianTrace (dualCoordinates k z) = 1 := by
  exact reconstruction_trace (dualBeta k) (dualA k z) (dualP k z)
    (hermitianInverse k hermitianIdentity) (hermitianInverse k (hermitianProjector z))
    traceLinear (by simp [dualBeta]) (inverse_trace_projector k z) hD

lemma dual_kernel_iff (k : Parameters K) (z : RealVector K) (hD : dualDen k z ≠ 0) :
    actionLinear z (dualCoordinates k z) = 0 ↔
      actionLinear z (dualA k z • hermitianInverse k (hermitianProjector z) -
        dualP k z • hermitianInverse k hermitianIdentity) = 0 :=
  reconstruction_kernel_iff _ _ _ _ _ (actionLinear z) hD

lemma dual_energy (k : Parameters K) (hk : originalInverseDen k ≠ 0) (z : RealVector K)
    (hD : dualDen k z ≠ 0) (hz : actionLinear z (dualCoordinates k z) = 0) :
    hermitianEnergy k (dualCoordinates k z)/2 = dualEnergy k z := by
  rw [hermitianEnergy_eq_pair]
  apply reconstruction_energy _ _ _ _ _ hermitianIdentity (hermitianProjector z)
    (operatorLinear k) pairLinear (hermitianInverse_right k hk _) (hermitianInverse_right k hk _)
  · change hermitianPair (dualCoordinates k z) hermitianIdentity = 1
    simpa only [hermitianPair_identity_right] using dual_trace k z hD
  · change hermitianPair (dualCoordinates k z) (hermitianProjector z) = 0
    rw [hermitianPair_comm]
    exact pair_projector_of_action_zero _ _ hz

end W3.OperatorField
