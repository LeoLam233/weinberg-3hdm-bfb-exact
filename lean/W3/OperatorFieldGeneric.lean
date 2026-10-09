import W3.OperatorFieldAmplitude
import W3.TransferOperatorStrata

/-! Genericity discharges every charged exceptional linear-system branch over
arbitrary ordered fields, including the source's sixteen-level field. -/
noncomputable section
namespace W3.OperatorField
open W3.TransferOperator W3.Elimination W3.RealModel W3.StrataTransfer W3.PrimalFieldBridge W3.Weighted
open scoped BigOperators
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

lemma generic_dual_weights (k : Parameters K)
    (hex : completeWeightedExceptional (originalDual k) ≠ 0) : ∀ i,dualWeights k i ≠ 0 := by
  obtain ⟨_,h0,h1,h2,_,_,_,_⟩ := elementaryExceptional_properties _ (mul_ne_zero_iff.mp hex).2
  intro i; fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- The actual normal equation and the explicit generic polynomial force D≠0. -/
theorem generic_normal_den_ne_zero (k : Parameters K) (hk : originalInverseDen k ≠ 0)
    (hex : completeWeightedExceptional (originalDual k) ≠ 0)
    (y : HermitianCoordinates K) (z : RealVector K) (lam mu : K)
    (hu : zMass z = 1) (ht : hermitianTrace y = 1) (hz : actionLinear z y = 0)
    (hn : hermitianOperator k y = lam • hermitianIdentity + mu • hermitianProjector z) :
    dualDen k z ≠ 0 := by
  intro hD
  have he := normal_equations k hk y z lam mu ht hz hn
  have hr := normal_inverse k hk y z lam mu hn
  have hU := inverse_identity_action_ne_zero k z hu (generic_dual_weights k hex)
  have hm := singular_mu_ne_zero (dualBeta k) (dualA k z) (dualP k z) lam mu
    _ _ y (actionLinear z) hD he hr hz hU
  have hp := kernel_proportional lam mu _ _ y (actionLinear z) hm hr hz
  exact generic_proportional_a_ne_zero k z (-lam/mu) hex hu hp
    ((charged_equations_singular_iff _ _ _ _ _ hD).mp he).1

theorem generic_normal_a_ne_zero (k : Parameters K) (hk : originalInverseDen k ≠ 0)
    (hex : completeWeightedExceptional (originalDual k) ≠ 0)
    (y : HermitianCoordinates K) (z : RealVector K) (lam mu : K)
    (hu : zMass z = 1) (ht : hermitianTrace y = 1) (hz : actionLinear z y = 0)
    (hn : hermitianOperator k y = lam • hermitianIdentity + mu • hermitianProjector z) :
    dualA k z ≠ 0 := by
  exact charged_a_ne_zero (dualBeta k) (dualA k z) (dualP k z) lam mu _ _ y (actionLinear z)
    (generic_normal_den_ne_zero k hk hex y z lam mu hu ht hz hn)
    (normal_equations k hk y z lam mu ht hz hn) (normal_inverse k hk y z lam mu hn) hz
    (inverse_identity_action_ne_zero k z hu (generic_dual_weights k hex))

lemma projective_proportional (k : Parameters K) (z : RealVector K)
    (ha : dualA k z ≠ 0)
    (h : actionLinear z (dualA k z • hermitianInverse k (hermitianProjector z) -
      dualP k z • hermitianInverse k hermitianIdentity) = 0) :
    actionLinear z (hermitianInverse k (hermitianProjector z)) =
      (dualP k z/dualA k z) • actionLinear z (hermitianInverse k hermitianIdentity) := by
  simp only [map_sub,map_smul,sub_eq_zero] at h
  calc
    _ = (dualA k z)⁻¹ • (dualA k z • actionLinear z (hermitianInverse k (hermitianProjector z))) := by
      rw [smul_smul,inv_mul_cancel₀ ha,one_smul]
    _ = (dualA k z)⁻¹ • (dualP k z • actionLinear z (hermitianInverse k hermitianIdentity)) := by rw [h]
    _ = _ := by rw [smul_smul]; congr 1; ring

/-- Full charged coverage of an actual normal stratum, with no projective or
coverage assumption and with p=0 retained. -/
theorem generic_charged_stratum (k : Parameters K) (hk : originalInverseDen k ≠ 0)
    (hex : completeWeightedExceptional (originalDual k) ≠ 0)
    (y : HermitianCoordinates K) (z : RealVector K) (lam mu : K)
    (hu : zMass z = 1) (ht : hermitianTrace y = 1) (hz : actionLinear z y = 0)
    (hn : hermitianOperator k y = lam • hermitianIdentity + mu • hermitianProjector z) :
    dualA k z ≠ 0 ∧ dualDen k z ≠ 0 ∧ y = dualCoordinates k z ∧
      AmplitudeEquations (toSpectrum (originalDual k)) (pairVector z 0) (pairVector z 1) (pairVector z 2)
        (originalDual k).g1 (originalDual k).g2 (originalDual k).g3 (2*(dualP k z/dualA k z)) ∧
      hermitianEnergy k y/2 = dualEnergy k z := by
  have hD := generic_normal_den_ne_zero k hk hex y z lam mu hu ht hz hn
  have ha := generic_normal_a_ne_zero k hk hex y z lam mu hu ht hz hn
  have hY := normal_reconstruction k hk y z lam mu ht hz hn hD
  have hker : actionLinear z (dualCoordinates k z) = 0 := by rw [← hY]; exact hz
  have hp := (dual_kernel_iff k z hD).mp hker
  exact ⟨ha,hD,hY,proportional_implies_dual_amplitudes k z _ (projective_proportional k z ha hp),
    by rw [hY]; exact dual_energy k hk z hD hker⟩

#print axioms generic_charged_stratum
end W3.OperatorField
