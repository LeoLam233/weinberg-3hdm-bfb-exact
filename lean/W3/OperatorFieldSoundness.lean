import W3.OperatorFieldAmplitude
import W3.WeightedAlgebraicityEigen

/-! Every retained common dual-spectrum solution yields an actual normalized
physical field in the sixteen-level ordered field. -/
noncomputable section
namespace W3.OperatorField
open W3.TransferOperator W3.Elimination W3.RealModel W3.StrataTransfer W3.PrimalFieldBridge W3.Weighted W3.Infinitesimal
open scoped BigOperators
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

lemma dual_amplitudes_proportional (k : Parameters K) (z : RealVector K) (lam : K)
    (h : AmplitudeEquations (toSpectrum (originalDual k)) (pairVector z 0) (pairVector z 1) (pairVector z 2)
      (originalDual k).g1 (originalDual k).g2 (originalDual k).g3 lam) :
    actionLinear z (hermitianInverse k (hermitianProjector z)) =
      (lam/2) • actionLinear z (hermitianInverse k hermitianIdentity) := by
  have hh := (dual_amplitudes_iff k (pairVector z 0) (pairVector z 1) (pairVector z 2) (lam/2)).mp (by
    rw [show 2*(lam/2)=lam by ring]
    exact h)
  have he := amplitudes_imply_neutral_eigen (inverseParameters k) z
    (originalDual k).g1 (originalDual k).g2 (originalDual k).g3 (lam/2) hh
  have hRe : hermitianRe (hermitianInverse k (hermitianProjector z)) =
      operatorRe (inverseParameters k) (neutralFields z) := by
    rw [projector_eq_neutral_gram]; rfl
  have hIm : hermitianIm (hermitianInverse k (hermitianProjector z)) =
      operatorIm (inverseParameters k) (neutralFields z) := by
    rw [projector_eq_neutral_gram]; rfl
  funext i
  fin_cases i
  · change actionRe _ _ z 0 = lam/2*actionRe _ _ z 0
    rw [inverse_identity_actionRe,hRe,hIm,(he 0).1]
    simp [dualWeights]
    ring
  · change actionIm _ _ z 0 = lam/2*actionIm _ _ z 0
    rw [inverse_identity_actionIm,hRe,hIm,(he 0).2]
    simp [dualWeights]
    ring
  · change actionRe _ _ z 1 = lam/2*actionRe _ _ z 1
    rw [inverse_identity_actionRe,hRe,hIm,(he 1).1]
    simp [dualWeights]
    ring
  · change actionIm _ _ z 1 = lam/2*actionIm _ _ z 1
    rw [inverse_identity_actionIm,hRe,hIm,(he 1).2]
    simp [dualWeights]
    ring
  · change actionRe _ _ z 2 = lam/2*actionRe _ _ z 2
    rw [inverse_identity_actionRe,hRe,hIm,(he 2).1]
    simp [dualWeights]
    ring
  · change actionIm _ _ z 2 = lam/2*actionIm _ _ z 2
    rw [inverse_identity_actionIm,hRe,hIm,(he 2).2]
    simp [dualWeights]
    ring

/-- This algebraic soundness direction also permits p=0 and a=0. -/
lemma dual_amplitudes_kernel (k : Parameters K) (z : RealVector K) (lam : K)
    (h : AmplitudeEquations (toSpectrum (originalDual k)) (pairVector z 0) (pairVector z 1) (pairVector z 2)
      (originalDual k).g1 (originalDual k).g2 (originalDual k).g3 lam) :
    actionLinear z (dualA k z • hermitianInverse k (hermitianProjector z) -
      dualP k z • hermitianInverse k hermitianIdentity) = 0 := by
  have hp := amplitude_energy_eigen (toSpectrum (originalDual k)) (pairVector z 0) (pairVector z 1) (pairVector z 2)
    (originalDual k).g1 (originalDual k).g2 (originalDual k).g3 lam h
  rw [dual_amplitude_energy,← dualA_eq_weight] at hp
  rw [map_sub,map_smul,map_smul,dual_amplitudes_proportional k z lam h,smul_smul]
  rw [show dualA k z*(lam/2)=dualP k z by rw [hp]; ring]
  exact sub_self _

lemma dual_candidate_physical (k : Parameters SixteenLevelField) (hk : originalInverseDen k ≠ 0)
    (z : RealVector SixteenLevelField) (lam : SixteenLevelField) (hu : zMass z=1)
    (h : AmplitudeEquations (toSpectrum (originalDual k)) (pairVector z 0) (pairVector z 1) (pairVector z 2)
      (originalDual k).g1 (originalDual k).g2 (originalDual k).g3 lam)
    (hD : dualDen k z ≠ 0) (hchi : dualPurity k z≤1) :
    ∃ x : RealFields SixteenLevelField,mass x=1 ∧ gramCoordinates x=dualCoordinates k z ∧
      quarticReal k x=dualEnergy k z := by
  have hker := (dual_kernel_iff k z hD).mpr (dual_amplitudes_kernel k z lam h)
  have hn : NormalizedKernel (dualCoordinates k z) z :=
    ⟨dual_trace k z hD,hu,(actionLinear_zero_iff z _).mp hker⟩
  obtain ⟨x,hx,hG,hE⟩ := sixteen_physical_energy_witness k (dualCoordinates k z) z hn hchi
  exact ⟨x,hx,(gramMatches_iff x _).mp hG,by
    rw [quarticReal,hE]; exact dual_energy k hk z hD hker⟩

#print axioms dual_amplitudes_kernel
#print axioms dual_candidate_physical
end W3.OperatorField
