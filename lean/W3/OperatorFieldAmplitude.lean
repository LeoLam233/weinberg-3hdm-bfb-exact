import W3.OperatorFieldCharged

/-! Exact identification of the rational inverse operator with the common
weighted spectrum over arbitrary ordered fields. -/
set_option maxHeartbeats 1200000
noncomputable section
namespace W3.OperatorField
open W3.TransferOperator W3.Elimination W3.RealModel W3.StrataTransfer W3.PrimalFieldBridge W3.Weighted
open ComplexPair
open scoped BigOperators
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def dualWeights (k : Parameters K) : Fin 3 → K :=
  ![(originalDual k).g1,(originalDual k).g2,(originalDual k).g3]

lemma projector_eq_neutral_gram (z : RealVector K) :
    hermitianProjector z = gramCoordinates (neutralFields z) := by
  apply hermitianCoordinates_ext
  · intro i j
    rw [hermitianRe_projector,hermitianRe_gramCoordinates,neutralFields_gramRe]
  · intro i j
    rw [hermitianIm_projector,hermitianIm_gramCoordinates,neutralFields_gramIm]

lemma inverse_identity (k : Parameters K) :
    hermitianInverse k hermitianIdentity =
      ![dualWeights k 0,dualWeights k 1,dualWeights k 2,0,0,0,0,0,0] := by
  funext i; fin_cases i <;>
    simp [hermitianInverse,hermitianOperator,inverseParameters,hermitianIdentity,dualWeights,originalDual] <;> ring

lemma inverse_identity_actionRe (k : Parameters K) (z : RealVector K) (i : Fin 3) :
    actionRe (hermitianRe (hermitianInverse k hermitianIdentity))
      (hermitianIm (hermitianInverse k hermitianIdentity)) z i = dualWeights k i*zRe z i := by
  rw [inverse_identity]
  fin_cases i <;> simp [actionRe,hermitianRe,hermitianIm,Fin.sum_univ_three]
lemma inverse_identity_actionIm (k : Parameters K) (z : RealVector K) (i : Fin 3) :
    actionIm (hermitianRe (hermitianInverse k hermitianIdentity))
      (hermitianIm (hermitianInverse k hermitianIdentity)) z i = dualWeights k i*zIm z i := by
  rw [inverse_identity]
  fin_cases i <;> simp [actionIm,hermitianRe,hermitianIm,Fin.sum_univ_three]

lemma dualA_eq_weight (k : Parameters K) (z : RealVector K) :
    dualA k z = (originalDual k).g1*normSq (pairVector z 0)+
      (originalDual k).g2*normSq (pairVector z 1)+(originalDual k).g3*normSq (pairVector z 2) := by
  unfold dualA
  rw [inverse_identity]
  simp [hermitianPair,hermitianProjector,dualWeights,pairVector,normSq]
  ring

lemma dual_rows (k : Parameters K) (z1 z2 z3 : ComplexPair K) :
    amplitudeRow₁ (toSpectrum (originalDual k)) z1 z2 z3 =
      scale 2 (amplitudeRow₁ (toSpectrum (originalPrimal (inverseParameters k))) z1 z2 z3) ∧
    amplitudeRow₂ (toSpectrum (originalDual k)) z1 z2 z3 =
      scale 2 (amplitudeRow₂ (toSpectrum (originalPrimal (inverseParameters k))) z1 z2 z3) ∧
    amplitudeRow₃ (toSpectrum (originalDual k)) z1 z2 z3 =
      scale 2 (amplitudeRow₃ (toSpectrum (originalPrimal (inverseParameters k))) z1 z2 z3) := by
  constructor
  · apply complexPair_ext <;>
      simp [amplitudeRow₁,amplitudeEdge,toSpectrum,originalDual,originalPrimal,inverseParameters,mul,scale] <;> ring
  constructor
  · apply complexPair_ext <;>
      simp [amplitudeRow₂,amplitudeEdge,toSpectrum,originalDual,originalPrimal,inverseParameters,mul,scale] <;> ring
  · apply complexPair_ext <;>
      simp [amplitudeRow₃,amplitudeEdge,toSpectrum,originalDual,originalPrimal,inverseParameters,mul,scale] <;> ring

lemma dual_amplitudes_iff (k : Parameters K) (z1 z2 z3 : ComplexPair K) (lam : K) :
    AmplitudeEquations (toSpectrum (originalDual k)) z1 z2 z3
      (originalDual k).g1 (originalDual k).g2 (originalDual k).g3 (2*lam) ↔
    AmplitudeEquations (toSpectrum (originalPrimal (inverseParameters k))) z1 z2 z3
      (originalDual k).g1 (originalDual k).g2 (originalDual k).g3 lam := by
  have h := dual_rows k z1 z2 z3
  simp only [AmplitudeEquations,h.1,h.2.1,h.2.2]
  have hc (x : ComplexPair K) (r : K) : scale 2 x = ⟨2*lam*r,0⟩ ↔ x = ⟨lam*r,0⟩ := by
    constructor
    · intro hx
      apply complexPair_ext
      · have hh := congrArg ComplexPair.re hx; simp only [scale] at hh; linarith
      · have hh := congrArg ComplexPair.im hx; simp only [scale] at hh; linarith
    · rintro rfl; apply complexPair_ext <;> simp [scale] <;> ring
  simpa only [_root_.mul_assoc] using and_congr
    (hc (amplitudeRow₁ (toSpectrum (originalPrimal (inverseParameters k))) z1 z2 z3) ((originalDual k).g1*normSq z1))
    (and_congr (hc (amplitudeRow₂ (toSpectrum (originalPrimal (inverseParameters k))) z1 z2 z3) ((originalDual k).g2*normSq z2))
      (hc (amplitudeRow₃ (toSpectrum (originalPrimal (inverseParameters k))) z1 z2 z3) ((originalDual k).g3*normSq z3)))

lemma inverse_projector_contraction (k : Parameters K) (z : RealVector K) :
    amplitudeRow₁ (toSpectrum (originalPrimal (inverseParameters k))) (pairVector z 0) (pairVector z 1) (pairVector z 2) =
      ⟨zRe z 0*actionRe (hermitianRe (hermitianInverse k (hermitianProjector z))) (hermitianIm (hermitianInverse k (hermitianProjector z))) z 0+
        zIm z 0*actionIm (hermitianRe (hermitianInverse k (hermitianProjector z))) (hermitianIm (hermitianInverse k (hermitianProjector z))) z 0,
       zRe z 0*actionIm (hermitianRe (hermitianInverse k (hermitianProjector z))) (hermitianIm (hermitianInverse k (hermitianProjector z))) z 0-
        zIm z 0*actionRe (hermitianRe (hermitianInverse k (hermitianProjector z))) (hermitianIm (hermitianInverse k (hermitianProjector z))) z 0⟩ ∧
    amplitudeRow₂ (toSpectrum (originalPrimal (inverseParameters k))) (pairVector z 0) (pairVector z 1) (pairVector z 2) =
      ⟨zRe z 1*actionRe (hermitianRe (hermitianInverse k (hermitianProjector z))) (hermitianIm (hermitianInverse k (hermitianProjector z))) z 1+
        zIm z 1*actionIm (hermitianRe (hermitianInverse k (hermitianProjector z))) (hermitianIm (hermitianInverse k (hermitianProjector z))) z 1,
       zRe z 1*actionIm (hermitianRe (hermitianInverse k (hermitianProjector z))) (hermitianIm (hermitianInverse k (hermitianProjector z))) z 1-
        zIm z 1*actionRe (hermitianRe (hermitianInverse k (hermitianProjector z))) (hermitianIm (hermitianInverse k (hermitianProjector z))) z 1⟩ ∧
    amplitudeRow₃ (toSpectrum (originalPrimal (inverseParameters k))) (pairVector z 0) (pairVector z 1) (pairVector z 2) =
      ⟨zRe z 2*actionRe (hermitianRe (hermitianInverse k (hermitianProjector z))) (hermitianIm (hermitianInverse k (hermitianProjector z))) z 2+
        zIm z 2*actionIm (hermitianRe (hermitianInverse k (hermitianProjector z))) (hermitianIm (hermitianInverse k (hermitianProjector z))) z 2,
       zRe z 2*actionIm (hermitianRe (hermitianInverse k (hermitianProjector z))) (hermitianIm (hermitianInverse k (hermitianProjector z))) z 2-
        zIm z 2*actionRe (hermitianRe (hermitianInverse k (hermitianProjector z))) (hermitianIm (hermitianInverse k (hermitianProjector z))) z 2⟩ := by
  simpa only [projector_eq_neutral_gram,hermitianInverse,hermitianRe_operator_gramCoordinates,
    hermitianIm_operator_gramCoordinates] using neutral_contraction (inverseParameters k) z

lemma proportional_implies_dual_amplitudes (k : Parameters K) (z : RealVector K) (rho : K)
    (h : actionLinear z (hermitianInverse k (hermitianProjector z)) =
      rho • actionLinear z (hermitianInverse k hermitianIdentity)) :
    AmplitudeEquations (toSpectrum (originalDual k)) (pairVector z 0) (pairVector z 1) (pairVector z 2)
      (originalDual k).g1 (originalDual k).g2 (originalDual k).g3 (2*rho) := by
  apply (dual_amplitudes_iff k _ _ _ rho).mpr
  have hr (i : Fin 3) : actionRe (hermitianRe (hermitianInverse k (hermitianProjector z)))
      (hermitianIm (hermitianInverse k (hermitianProjector z))) z i = rho*dualWeights k i*zRe z i := by
    fin_cases i
    · calc
        _ = rho*actionRe (hermitianRe (hermitianInverse k hermitianIdentity))
          (hermitianIm (hermitianInverse k hermitianIdentity)) z 0 := congrFun h 0
        _ = _ := by rw [inverse_identity_actionRe]; simp [dualWeights,zRe]; ring
    · calc
        _ = rho*actionRe (hermitianRe (hermitianInverse k hermitianIdentity))
          (hermitianIm (hermitianInverse k hermitianIdentity)) z 1 := congrFun h 2
        _ = _ := by rw [inverse_identity_actionRe]; simp [dualWeights,zRe]; ring
    · calc
        _ = rho*actionRe (hermitianRe (hermitianInverse k hermitianIdentity))
          (hermitianIm (hermitianInverse k hermitianIdentity)) z 2 := congrFun h 4
        _ = _ := by rw [inverse_identity_actionRe]; simp [dualWeights,zRe]; ring
  have hi (i : Fin 3) : actionIm (hermitianRe (hermitianInverse k (hermitianProjector z)))
      (hermitianIm (hermitianInverse k (hermitianProjector z))) z i = rho*dualWeights k i*zIm z i := by
    fin_cases i
    · calc
        _ = rho*actionIm (hermitianRe (hermitianInverse k hermitianIdentity))
          (hermitianIm (hermitianInverse k hermitianIdentity)) z 0 := congrFun h 1
        _ = _ := by rw [inverse_identity_actionIm]; simp [dualWeights,zIm]; ring
    · calc
        _ = rho*actionIm (hermitianRe (hermitianInverse k hermitianIdentity))
          (hermitianIm (hermitianInverse k hermitianIdentity)) z 1 := congrFun h 3
        _ = _ := by rw [inverse_identity_actionIm]; simp [dualWeights,zIm]; ring
    · calc
        _ = rho*actionIm (hermitianRe (hermitianInverse k hermitianIdentity))
          (hermitianIm (hermitianInverse k hermitianIdentity)) z 2 := congrFun h 5
        _ = _ := by rw [inverse_identity_actionIm]; simp [dualWeights,zIm]; ring
  have hc := inverse_projector_contraction k z
  unfold AmplitudeEquations
  rw [hc.1,hc.2.1,hc.2.2,hr 0,hr 1,hr 2,hi 0,hi 1,hi 2]
  constructor
  · apply complexPair_ext <;> simp [dualWeights,pairVector,normSq] <;> ring
  constructor <;> apply complexPair_ext <;> simp [dualWeights,pairVector,normSq] <;> ring

/-- The doubled inverse spectrum numerator is exactly p=<P,RP>. -/
lemma dual_amplitude_energy (k : Parameters K) (z : RealVector K) :
    amplitudeEnergy (toSpectrum (originalDual k)) (pairVector z 0) (pairVector z 1) (pairVector z 2) = dualP k z := by
  have hr := dual_rows k (pairVector z 0) (pairVector z 1) (pairVector z 2)
  have he : amplitudeEnergy (toSpectrum (originalDual k)) (pairVector z 0) (pairVector z 1) (pairVector z 2) =
      2*amplitudeEnergy (toSpectrum (originalPrimal (inverseParameters k))) (pairVector z 0) (pairVector z 1) (pairVector z 2) := by
    simp only [amplitudeEnergy,hr.1,hr.2.1,hr.2.2,scale]
    ring
  rw [he,← neutralFields_energy,quarticReal,← hermitianEnergy_gramCoordinates,
    ← projector_eq_neutral_gram,hermitianEnergy_eq_pair]
  dsimp [dualP,hermitianInverse]
  ring

lemma inverse_identity_action_ne_zero (k : Parameters K) (z : RealVector K)
    (hu : zMass z = 1) (hg : ∀ i,dualWeights k i ≠ 0) :
    actionLinear z (hermitianInverse k hermitianIdentity) ≠ 0 := by
  intro h
  have hh := (actionLinear_zero_iff z _).mp h
  have hr (i : Fin 3) : zRe z i = 0 := by
    have hi := (hh i).1
    rw [inverse_identity_actionRe] at hi
    exact (mul_eq_zero.mp hi).resolve_left (hg i)
  have hi (i : Fin 3) : zIm z i = 0 := by
    have hi := (hh i).2
    rw [inverse_identity_actionIm] at hi
    exact (mul_eq_zero.mp hi).resolve_left (hg i)
  simp [zMass,hr,hi] at hu

lemma generic_proportional_a_ne_zero (k : Parameters K) (z : RealVector K) (rho : K)
    (hex : completeWeightedExceptional (originalDual k) ≠ 0) (hu : zMass z = 1)
    (h : actionLinear z (hermitianInverse k (hermitianProjector z)) =
      rho • actionLinear z (hermitianInverse k hermitianIdentity)) : dualA k z ≠ 0 := by
  rw [dualA_eq_weight]
  exact generic_amplitude_weight_ne_zero (originalDual k) hex (pairVector z 0) (pairVector z 1) (pairVector z 2)
    (2*rho) ((pairVector_norm_sum z).trans hu) (proportional_implies_dual_amplitudes k z rho h)

#print axioms proportional_implies_dual_amplitudes
#print axioms generic_proportional_a_ne_zero
end W3.OperatorField
