import W3.OperatorCharged
import W3.OperatorPoles
import W3.WeightedInverseBridge
import W3.EliminationOperator

/-! Concrete generic exclusion of every missing charged denominator branch. -/
noncomputable section
namespace W3.Operator
open Matrix ComplexConjugate
open W3.Weighted W3.Elimination
open scoped BigOperators ComplexOrder

/-- Ordered-data packaging, retaining the exact α', e', d' and g of the source. -/
def weightedDataOf (k : SpectrumData ℝ) (g : Fin 3 → ℝ) : WeightedData ℝ :=
  ⟨k.a₁,k.a₂,k.a₃,k.e₁₂,k.e₁₃,k.e₂₃,
    k.d₁₂.re,k.d₁₂.im,k.d₁₃.re,k.d₁₃.im,k.d₂₃.re,k.d₂₃.im,g 0,g 1,g 2⟩

@[simp] lemma toSpectrum_weightedDataOf (k : SpectrumData ℝ) (g : Fin 3 → ℝ) :
    toSpectrum (weightedDataOf k g) = k := by cases k; rfl

def operatorDualData (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ) (d : Fin 3 → ℂ) : WeightedData ℝ :=
  weightedDataOf (dualSpectrum A c d) (dualWeights A)

@[simp] lemma weightedDataOf_toSpectrum (w : WeightedData ℝ) :
    weightedDataOf (toSpectrum w) ![w.g1,w.g2,w.g3] = w := by cases w; rfl

/-- Exact identification with the rational fifteen-coordinate genericity map. -/
theorem operatorDualData_original (x : Fin 15 → ℝ) (h : originalInverseDen x ≠ 0) :
    operatorDualData (couplingMatrix (couplingsOfOriginal x))
      (couplingsOfOriginal x).c (couplingsOfOriginal x).d = originalDual x := by
  unfold operatorDualData
  rw [← dualSpectrum_original x h, dualWeights_original x h]
  exact weightedDataOf_toSpectrum _

theorem operatorDualData_originalOfCouplings (κ : W3.Couplings)
    (h : originalInverseDen (originalOfCouplings κ) ≠ 0) :
    operatorDualData (couplingMatrix κ) κ.c κ.d = originalDual (originalOfCouplings κ) := by
  simpa only [couplings_original_roundtrip] using operatorDualData_original (originalOfCouplings κ) h

lemma dualA_eq_weight (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ) (d : Fin 3 → ℂ)
    (hA : A.det ≠ 0) (hΔ : ∀ i, blockDet (c i) (d i) ≠ 0) (z : Fin 3 → ℂ) :
    dualA (structuredEquiv A c d hA hΔ).symm z =
      dualWeights A 0 * Complex.normSq (z 0) + dualWeights A 1 * Complex.normSq (z 1) +
        dualWeights A 2 * Complex.normSq (z 2) := by
  simp [dualA, structuredEquiv_symm_apply, coordinatePair, projectorCoordinates,
    structuredInverse, identityCoordinates, inverseBlock, dualWeights, Fin.sum_univ_three]
  ring

/-- A proportional inverse-kernel equation, including the singular charged
branch, cannot lie on a weighted pole under the explicit generic polynomial. -/
theorem generic_inverse_proportional_weight_ne_zero
    (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ) (d z : Fin 3 → ℂ)
    (hA : A.IsSymm) (hunit : ∑ i, Complex.normSq (z i) = 1) (ρ : ℝ)
    (hex : completeWeightedExceptional (operatorDualData A c d) ≠ 0)
    (hprop : coordinateMatrix (structuredInverse A c d (projectorCoordinates z)) *ᵥ z =
      ρ • (coordinateMatrix (structuredInverse A c d identityCoordinates) *ᵥ z)) :
    dualWeights A 0 * Complex.normSq (z 0) + dualWeights A 1 * Complex.normSq (z 1) +
      dualWeights A 2 * Complex.normSq (z 2) ≠ 0 := by
  have heigen : coordinateMatrix (structuredLinear A⁻¹ (inverseC c d) (inverseD c d)
      (projectorCoordinates z)) *ᵥ z = fun i => ((ρ * dualWeights A i : ℝ) : ℂ) * z i := by
    rw [← structuredInverse_eq_linear, hprop, inverse_identity_diagonal]
    ext i
    simp [dualWeights, Matrix.mulVec_diagonal, Complex.real_smul, mul_assoc]
  have he := structured_eigen_implies_amplitudes A⁻¹ (inverseC c d) (inverseD c d) z (dualWeights A) ρ
    (congrFun (congrFun hA.inv 0) 1) (congrFun (congrFun hA.inv 0) 2)
    (congrFun (congrFun hA.inv 1) 2) heigen
  have he2 := amplitudeEquations_scale 2 _ _ _ _ _ _ _ _ he
  have hn : (ofComplex (z 0)).normSq + (ofComplex (z 1)).normSq + (ofComplex (z 2)).normSq = 1 := by
    simpa [ofComplex, ComplexPair.normSq, Complex.normSq_apply, Fin.sum_univ_three, pow_two] using hunit
  have hout := generic_amplitude_weight_ne_zero (operatorDualData A c d) hex
    (ofComplex (z 0)) (ofComplex (z 1)) (ofComplex (z 2)) (2*ρ) hn (by
      rw [show toSpectrum (operatorDualData A c d) = dualSpectrum A c d from toSpectrum_weightedDataOf _ _]
      exact he2)
  simpa [operatorDualData, weightedDataOf, ofComplex, ComplexPair.normSq, Complex.normSq_apply, pow_two] using hout

/-- The charged denominator D is genuinely nonzero under the proved explicit
weighted generic certificate; it is not an assumed stationary-coverage condition. -/
theorem generic_normal_denominator_ne_zero (κ : W3.Couplings)
    (hA : (couplingMatrix κ).det ≠ 0) (hΔ : ∀ i, blockDet (κ.c i) (κ.d i) ≠ 0)
    (hex : completeWeightedExceptional (operatorDualData (couplingMatrix κ) κ.c κ.d) ≠ 0)
    (K : Coordinates) (z : Fin 3 → ℂ) (lam μ : ℝ)
    (hunit : ∑ i, Complex.normSq (z i) = 1)
    (htr : (coordinateMatrix K).trace = 1) (hker : coordinateMatrix K *ᵥ z = 0)
    (hnormal : coordinateMatrix (couplingEquiv κ hA hΔ K) = lam • 1 + μ • projector z) :
    denominator (dualBeta (couplingEquiv κ hA hΔ).symm)
      (dualA (couplingEquiv κ hA hΔ).symm z) (dualP (couplingEquiv κ hA hΔ).symm z) ≠ 0 := by
  intro hD
  have hz : z ≠ 0 := by intro hz; simp [hz] at hunit
  have hel := (mul_ne_zero_iff.mp hex).2
  obtain ⟨hloop,hg₀,hg₁,hg₂,hβ,hp01,hp02,hp12⟩ := elementaryExceptional_properties _ hel
  have hg : ∀ i, dualWeights (couplingMatrix κ) i ≠ 0 := by
    intro i; fin_cases i
    · exact hg₀
    · exact hg₁
    · exact hg₂
  have hU : coordinateMatrix ((couplingEquiv κ hA hΔ).symm identityCoordinates) *ᵥ z ≠ 0 :=
    inverse_identity_action_ne_zero _ _ _ z hz hg
  obtain ⟨hμ,hprop⟩ := normal_charged_singular (couplingEquiv κ hA hΔ)
    (couplingEquiv_selfadjoint κ hA hΔ) K z lam μ htr hker hnormal hD hU
  have ha := ((charged_equations_singular_iff _ _ _ _ _ hD).mp
    (normal_charged_equations (couplingEquiv κ hA hΔ)
      (couplingEquiv_selfadjoint κ hA hΔ) K z lam μ htr hker hnormal)).1
  have hn := generic_inverse_proportional_weight_ne_zero (couplingMatrix κ) κ.c κ.d z
    (couplingMatrix_isSymm κ) hunit (-lam/μ) hex hprop
  apply hn
  exact (dualA_eq_weight (couplingMatrix κ) κ.c κ.d hA hΔ z).symm.trans ha

/-- Nonzero a follows from the actual RI kernel test, even at p=0. -/
theorem generic_normal_a_ne_zero (κ : W3.Couplings)
    (hA : (couplingMatrix κ).det ≠ 0) (hΔ : ∀ i, blockDet (κ.c i) (κ.d i) ≠ 0)
    (hex : completeWeightedExceptional (operatorDualData (couplingMatrix κ) κ.c κ.d) ≠ 0)
    (K : Coordinates) (z : Fin 3 → ℂ) (lam μ : ℝ)
    (hunit : ∑ i, Complex.normSq (z i) = 1)
    (htr : (coordinateMatrix K).trace = 1) (hker : coordinateMatrix K *ᵥ z = 0)
    (hnormal : coordinateMatrix (couplingEquiv κ hA hΔ K) = lam • 1 + μ • projector z) :
    dualA (couplingEquiv κ hA hΔ).symm z ≠ 0 := by
  have hD := generic_normal_denominator_ne_zero κ hA hΔ hex K z lam μ hunit htr hker hnormal
  have hz : z ≠ 0 := by intro hz; simp [hz] at hunit
  obtain ⟨hloop,hg₀,hg₁,hg₂,hβ,hp01,hp02,hp12⟩ := elementaryExceptional_properties _ ((mul_ne_zero_iff.mp hex).2)
  have hg : ∀ i, dualWeights (couplingMatrix κ) i ≠ 0 := by
    intro i; fin_cases i
    · exact hg₀
    · exact hg₁
    · exact hg₂
  apply charged_a_ne_zero _ _ _ lam μ _ _ K (coordinateAction z) hD
    (normal_charged_equations (couplingEquiv κ hA hΔ)
      (couplingEquiv_selfadjoint κ hA hΔ) K z lam μ htr hker hnormal)
    (inverse_normal_equation (couplingEquiv κ hA hΔ) K z lam μ hnormal) hker
  exact inverse_identity_action_ne_zero _ _ _ z hz hg

#print axioms generic_normal_denominator_ne_zero
#print axioms generic_normal_a_ne_zero
end W3.Operator
