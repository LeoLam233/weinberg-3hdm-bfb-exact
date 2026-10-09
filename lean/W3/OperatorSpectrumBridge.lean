import W3.OperatorInvariance
import W3.WeightedValue

/-! Reverse amplitude-to-operator and exact dual numerator identities. -/
noncomputable section
namespace W3.Operator
open Matrix ComplexConjugate
open W3.Weighted W3.Elimination
open scoped BigOperators

def complexOfPair (z : ComplexPair ℝ) : ℂ := ⟨z.re,z.im⟩

@[simp] lemma ofComplex_complexOfPair (z : ComplexPair ℝ) : ofComplex (complexOfPair z) = z := by cases z; rfl
@[simp] lemma complexOfPair_ofComplex (z : ℂ) : complexOfPair (ofComplex z) = z := rfl
@[simp] lemma normSq_ofComplex (z : ℂ) : (ofComplex z).normSq = Complex.normSq z := by
  simp [ofComplex, ComplexPair.normSq, Complex.normSq_apply, pow_two]

lemma structured_amplitude_energy (A : Matrix (Fin 3) (Fin 3) ℝ)
    (c : Fin 3 → ℝ) (d z : Fin 3 → ℂ) (hA : A.IsSymm) :
    coordinatePair (projectorCoordinates z) (structuredLinear A c d (projectorCoordinates z)) / 2 =
      amplitudeEnergy (structuredSpectrum A c d) (ofComplex (z 0)) (ofComplex (z 1)) (ofComplex (z 2)) := by
  rw [projector_pair_contractions]
  unfold amplitudeEnergy
  have h₁ := congrArg ComplexPair.re (structured_contraction₁ A c d z)
  have h₂ := congrArg ComplexPair.re (structured_contraction₂ A c d z (congrFun (congrFun hA 0) 1))
  have h₃ := congrArg ComplexPair.re (structured_contraction₃ A c d z
    (congrFun (congrFun hA 0) 2) (congrFun (congrFun hA 1) 2))
  exact congrArg (fun x => x / 2) (congrArg₂ (· + ·) (congrArg₂ (· + ·) h₁ h₂) h₃)

lemma amplitudeEnergy_scale (t : ℝ) (k : SpectrumData ℝ) (z₁ z₂ z₃ : ComplexPair ℝ) :
    amplitudeEnergy (scaleSpectrum t k) z₁ z₂ z₃ = t * amplitudeEnergy k z₁ z₂ z₃ := by
  unfold amplitudeEnergy
  rw [amplitudeRow₁_scale,amplitudeRow₂_scale,amplitudeRow₃_scale]
  simp only [ComplexPair.scale]
  ring

lemma amplitudeEquations_half (k : SpectrumData ℝ) (z₁ z₂ z₃ : ComplexPair ℝ)
    (g₁ g₂ g₃ lam : ℝ)
    (he : AmplitudeEquations (scaleSpectrum 2 k) z₁ z₂ z₃ g₁ g₂ g₃ lam) :
    AmplitudeEquations k z₁ z₂ z₃ g₁ g₂ g₃ (lam/2) := by
  have h := amplitudeEquations_scale (1/2) _ _ _ _ _ _ _ _ he
  have hk : scaleSpectrum (1/2) (scaleSpectrum 2 k) = k := by
    cases k
    simp [scaleSpectrum,ComplexPair.scale,← mul_assoc]
  rw [hk] at h
  convert h using 1 <;> ring

/-- The doubled dual numerator is precisely p=〈P,R(P)〉. -/
theorem dual_amplitude_energy (A : Matrix (Fin 3) (Fin 3) ℝ)
    (c : Fin 3 → ℝ) (d z : Fin 3 → ℂ) (hA : A.det ≠ 0)
    (hΔ : ∀ i, blockDet (c i) (d i) ≠ 0) (hSym : A.IsSymm) :
    amplitudeEnergy (dualSpectrum A c d) (ofComplex (z 0)) (ofComplex (z 1)) (ofComplex (z 2)) =
      dualP (structuredEquiv A c d hA hΔ).symm z := by
  unfold dualSpectrum
  rw [amplitudeEnergy_scale]
  have h := structured_amplitude_energy A⁻¹ (inverseC c d) (inverseD c d) z hSym.inv
  change 2 * amplitudeEnergy _ _ _ _ = coordinatePair _ (structuredInverse A c d _)
  rw [structuredInverse_eq_linear]
  linear_combination -2 * h

/-- Every dual amplitude stationary point gives the exact projective vector
numerator equation; there is no division by p, λ, or even a in this implication. -/
theorem dual_amplitudes_imply_kernel (A : Matrix (Fin 3) (Fin 3) ℝ)
    (c : Fin 3 → ℝ) (d z : Fin 3 → ℂ) (hA : A.det ≠ 0)
    (hΔ : ∀ i, blockDet (c i) (d i) ≠ 0) (hSym : A.IsSymm) (lam : ℝ)
    (he : AmplitudeEquations (dualSpectrum A c d)
      (ofComplex (z 0)) (ofComplex (z 1)) (ofComplex (z 2))
      (dualWeights A 0) (dualWeights A 1) (dualWeights A 2) lam) :
    let R := (structuredEquiv A c d hA hΔ).symm
    coordinateMatrix ((dualA R z) • R (projectorCoordinates z) -
      (dualP R z) • R identityCoordinates) *ᵥ z = 0 := by
  let R := (structuredEquiv A c d hA hΔ).symm
  have hehalf := amplitudeEquations_half _ _ _ _ _ _ _ lam he
  have heig := (structured_eigen_iff_amplitudes A⁻¹ (inverseC c d) (inverseD c d) z
    (dualWeights A) (lam/2) (congrFun (congrFun hSym.inv 0) 1)
    (congrFun (congrFun hSym.inv 0) 2) (congrFun (congrFun hSym.inv 1) 2)).mpr hehalf
  have hp : dualP R z = (lam/2) * dualA R z := by
    have h := amplitude_energy_eigen _ _ _ _ _ _ _ _ he
    rw [dual_amplitude_energy A c d z hA hΔ hSym] at h
    simp only [normSq_ofComplex] at h
    rw [← dualA_eq_weight A c d hA hΔ z] at h
    change dualP R z = _ at h
    linear_combination h
  change coordinateAction z ((dualA R z) • R (projectorCoordinates z) -
    (dualP R z) • R identityCoordinates) = 0
  simp only [map_sub,map_smul,coordinateAction_apply]
  change (dualA R z) • (coordinateMatrix (structuredInverse A c d (projectorCoordinates z)) *ᵥ z) -
    (dualP R z) • (coordinateMatrix (structuredInverse A c d identityCoordinates) *ᵥ z) = 0
  rw [structuredInverse_eq_linear,heig,inverse_identity_diagonal,hp]
  ext i
  simp [Matrix.mulVec_diagonal,Complex.real_smul,Complex.ofReal_div,dualWeights]
  ring

#print axioms dual_amplitude_energy
#print axioms dual_amplitudes_imply_kernel
end W3.Operator
