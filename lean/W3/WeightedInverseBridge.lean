import W3.WeightedOperatorBridge
import W3.OperatorBridge

noncomputable section
namespace W3.Weighted
open ComplexConjugate Matrix
open W3.Operator
open scoped BigOperators

def inverseC (c : Fin 3 → ℝ) (d : Fin 3 → ℂ) (i : Fin 3) : ℝ := c i / blockDet (c i) (d i)
def inverseD (c : Fin 3 → ℝ) (d : Fin 3 → ℂ) (i : Fin 3) : ℂ :=
  (-(blockDet (c i) (d i))⁻¹ : ℝ) • d i

/-- The actual inverse operator remains in the identical Weinberg class.
The identity uses totalized inverses and does not assume away a zero energy. -/
theorem structuredInverse_eq_linear (A : Matrix (Fin 3) (Fin 3) ℝ)
    (c : Fin 3 → ℝ) (d : Fin 3 → ℂ) (x : Coordinates) :
    structuredInverse A c d x = structuredLinear A⁻¹ (inverseC c d) (inverseD c d) x := by
  apply Prod.ext
  · rfl
  · funext i
    apply Complex.ext <;>
      simp [structuredInverse, structuredLinear, inverseC, inverseD, inverseBlock,
        block, Complex.mul_re, Complex.mul_im, Complex.smul_re, Complex.smul_im, div_eq_mul_inv] <;> ring

theorem couplingMatrix_isSymm (κ : W3.Couplings) : (couplingMatrix κ).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem inverse_couplingMatrix_isSymm (κ : W3.Couplings) : (couplingMatrix κ)⁻¹.IsSymm :=
  (couplingMatrix_isSymm κ).inv

/-- Data scaling used in the dual quotient (the source uses twice the inverse coefficients). -/
def scaleSpectrum (t : ℝ) (k : SpectrumData ℝ) : SpectrumData ℝ :=
  ⟨t * k.a₁, t * k.a₂, t * k.a₃, t * k.e₁₂, t * k.e₁₃, t * k.e₂₃,
    ComplexPair.scale t k.d₁₂, ComplexPair.scale t k.d₁₃, ComplexPair.scale t k.d₂₃⟩

theorem amplitudeRow₁_scale (t : ℝ) (k : SpectrumData ℝ) (z₁ z₂ z₃ : ComplexPair ℝ) :
    amplitudeRow₁ (scaleSpectrum t k) z₁ z₂ z₃ = ComplexPair.scale t (amplitudeRow₁ k z₁ z₂ z₃) := by
  apply complexPair_ext <;> simp [amplitudeRow₁, amplitudeEdge, scaleSpectrum,
    ComplexPair.scale, ComplexPair.mul, ComplexPair.conj] <;> ring

theorem amplitudeRow₂_scale (t : ℝ) (k : SpectrumData ℝ) (z₁ z₂ z₃ : ComplexPair ℝ) :
    amplitudeRow₂ (scaleSpectrum t k) z₁ z₂ z₃ = ComplexPair.scale t (amplitudeRow₂ k z₁ z₂ z₃) := by
  apply complexPair_ext <;> simp [amplitudeRow₂, amplitudeEdge, scaleSpectrum,
    ComplexPair.scale, ComplexPair.mul, ComplexPair.conj] <;> ring

theorem amplitudeRow₃_scale (t : ℝ) (k : SpectrumData ℝ) (z₁ z₂ z₃ : ComplexPair ℝ) :
    amplitudeRow₃ (scaleSpectrum t k) z₁ z₂ z₃ = ComplexPair.scale t (amplitudeRow₃ k z₁ z₂ z₃) := by
  apply complexPair_ext <;> simp [amplitudeRow₃, amplitudeEdge, scaleSpectrum,
    ComplexPair.scale, ComplexPair.mul, ComplexPair.conj] <;> ring

theorem amplitudeEquations_scale (t : ℝ) (k : SpectrumData ℝ) (z₁ z₂ z₃ : ComplexPair ℝ)
    (g₁ g₂ g₃ lam : ℝ) (he : AmplitudeEquations k z₁ z₂ z₃ g₁ g₂ g₃ lam) :
    AmplitudeEquations (scaleSpectrum t k) z₁ z₂ z₃ g₁ g₂ g₃ (t * lam) := by
  unfold AmplitudeEquations at *
  rw [amplitudeRow₁_scale, amplitudeRow₂_scale, amplitudeRow₃_scale, he.1, he.2.1, he.2.2]
  refine ⟨?_, ?_, ?_⟩ <;> apply complexPair_ext <;> simp [ComplexPair.scale] <;> ring

def dualSpectrum (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ) (d : Fin 3 → ℂ) : SpectrumData ℝ :=
  scaleSpectrum 2 (structuredSpectrum A⁻¹ (inverseC c d) (inverseD c d))

def dualWeights (A : Matrix (Fin 3) (Fin 3) ℝ) : Fin 3 → ℝ := A⁻¹ *ᵥ (fun _ => 1)

/-- The pole-excluded dual kernel equation is a genuine generalized eigenvalue
problem. The diagonal weights are exactly R(I), including negative weights. -/
theorem inverse_kernel_implies_eigen (A : Matrix (Fin 3) (Fin 3) ℝ)
    (c : Fin 3 → ℝ) (d z : Fin 3 → ℂ) (a p : ℝ) (ha : a ≠ 0)
    (hk : coordinateMatrix (a • structuredInverse A c d (projectorCoordinates z) -
      p • structuredInverse A c d identityCoordinates) *ᵥ z = 0) :
    coordinateMatrix (structuredLinear A⁻¹ (inverseC c d) (inverseD c d) (projectorCoordinates z)) *ᵥ z =
      fun i => (((p / a) * dualWeights A i : ℝ) : ℂ) * z i := by
  change coordinateAction z (a • structuredInverse A c d (projectorCoordinates z) -
    p • structuredInverse A c d identityCoordinates) = 0 at hk
  simp only [map_sub, map_smul, coordinateAction_apply, inverse_identity_diagonal,
    ] at hk
  rw [← structuredInverse_eq_linear]
  funext i
  have hi := congrFun hk i
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, Complex.real_smul, mulVec_diagonal] at hi
  apply mul_left_cancel₀ (show (a : ℂ) ≠ 0 by exact_mod_cast ha)
  simp only [Complex.ofReal_mul, Complex.ofReal_div]
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  field_simp [hac]
  change (a : ℂ) * _ - (p : ℂ) * ((dualWeights A i : ℂ) * z i) = 0 at hi
  linear_combination hi

/-- Concrete charged projector/kernel stationarity reaches the same common
spectrum with exactly α'=2Gii, e'=2(Gij+cR), d'=2dR. -/
theorem inverse_kernel_implies_amplitudes (A : Matrix (Fin 3) (Fin 3) ℝ)
    (c : Fin 3 → ℝ) (d z : Fin 3 → ℂ) (a p : ℝ) (ha : a ≠ 0) (hA : A.IsSymm)
    (hk : coordinateMatrix (a • structuredInverse A c d (projectorCoordinates z) -
      p • structuredInverse A c d identityCoordinates) *ᵥ z = 0) :
    AmplitudeEquations (dualSpectrum A c d) (ofComplex (z 0)) (ofComplex (z 1)) (ofComplex (z 2))
      (dualWeights A 0) (dualWeights A 1) (dualWeights A 2) (2 * (p / a)) := by
  apply amplitudeEquations_scale
  apply structured_eigen_implies_amplitudes A⁻¹ (inverseC c d) (inverseD c d) z (dualWeights A) (p / a)
  · exact congrFun (congrFun hA.inv 0) 1
  · exact congrFun (congrFun hA.inv 0) 2
  · exact congrFun (congrFun hA.inv 1) 2
  · exact inverse_kernel_implies_eigen A c d z a p ha hk

end W3.Weighted
