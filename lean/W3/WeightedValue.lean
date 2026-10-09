import W3.WeightedSpectrum
import W3.WeightedOperatorBridge

noncomputable section
namespace W3.Weighted
open ComplexPair
open W3.Elimination
section Field
variable {K : Type*} [Field K] [CharZero K]

def amplitudeEnergy (k : SpectrumData K) (z₁ z₂ z₃ : ComplexPair K) : K :=
  ((amplitudeRow₁ k z₁ z₂ z₃).re + (amplitudeRow₂ k z₁ z₂ z₃).re +
    (amplitudeRow₃ k z₁ z₂ z₃).re) / 2

/-- Contracting the eigen-equation fixes the energy coefficient on every
support stratum; no nonzero component or nonzero energy is assumed. -/
theorem amplitude_energy_eigen (k : SpectrumData K) (z₁ z₂ z₃ : ComplexPair K)
    (g₁ g₂ g₃ lam : K) (he : AmplitudeEquations k z₁ z₂ z₃ g₁ g₂ g₃ lam) :
    amplitudeEnergy k z₁ z₂ z₃ =
      lam * (g₁ * normSq z₁ + g₂ * normSq z₂ + g₃ * normSq z₃) / 2 := by
  unfold amplitudeEnergy
  rw [he.1, he.2.1, he.2.2]
  dsimp only
  ring
end Field

section Ordered
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The spectrum quotient is exactly the rank-one operator energy divided
by the square of its diagonal weight. -/
theorem spectrumValue_amplitudePoint (w : WeightedData K) (z₁ z₂ z₃ : ComplexPair K)
    (h₁ : normSq z₁ ≠ 0) (h₂ : normSq z₂ ≠ 0) (h₃ : normSq z₃ ≠ 0) :
    spectrumValue w (amplitudePoint z₁ z₂ z₃) =
      amplitudeEnergy (toSpectrum w) z₁ z₂ z₃ /
        (w.g1 * normSq z₁ + w.g2 * normSq z₂ + w.g3 * normSq z₃) ^ 2 := by
  unfold spectrumValue amplitudePoint amplitudeEnergy weightedQuotient
  dsimp only
  rw [amplitudeRow₁_phase _ _ _ _ h₁ h₂ h₃,
    amplitudeRow₂_phase _ _ _ _ h₁ h₂ h₃, amplitudeRow₃_phase _ _ _ _ h₁ h₂ h₃]
  dsimp only
  rw [div_mul_eq_div_div]

/-- The represented candidate value agrees with the generalized-eigenvalue
normalization, rather than merely having the right stationary phases. -/
theorem spectrumValue_amplitude_eigen (w : WeightedData K) (z₁ z₂ z₃ : ComplexPair K)
    (lam : K) (h₁ : normSq z₁ ≠ 0) (h₂ : normSq z₂ ≠ 0) (h₃ : normSq z₃ ≠ 0)
    (hG : w.g1 * normSq z₁ + w.g2 * normSq z₂ + w.g3 * normSq z₃ ≠ 0)
    (he : AmplitudeEquations (toSpectrum w) z₁ z₂ z₃ w.g1 w.g2 w.g3 lam) :
    spectrumValue w (amplitudePoint z₁ z₂ z₃) =
      lam / (2 * (w.g1 * normSq z₁ + w.g2 * normSq z₂ + w.g3 * normSq z₃)) := by
  rw [spectrumValue_amplitudePoint w z₁ z₂ z₃ h₁ h₂ h₃,
    amplitude_energy_eigen _ _ _ _ _ _ _ _ he]
  field_simp [hG]

end Ordered

open ComplexConjugate Matrix W3.Operator
open scoped BigOperators

theorem projector_pair_contractions (X : Coordinates) (z : Fin 3 → ℂ) :
    coordinatePair (projectorCoordinates z) X =
      (conj (z 0) * (coordinateMatrix X *ᵥ z) 0).re +
      (conj (z 1) * (coordinateMatrix X *ᵥ z) 1).re +
      (conj (z 2) * (coordinateMatrix X *ᵥ z) 2).re := by
  simp [coordinatePair, projectorCoordinates, coordinateMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

/-- Actual Model energy equals the real-coordinate amplitude energy. -/
theorem primal_amplitude_energy (κ : W3.Couplings) (z : Fin 3 → ℂ) :
    coordinateEnergy κ (projectorCoordinates z) =
      amplitudeEnergy (structuredSpectrum (couplingMatrix κ) κ.c κ.d)
        (ofComplex (z 0)) (ofComplex (z 1)) (ofComplex (z 2)) := by
  rw [coordinateEnergy_eq_half_pair, projector_pair_contractions]
  unfold amplitudeEnergy
  have h₁ := congrArg ComplexPair.re (structured_contraction₁ (couplingMatrix κ) κ.c κ.d z)
  have h₂ := congrArg ComplexPair.re (structured_contraction₂ (couplingMatrix κ) κ.c κ.d z (by rfl))
  have h₃ := congrArg ComplexPair.re (structured_contraction₃ (couplingMatrix κ) κ.c κ.d z (by rfl) (by rfl))
  exact congrArg (fun x => x / 2) (congrArg₂ (· + ·) (congrArg₂ (· + ·) h₁ h₂) h₃)

end W3.Weighted
