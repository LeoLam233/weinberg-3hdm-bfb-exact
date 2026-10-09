import W3.WeightedAmplitude
import W3.OperatorModel

/-! Direct bridge from the concrete Hermitian matrix action to the common
spectrum's real-coordinate amplitude equations. -/
noncomputable section
namespace W3.Weighted
open ComplexConjugate Matrix
open W3.Operator
open scoped BigOperators

def ofComplex (z : ℂ) : ComplexPair ℝ := ⟨z.re, z.im⟩

@[simp] theorem ofComplex_mul (z w : ℂ) : ofComplex (z * w) = ComplexPair.mul (ofComplex z) (ofComplex w) := rfl
@[simp] theorem ofComplex_conj (z : ℂ) : ofComplex (conj z) = ComplexPair.conj (ofComplex z) := rfl
@[simp] theorem ofComplex_norm (z : ℂ) : ComplexPair.normSq (ofComplex z) = Complex.normSq z := by
  simp [ofComplex, ComplexPair.normSq, Complex.normSq_apply, pow_two]

def structuredSpectrum (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ) (d : Fin 3 → ℂ) : SpectrumData ℝ :=
  ⟨A 0 0, A 1 1, A 2 2, A 0 1 + c 0, A 0 2 + c 1, A 1 2 + c 2,
    ofComplex (d 0), ofComplex (d 1), ofComplex (d 2)⟩

/-- Contracted component one of the concrete operator equation, with no
support assumption. This polynomial identity includes b+c and complex d. -/
theorem structured_contraction₁ (A : Matrix (Fin 3) (Fin 3) ℝ)
    (c : Fin 3 → ℝ) (d z : Fin 3 → ℂ) :
    ofComplex (conj (z 0) * (coordinateMatrix (structuredLinear A c d (projectorCoordinates z)) *ᵥ z) 0) =
      amplitudeRow₁ (structuredSpectrum A c d) (ofComplex (z 0)) (ofComplex (z 1)) (ofComplex (z 2)) := by
  apply complexPair_ext <;>
    simp [ofComplex, amplitudeRow₁, structuredSpectrum, amplitudeEdge,
      ComplexPair.normSq, ComplexPair.mul, ComplexPair.conj, coordinateMatrix,
      structuredLinear, projectorCoordinates, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, block, Complex.mul_re, Complex.mul_im, Complex.normSq_apply] <;> ring

theorem structured_contraction₂ (A : Matrix (Fin 3) (Fin 3) ℝ)
    (c : Fin 3 → ℝ) (d z : Fin 3 → ℂ) (h₁₀ : A 1 0 = A 0 1) :
    ofComplex (conj (z 1) * (coordinateMatrix (structuredLinear A c d (projectorCoordinates z)) *ᵥ z) 1) =
      amplitudeRow₂ (structuredSpectrum A c d) (ofComplex (z 0)) (ofComplex (z 1)) (ofComplex (z 2)) := by
  apply complexPair_ext <;>
    simp [ofComplex, amplitudeRow₂, structuredSpectrum, amplitudeEdge,
      ComplexPair.normSq, ComplexPair.mul, ComplexPair.conj, coordinateMatrix,
      structuredLinear, projectorCoordinates, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, block, Complex.mul_re, Complex.mul_im, Complex.normSq_apply, h₁₀] <;> ring

theorem structured_contraction₃ (A : Matrix (Fin 3) (Fin 3) ℝ)
    (c : Fin 3 → ℝ) (d z : Fin 3 → ℂ) (h₂₀ : A 2 0 = A 0 2) (h₂₁ : A 2 1 = A 1 2) :
    ofComplex (conj (z 2) * (coordinateMatrix (structuredLinear A c d (projectorCoordinates z)) *ᵥ z) 2) =
      amplitudeRow₃ (structuredSpectrum A c d) (ofComplex (z 0)) (ofComplex (z 1)) (ofComplex (z 2)) := by
  apply complexPair_ext <;>
    simp [ofComplex, amplitudeRow₃, structuredSpectrum, amplitudeEdge,
      ComplexPair.normSq, ComplexPair.mul, ComplexPair.conj, coordinateMatrix,
      structuredLinear, projectorCoordinates, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, block, Complex.mul_re, Complex.mul_im, Complex.normSq_apply, h₂₀, h₂₁] <;> ring

/-- Genuine matrix eigenvector stationarity implies the coordinate amplitude
system, even on faces with missing components. -/
theorem structured_eigen_implies_amplitudes (A : Matrix (Fin 3) (Fin 3) ℝ)
    (c : Fin 3 → ℝ) (d z : Fin 3 → ℂ) (g : Fin 3 → ℝ) (lam : ℝ)
    (h₁₀ : A 1 0 = A 0 1) (h₂₀ : A 2 0 = A 0 2) (h₂₁ : A 2 1 = A 1 2)
    (he : coordinateMatrix (structuredLinear A c d (projectorCoordinates z)) *ᵥ z =
      fun i => ((lam * g i : ℝ) : ℂ) * z i) :
    AmplitudeEquations (structuredSpectrum A c d)
      (ofComplex (z 0)) (ofComplex (z 1)) (ofComplex (z 2)) (g 0) (g 1) (g 2) lam := by
  have hc (i : Fin 3) :
      ofComplex (conj (z i) * (coordinateMatrix (structuredLinear A c d (projectorCoordinates z)) *ᵥ z) i) =
      ⟨lam * g i * ComplexPair.normSq (ofComplex (z i)), 0⟩ := by
    rw [he]
    apply complexPair_ext <;> simp [ofComplex, ComplexPair.normSq, Complex.mul_re, Complex.mul_im] <;> ring
  unfold AmplitudeEquations
  rw [← structured_contraction₁, ← structured_contraction₂ A c d z h₁₀,
    ← structured_contraction₃ A c d z h₂₀ h₂₁]
  exact ⟨hc 0, hc 1, hc 2⟩

/-- Specialization to the exact full complex Weinberg operator encoded in Model. -/
theorem primal_eigen_implies_amplitudes (κ : W3.Couplings) (z : Fin 3 → ℂ) (lam : ℝ)
    (he : coordinateMatrix (couplingOperator κ (projectorCoordinates z)) *ᵥ z = lam • z) :
    AmplitudeEquations (structuredSpectrum (couplingMatrix κ) κ.c κ.d)
      (ofComplex (z 0)) (ofComplex (z 1)) (ofComplex (z 2)) 1 1 1 lam := by
  apply structured_eigen_implies_amplitudes (couplingMatrix κ) κ.c κ.d z (fun _ => 1) lam
    (by rfl) (by rfl) (by rfl)
  change coordinateMatrix (couplingOperator κ (projectorCoordinates z)) *ᵥ z = _
  rw [he]
  funext i
  simp [Complex.real_smul]


lemma ofComplex_injective : Function.Injective ofComplex := by
  intro z w h
  apply Complex.ext
  · exact congrArg ComplexPair.re h
  · exact congrArg ComplexPair.im h

/-- Missing amplitudes yield a zero component of the structured operator
applied to their rank-one projector, including nonzero mixed diagonal entries. -/
theorem structured_zero_component (A : Matrix (Fin 3) (Fin 3) ℝ)
    (c : Fin 3 → ℝ) (d z : Fin 3 → ℂ) (i : Fin 3) (hi : z i = 0) :
    (coordinateMatrix (structuredLinear A c d (projectorCoordinates z)) *ᵥ z) i = 0 := by
  fin_cases i <;> dsimp at hi <;>
    simp [coordinateMatrix, structuredLinear, projectorCoordinates, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three, block, hi]

/-- The concrete eigenvector equation is equivalent to the contracted
amplitude system, without a full-support assumption. -/
theorem structured_eigen_iff_amplitudes (A : Matrix (Fin 3) (Fin 3) ℝ)
    (c : Fin 3 → ℝ) (d z : Fin 3 → ℂ) (g : Fin 3 → ℝ) (lam : ℝ)
    (h₁₀ : A 1 0 = A 0 1) (h₂₀ : A 2 0 = A 0 2) (h₂₁ : A 2 1 = A 1 2) :
    (coordinateMatrix (structuredLinear A c d (projectorCoordinates z)) *ᵥ z =
      fun i => ((lam * g i : ℝ) : ℂ) * z i) ↔
    AmplitudeEquations (structuredSpectrum A c d)
      (ofComplex (z 0)) (ofComplex (z 1)) (ofComplex (z 2)) (g 0) (g 1) (g 2) lam := by
  constructor
  · exact structured_eigen_implies_amplitudes A c d z g lam h₁₀ h₂₀ h₂₁
  · intro he
    have hc (i : Fin 3) :
        ofComplex (conj (z i) * (coordinateMatrix (structuredLinear A c d (projectorCoordinates z)) *ᵥ z) i) =
        ⟨lam * g i * ComplexPair.normSq (ofComplex (z i)), 0⟩ := by
      fin_cases i
      · exact (structured_contraction₁ A c d z).trans he.1
      · exact (structured_contraction₂ A c d z h₁₀).trans he.2.1
      · exact (structured_contraction₃ A c d z h₂₀ h₂₁).trans he.2.2
    funext i
    by_cases hz : z i = 0
    · simp only [hz, mul_zero]
      exact structured_zero_component A c d z i hz
    · apply mul_left_cancel₀ (show conj (z i) ≠ 0 from by simpa using hz)
      apply ofComplex_injective
      rw [hc i]
      apply complexPair_ext <;> simp [ofComplex, ComplexPair.normSq, Complex.mul_re, Complex.mul_im] <;> ring

end W3.Weighted
