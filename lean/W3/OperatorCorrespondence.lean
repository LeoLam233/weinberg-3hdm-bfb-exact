import W3.OperatorSpectrumBridge
import W3.WeightedCorrespondence

/-! Exact passage from weighted phase points to concrete complex projectors. -/
noncomputable section
namespace W3.Operator
open Matrix ComplexConjugate
open W3.Weighted W3.Elimination
open scoped BigOperators

def VectorMatches (x : SpectrumPoint ℝ) (z : Fin 3 → ℂ) : Prop :=
  PointMatches x (ofComplex (z 0)) (ofComplex (z 1)) (ofComplex (z 2))

lemma ofComplex_injective : Function.Injective ofComplex := by
  intro z w h
  exact Complex.ext (congrArg ComplexPair.re h) (congrArg ComplexPair.im h)

lemma ofComplex_squaredEntry (z w : ℂ) :
    squaredEntry (ofComplex z) (ofComplex w) = ofComplex ((z * conj w) ^ 2) := by
  apply W3.Weighted.complexPair_ext <;>
    simp [squaredEntry,ofComplex,ComplexPair.mul,ComplexPair.conj,Complex.mul_re,Complex.mul_im,pow_two] <;> ring

/-- The same represented phase point has exactly the sign-independent
coordinates used by all charged scalar tests. -/
theorem vectorMatches_quadratic_eq (x : SpectrumPoint ℝ) (z w : Fin 3 → ℂ)
    (hz : VectorMatches x z) (hw : VectorMatches x w) :
    QuadraticCoordinatesEq (projectorCoordinates z) (projectorCoordinates w) := by
  have h₀ : Complex.normSq (z 0) = Complex.normSq (w 0) := by
    simpa only [normSq_ofComplex] using hz.1.symm.trans hw.1
  have h₁ : Complex.normSq (z 1) = Complex.normSq (w 1) := by
    simpa only [normSq_ofComplex] using hz.2.1.symm.trans hw.2.1
  have h₂ : Complex.normSq (z 2) = Complex.normSq (w 2) := by
    simpa only [normSq_ofComplex] using hz.2.2.1.symm.trans hw.2.2.1
  have h01 : (z 0 * conj (z 1)) ^ 2 = (w 0 * conj (w 1)) ^ 2 := by
    apply ofComplex_injective
    rw [← ofComplex_squaredEntry,← ofComplex_squaredEntry]
    exact hz.2.2.2.1.trans hw.2.2.2.1.symm
  have h02 : (z 0 * conj (z 2)) ^ 2 = (w 0 * conj (w 2)) ^ 2 := by
    apply ofComplex_injective
    rw [← ofComplex_squaredEntry,← ofComplex_squaredEntry]
    exact hz.2.2.2.2.1.trans hw.2.2.2.2.1.symm
  have h12 : (z 1 * conj (z 2)) ^ 2 = (w 1 * conj (w 2)) ^ 2 := by
    apply ofComplex_injective
    rw [← ofComplex_squaredEntry,← ofComplex_squaredEntry]
    exact hz.2.2.2.2.2.trans hw.2.2.2.2.2.symm
  constructor
  · funext i
    fin_cases i
    · exact h₀
    · exact h₁
    · exact h₂
  · intro i
    fin_cases i
    · exact ⟨by simpa [projectorCoordinates,Complex.normSq_mul,Complex.normSq_conj,h₀,h₁],h01⟩
    · exact ⟨by simpa [projectorCoordinates,Complex.normSq_mul,Complex.normSq_conj,h₀,h₂],h02⟩
    · exact ⟨by simpa [projectorCoordinates,Complex.normSq_mul,Complex.normSq_conj,h₁,h₂],h12⟩

def operatorPrimalData (κ : W3.Couplings) : WeightedData ℝ :=
  weightedDataOf (structuredSpectrum (couplingMatrix κ) κ.c κ.d) (fun _ => 1)

lemma vectorMatches_primal_value (κ : W3.Couplings) (x : SpectrumPoint ℝ) (z : Fin 3 → ℂ)
    (hmatch : VectorMatches x z) (hunit : ∑ i, Complex.normSq (z i) = 1) :
    spectrumValue (operatorPrimalData κ) x = coordinateEnergy κ (projectorCoordinates z) := by
  rw [pointMatches_value _ _ _ _ _ hmatch]
  rw [show toSpectrum (operatorPrimalData κ) = structuredSpectrum (couplingMatrix κ) κ.c κ.d from toSpectrum_weightedDataOf _ _]
  rw [← primal_amplitude_energy]
  have hn : (ofComplex (z 0)).normSq+(ofComplex (z 1)).normSq+(ofComplex (z 2)).normSq = 1 := by
    simpa [Fin.sum_univ_three] using hunit
  change coordinateEnergy κ (projectorCoordinates z) /
    (1*(ofComplex (z 0)).normSq+1*(ofComplex (z 1)).normSq+1*(ofComplex (z 2)).normSq)^2 = _
  simp only [one_mul,hn,one_pow,div_one]

lemma vectorMatches_dual_value (A : Matrix (Fin 3) (Fin 3) ℝ)
    (c : Fin 3 → ℝ) (d : Fin 3 → ℂ) (hA : A.det ≠ 0)
    (hΔ : ∀ i, blockDet (c i) (d i) ≠ 0) (hSym : A.IsSymm)
    (x : SpectrumPoint ℝ) (z : Fin 3 → ℂ) (hmatch : VectorMatches x z) :
    spectrumValue (operatorDualData A c d) x =
      dualP (structuredEquiv A c d hA hΔ).symm z / dualA (structuredEquiv A c d hA hΔ).symm z ^ 2 := by
  rw [pointMatches_value _ _ _ _ _ hmatch]
  rw [show toSpectrum (operatorDualData A c d) = dualSpectrum A c d from toSpectrum_weightedDataOf _ _]
  rw [dual_amplitude_energy A c d z hA hΔ hSym,dualA_eq_weight]
  simp only [normSq_ofComplex,operatorDualData,weightedDataOf]

#print axioms vectorMatches_quadratic_eq
#print axioms vectorMatches_dual_value
end W3.Operator
