import W3.OperatorStationarity
import W3.OperatorRank
import W3.PhysicalFields

/-! Unconditional stationary-stratum consequences of an actual global minimum.
Finite-spectrum coverage and generic denominator exclusions remain separate obligations. -/
noncomputable section
namespace W3.Operator
open ComplexConjugate Matrix
open scoped BigOperators ComplexOrder

/-- The field-gradient equation in the source's actual 2×3 matrix representation. -/
theorem normalized_minimum_matrix_stationarity (κ : W3.Couplings) (φ : W3.Fields)
    (hφ : ‖φ‖ = 1)
    (hmin : ∀ ψ : W3.Fields, ‖ψ‖ = 1 → W3.quartic κ φ ≤ W3.quartic κ ψ) :
    W3.fieldMatrix φ * coordinateMatrix (couplingOperator κ (fieldCoordinates φ)) =
      (2 * W3.quartic κ φ) • W3.fieldMatrix φ := by
  have h := normalized_minimum_field_stationarity κ φ hφ hmin
  ext k i
  exact congrArg (fun ψ : W3.Fields => ψ (k,i)) h

/-- Gram annihilation of L(K)−2f(K)I at every normalized minimum. -/
theorem normalized_minimum_gram_stationarity (κ : W3.Couplings) (φ : W3.Fields)
    (hφ : ‖φ‖ = 1)
    (hmin : ∀ ψ : W3.Fields, ‖ψ‖ = 1 → W3.quartic κ φ ≤ W3.quartic κ ψ) :
    W3.gram φ * (coordinateMatrix (couplingOperator κ (fieldCoordinates φ)) -
      (2 * W3.quartic κ φ) • 1) = 0 := by
  rw [W3.gram_matrix, Matrix.mul_assoc, Matrix.mul_sub,
    normalized_minimum_matrix_stationarity κ φ hφ hmin,
    Matrix.mul_smul, Matrix.mul_one, sub_self, Matrix.mul_zero]

lemma shifted_operator_hermitian (κ : W3.Couplings) (φ : W3.Fields) :
    (coordinateMatrix (couplingOperator κ (fieldCoordinates φ)) -
      (2 * W3.quartic κ φ) • 1).IsHermitian :=
  (coordinateMatrix_hermitian _).sub (Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint]))

/-- The source's rank-two normal equation (29), derived rather than assumed. -/
theorem normalized_minimum_rank_two (κ : W3.Couplings) (φ : W3.Fields)
    (hφ : ‖φ‖ = 1)
    (hmin : ∀ ψ : W3.Fields, ‖ψ‖ = 1 → W3.quartic κ φ ≤ W3.quartic κ ψ)
    (hrank : (W3.gram φ).rank = 2) :
    ∃ (z : Fin 3 → ℂ) (μ : ℝ),
      (∑ i, Complex.normSq (z i)) = 1 ∧ W3.gram φ *ᵥ z = 0 ∧
      coordinateMatrix (couplingOperator κ (fieldCoordinates φ)) =
        (2 * W3.quartic κ φ) • 1 + μ • projector z := by
  obtain ⟨z,μ,hz,hker,hX⟩ := rank_two_hermitian_normal_unit (W3.gram φ)
    (coordinateMatrix (couplingOperator κ (fieldCoordinates φ)) - (2 * W3.quartic κ φ) • 1)
    hrank (shifted_operator_hermitian κ φ) (normalized_minimum_gram_stationarity κ φ hφ hmin)
  refine ⟨z,μ,hz,hker,?_⟩
  exact (sub_eq_iff_eq_add.mp hX).trans (add_comm _ _)

/-- The source's neutral projective eigen-equation on the actual support. -/
theorem normalized_minimum_rank_one (κ : W3.Couplings) (φ : W3.Fields)
    (hφ : ‖φ‖ = 1)
    (hmin : ∀ ψ : W3.Fields, ‖ψ‖ = 1 → W3.quartic κ φ ≤ W3.quartic κ ψ)
    (hrank : (W3.gram φ).rank = 1) :
    ∃ z : Fin 3 → ℂ, (∑ i, Complex.normSq (z i)) = 1 ∧ W3.gram φ = projector z ∧
      coordinateMatrix (couplingOperator κ (fieldCoordinates φ)) *ᵥ z =
        (2 * W3.quartic κ φ) • z := by
  have htr : (W3.gram φ).trace = 1 := by simp [W3.gram_trace, hφ]
  obtain ⟨z,hz,hP⟩ := rank_one_hermitian_trace_one (W3.gram φ)
    (W3.gram_posSemidef φ).isHermitian hrank htr
  refine ⟨z,hz,hP,?_⟩
  have hker := projector_annihilation
    (coordinateMatrix (couplingOperator κ (fieldCoordinates φ)) - (2 * W3.quartic κ φ) • 1)
    (shifted_operator_hermitian κ φ) z hz (by
      rw [← hP]
      exact normalized_minimum_gram_stationarity κ φ hφ hmin)
  simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    sub_eq_zero] using hker

lemma normalized_gram_rank_cases (φ : W3.Fields) (hφ : ‖φ‖ = 1) :
    (W3.gram φ).rank = 1 ∨ (W3.gram φ).rank = 2 := by
  have hle : (W3.gram φ).rank ≤ 2 := by
    rw [W3.gram_matrix]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)
  have hne : (W3.gram φ).rank ≠ 0 := by
    intro hz
    have hrange : LinearMap.range (W3.gram φ).mulVecLin = ⊥ :=
      Submodule.finrank_eq_zero.mp hz
    have hzero : W3.gram φ = 0 := by
      ext i j
      have hm : (W3.gram φ).mulVecLin (Pi.single j 1) = 0 := by
        have hm : (W3.gram φ).mulVecLin (Pi.single j 1) ∈
            LinearMap.range (W3.gram φ).mulVecLin := ⟨Pi.single j 1, rfl⟩
        simpa [hrange] using hm
      have h := congrFun hm i
      simpa using h
    have htr := W3.gram_trace φ
    rw [hzero, Matrix.trace_zero, hφ] at htr
    norm_num at htr
  omega

/-- Exhaustive stationary strata for the actual normalized physical minimum.
This theorem stops before the independent finite-spectrum elimination argument. -/
theorem normalized_minimum_stationary_strata (κ : W3.Couplings) (φ : W3.Fields)
    (hφ : ‖φ‖ = 1)
    (hmin : ∀ ψ : W3.Fields, ‖ψ‖ = 1 → W3.quartic κ φ ≤ W3.quartic κ ψ) :
    (∃ z : Fin 3 → ℂ, (∑ i, Complex.normSq (z i)) = 1 ∧ W3.gram φ = projector z ∧
      coordinateMatrix (couplingOperator κ (fieldCoordinates φ)) *ᵥ z =
        (2 * W3.quartic κ φ) • z) ∨
    (∃ (z : Fin 3 → ℂ) (μ : ℝ),
      (∑ i, Complex.normSq (z i)) = 1 ∧ W3.gram φ *ᵥ z = 0 ∧
      coordinateMatrix (couplingOperator κ (fieldCoordinates φ)) =
        (2 * W3.quartic κ φ) • 1 + μ • projector z) := by
  rcases normalized_gram_rank_cases φ hφ with h1 | h2
  · exact Or.inl (normalized_minimum_rank_one κ φ hφ hmin h1)
  · exact Or.inr (normalized_minimum_rank_two κ φ hφ hmin h2)

#print axioms normalized_minimum_rank_two
#print axioms normalized_minimum_rank_one
#print axioms normalized_minimum_stationary_strata
end W3.Operator
