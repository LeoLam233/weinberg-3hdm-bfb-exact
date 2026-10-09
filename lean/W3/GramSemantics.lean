import W3.GramFactor
import W3.OperatorStrata
import W3.ActualStability

/-! Exact equivalence with the original statement's normalized physical Gram
domain: Hermitian PSD, trace one, rank at most two. -/
noncomputable section
namespace W3
open Matrix Operator RealModel Infinitesimal
open scoped ComplexOrder

def PhysicalGram (K : Matrix (Fin 3) (Fin 3) ℂ) : Prop :=
  K.IsHermitian ∧ K.PosSemidef ∧ K.trace=1 ∧ K.rank≤2

def gramQuartic (κ : Couplings) (K : Matrix (Fin 3) (Fin 3) ℂ) : ℝ :=
  coordinateEnergy κ (matrixCoordinates K)

lemma gramQuartic_gram (κ : Couplings) (φ : Fields) : gramQuartic κ (gram φ) = quartic κ φ := by
  rw [gramQuartic,← coordinateMatrix_fieldCoordinates,matrixCoordinates_coordinateMatrix]
  rfl

lemma gram_physical (φ : Fields) (hφ : ‖φ‖=1) : PhysicalGram (gram φ) := by
  refine ⟨(gram_posSemidef φ).isHermitian,gram_posSemidef φ,?_,?_⟩
  · simp [gram_trace,hφ]
  · rw [gram_matrix]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)

/-- No extra Gram matrices or lost charge-breaking directions occur. -/
theorem physicalGram_iff_fields (K : Matrix (Fin 3) (Fin 3) ℂ) :
    PhysicalGram K ↔ ∃ φ : Fields, ‖φ‖=1 ∧ gram φ=K := by
  constructor
  · rintro ⟨_,hPSD,htr,hrank⟩
    have hdet : K.det=0 := by
      by_contra hn
      have hh := Matrix.rank_of_det_ne_zero hn
      norm_num at hh
      omega
    obtain ⟨φ,hK,hn⟩ := exists_normalized_gram_factor K hPSD hdet htr
    exact ⟨φ,hn,hK⟩
  · rintro ⟨φ,hφ,rfl⟩
    exact gram_physical φ hφ

/-- Exact minimum on the source's matrix domain, not merely on a chosen support. -/
theorem realMinimum_gram (κ : Parameters ℝ) :
    (∀ K, PhysicalGram K → realMinimum κ ≤ gramQuartic (couplings κ) K) ∧
    ∃ K,PhysicalGram K ∧ gramQuartic (couplings κ) K=realMinimum κ := by
  constructor
  · intro K hK
    obtain ⟨φ,hφ,rfl⟩ := (physicalGram_iff_fields K).mp hK
    rw [gramQuartic_gram]
    exact realMinimum_le_field κ φ hφ
  · refine ⟨gram (fields (realMinimumPoint κ)),gram_physical _ (realMinimum_field_norm κ),?_⟩
    rw [gramQuartic_gram,realMinimum_field_value]

/-- Weak/strict tests on exactly D from equation (2). -/
theorem gram_stability_equivalences (κ : Parameters ℝ) :
    ((∀ K,PhysicalGram K→0≤gramQuartic (couplings κ) K) ↔ 0≤realMinimum κ) ∧
    ((∀ K,PhysicalGram K→0<gramQuartic (couplings κ) K) ↔ 0<realMinimum κ) := by
  obtain ⟨hmin,K,hK,hE⟩ := realMinimum_gram κ
  constructor
  · constructor
    · intro h
      simpa [hE] using h K hK
    · intro h K hK
      exact h.trans (hmin K hK)
  · constructor
    · intro h
      simpa [hE] using h K hK
    · intro h K hK
      exact h.trans_le (hmin K hK)

#print axioms physicalGram_iff_fields
#print axioms realMinimum_gram
end W3
