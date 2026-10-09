import W3.WeightedAlgebra

noncomputable section
namespace W3.Weighted
section Pair
variable {K : Type*} [Field K]

def pairN₁ (A B h g₁ g₂ : K) : K := B * g₁ - h * g₂
def pairN₂ (A B h g₁ g₂ : K) : K := A * g₂ - h * g₁
def pairW (A B h g₁ g₂ : K) : K := B * g₁ ^ 2 - 2 * h * g₁ * g₂ + A * g₂ ^ 2
def pairDet (A B h : K) : K := A * B - h ^ 2

def PairRadialEquations (A B h g₁ g₂ r₁ r₂ ν : K) : Prop :=
  A * r₁ + h * r₂ = ν * (g₁ * r₁ + g₂ * r₂) * g₁ ∧
  h * r₁ + B * r₂ = ν * (g₁ * r₁ + g₂ * r₂) * g₂

theorem pair_weight_identity (A B h g₁ g₂ : K) :
    g₁ * pairN₁ A B h g₁ g₂ + g₂ * pairN₂ A B h g₁ g₂ = pairW A B h g₁ g₂ := by
  unfold pairN₁ pairN₂ pairW
  ring

/-- Pair-support coverage does not divide by det B. Zero-energy stationary
points are included even when the two-by-two matrix is singular. -/
theorem pair_stationary_reconstruction (A B h g₁ g₂ r₁ r₂ ν : K)
    (hW : pairW A B h g₁ g₂ ≠ 0) (hG : g₁ * r₁ + g₂ * r₂ ≠ 0)
    (hn : r₁ + r₂ = 1) (hs : PairRadialEquations A B h g₁ g₂ r₁ r₂ ν) :
    pairN₁ A B h g₁ g₂ + pairN₂ A B h g₁ g₂ ≠ 0 ∧
    r₁ = pairN₁ A B h g₁ g₂ / (pairN₁ A B h g₁ g₂ + pairN₂ A B h g₁ g₂) ∧
    r₂ = pairN₂ A B h g₁ g₂ / (pairN₁ A B h g₁ g₂ + pairN₂ A B h g₁ g₂) ∧
    ν = pairDet A B h / pairW A B h g₁ g₂ := by
  have he : pairN₂ A B h g₁ g₂ * r₁ - pairN₁ A B h g₁ g₂ * r₂ = 0 := by
    unfold pairN₁ pairN₂
    linear_combination g₂ * hs.1 - g₁ * hs.2
  have h₁ : r₁ * (pairN₁ A B h g₁ g₂ + pairN₂ A B h g₁ g₂) = pairN₁ A B h g₁ g₂ := by
    linear_combination pairN₁ A B h g₁ g₂ * hn + he
  have h₂ : r₂ * (pairN₁ A B h g₁ g₂ + pairN₂ A B h g₁ g₂) = pairN₂ A B h g₁ g₂ := by
    linear_combination pairN₂ A B h g₁ g₂ * hn - he
  have hN : pairN₁ A B h g₁ g₂ + pairN₂ A B h g₁ g₂ ≠ 0 := by
    intro hz
    have hz₁ : pairN₁ A B h g₁ g₂ = 0 := by simpa [hz] using h₁.symm
    have hz₂ : pairN₂ A B h g₁ g₂ = 0 := by simpa [hz] using h₂.symm
    apply hW
    rw [← pair_weight_identity, hz₁, hz₂]
    ring
  refine ⟨hN, (eq_div_iff hN).mpr h₁, (eq_div_iff hN).mpr h₂, ?_⟩
  apply (eq_div_iff hW).mpr
  apply mul_left_cancel₀ hG
  unfold pairW pairDet
  linear_combination -(B * g₁ - h * g₂) * hs.1 - (A * g₂ - h * g₁) * hs.2

/-- Every admissible pair formula is genuinely stationary, including det B=0. -/
theorem pair_reconstruction_stationary (A B h g₁ g₂ : K)
    (hW : pairW A B h g₁ g₂ ≠ 0)
    (hN : pairN₁ A B h g₁ g₂ + pairN₂ A B h g₁ g₂ ≠ 0) :
    PairRadialEquations A B h g₁ g₂
      (pairN₁ A B h g₁ g₂ / (pairN₁ A B h g₁ g₂ + pairN₂ A B h g₁ g₂))
      (pairN₂ A B h g₁ g₂ / (pairN₁ A B h g₁ g₂ + pairN₂ A B h g₁ g₂))
      (pairDet A B h / pairW A B h g₁ g₂) := by
  constructor <;> field_simp [hN, hW] <;> unfold pairN₁ pairN₂ pairDet pairW <;> ring

theorem pair_reconstruction_weight (A B h g₁ g₂ : K)
    (hN : pairN₁ A B h g₁ g₂ + pairN₂ A B h g₁ g₂ ≠ 0) :
    g₁ * (pairN₁ A B h g₁ g₂ / (pairN₁ A B h g₁ g₂ + pairN₂ A B h g₁ g₂)) +
    g₂ * (pairN₂ A B h g₁ g₂ / (pairN₁ A B h g₁ g₂ + pairN₂ A B h g₁ g₂)) =
    pairW A B h g₁ g₂ / (pairN₁ A B h g₁ g₂ + pairN₂ A B h g₁ g₂) := by
  rw [← pair_weight_identity]
  ring

/-- Radial stationarity determines the quotient value. -/
theorem pair_stationary_value (A B h g₁ g₂ r₁ r₂ ν : K)
    (hG : g₁ * r₁ + g₂ * r₂ ≠ 0)
    (hs : PairRadialEquations A B h g₁ g₂ r₁ r₂ ν) :
    ν = (A * r₁ ^ 2 + 2 * h * r₁ * r₂ + B * r₂ ^ 2) /
      (g₁ * r₁ + g₂ * r₂) ^ 2 := by
  apply (eq_div_iff (pow_ne_zero 2 hG)).mpr
  linear_combination -r₁ * hs.1 - r₂ * hs.2
end Pair
end W3.Weighted
