import W3.WeightedRadial
import W3.WeightedHalfAngle

noncomputable section
namespace W3.Weighted
section Field
variable {K : Type*} [Field K] [CharZero K]

/-- The current denominator in equation (11). -/
def currentDen (k : SpectrumData K) (q v : ComplexPair K) : K :=
  (edge₂₃ k q v).im - (edge₁₃ k v).im + (edge₁₂ k q).im

/-- Complete algebraic stationary system on the full-support stratum. -/
def FullStationaryEquations (k : SpectrumData K) (q v : ComplexPair K)
    (g₁ g₂ g₃ r₁ r₂ r₃ : K) : Prop :=
  CurrentEquations r₁ r₂ r₃ (edge₁₂ k q).im (edge₁₃ k v).im (edge₂₃ k q v).im ∧
  FullRadialEquations k q v g₁ g₂ g₃ r₁ r₂ r₃

/-- Full-support equivalence of the original algebraic stationary system and
the amplitude-free two-phase system. Every denominator condition is proved or
stated explicitly, and no abstract coverage premise is used. -/
theorem full_stationary_iff_reduced (k : SpectrumData K) (q v : ComplexPair K)
    (g₁ g₂ g₃ r₁ r₂ r₃ : K) (hq : ComplexPair.normSq q = 1) (hv : ComplexPair.normSq v = 1)
    (hloop : (ComplexPair.mul (ComplexPair.mul k.d₁₂ k.d₂₃) (ComplexPair.conj k.d₁₃)).im ≠ 0)
    (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0) (hr₃ : r₃ ≠ 0) (hsum : r₁ + r₂ + r₃ = 1)
    (hg₁ : g₁ ≠ 0) (hG : g₁ * r₁ + g₂ * r₂ + g₃ * r₃ ≠ 0) :
    FullStationaryEquations k q v g₁ g₂ g₃ r₁ r₂ r₃ ↔
    (currentDen k q v ≠ 0 ∧
      r₁ = (edge₂₃ k q v).im / currentDen k q v ∧
      r₂ = -(edge₁₃ k v).im / currentDen k q v ∧
      r₃ = (edge₁₂ k q).im / currentDen k q v ∧
      ReducedRadialEquations k q v g₁ g₂ g₃) := by
  have hn := ComplexPair.nonreal_loop_excludes_zero k.d₁₂ k.d₁₃ k.d₂₃ q v hq hv hloop
  constructor
  · rintro ⟨hc, hrad⟩
    obtain ⟨hD, h₁, h₂, h₃⟩ := current_reconstruction r₁ r₂ r₃
      (edge₁₂ k q).im (edge₁₃ k v).im (edge₂₃ k q v).im hr₁ hr₂ hr₃ hsum hc hn
    change currentDen k q v ≠ 0 at hD
    change r₁ = (edge₂₃ k q v).im / currentDen k q v at h₁
    change r₂ = -(edge₁₃ k v).im / currentDen k q v at h₂
    change r₃ = (edge₁₂ k q).im / currentDen k q v at h₃
    refine ⟨hD, h₁, h₂, h₃, ?_⟩
    rw [h₁, h₂, h₃] at hG hrad
    exact (reconstructed_radial_iff k q v g₁ g₂ g₃ (currentDen k q v) hq hv hg₁ hD hG).mp hrad
  · rintro ⟨hD, h₁, h₂, h₃, hred⟩
    rw [h₁, h₂, h₃] at hG ⊢
    exact ⟨reconstructed_current_equations _ _ _,
      (reconstructed_radial_iff k q v g₁ g₂ g₃ (currentDen k q v) hq hv hg₁ hD hG).mpr hred⟩

/-- The phase derivatives of the quotient have a common nonzero scalar
factor; their numerators are the two current balances below. -/
def PhaseTangentEquations (r₁ r₂ r₃ s₁₂ s₁₃ s₂₃ : K) : Prop :=
  -r₁ * r₂ * s₁₂ + r₂ * r₃ * s₂₃ = 0 ∧
  -r₁ * r₃ * s₁₃ - r₂ * r₃ * s₂₃ = 0

theorem phase_tangent_iff_currents (r₁ r₂ r₃ s₁₂ s₁₃ s₂₃ : K) :
    PhaseTangentEquations r₁ r₂ r₃ s₁₂ s₁₃ s₂₃ ↔
      CurrentEquations r₁ r₂ r₃ s₁₂ s₁₃ s₂₃ := by
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor
    · linear_combination -h₁
    · linear_combination -h₂
  · rintro ⟨h₁, h₂⟩
    constructor
    · linear_combination -h₁
    · linear_combination -h₂

/-- Homogeneous Euler identity makes the normalized radial Lagrange
multiplier vanish. This is the projective-normalization step, not an assumed
unconstrained derivative condition. -/
theorem radial_tangent_iff_unconstrained (r₁ r₂ r₃ g₁ g₂ g₃ b₁ b₂ b₃ : K)
    (hsum : r₁ + r₂ + r₃ = 1) :
    let G := g₁ * r₁ + g₂ * r₂ + g₃ * r₃
    let N := r₁ * b₁ + r₂ * b₂ + r₃ * b₃
    let d₁ := G * b₁ - N * g₁
    let d₂ := G * b₂ - N * g₂
    let d₃ := G * b₃ - N * g₃
    (d₂ - d₁ = 0 ∧ d₃ - d₁ = 0) ↔ (d₁ = 0 ∧ d₂ = 0 ∧ d₃ = 0) := by
  dsimp only
  let G := g₁ * r₁ + g₂ * r₂ + g₃ * r₃
  let N := r₁ * b₁ + r₂ * b₂ + r₃ * b₃
  have he : r₁ * (G * b₁ - N * g₁) + r₂ * (G * b₂ - N * g₂) +
      r₃ * (G * b₃ - N * g₃) = 0 := by dsimp [G, N]; ring
  change ((G * b₂ - N * g₂) - (G * b₁ - N * g₁) = 0 ∧
    (G * b₃ - N * g₃) - (G * b₁ - N * g₁) = 0) ↔
    (G * b₁ - N * g₁ = 0 ∧ G * b₂ - N * g₂ = 0 ∧ G * b₃ - N * g₃ = 0)
  constructor
  · rintro ⟨h₂, h₃⟩
    have h₁ : G * b₁ - N * g₁ = 0 := by
      linear_combination he - r₂ * h₂ - r₃ * h₃ - (G * b₁ - N * g₁) * hsum
    exact ⟨h₁, by linear_combination h₂ + h₁, by linear_combination h₃ + h₁⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨by linear_combination h₂ - h₁, by linear_combination h₃ - h₁⟩

end Field
end W3.Weighted
