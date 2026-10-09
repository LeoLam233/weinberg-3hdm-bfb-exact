import W3.WeightedStationarity
import W3.WeightedPairPhase

noncomputable section
namespace W3.Weighted
open ComplexPair
section Ring
variable {K : Type*} [CommRing K]

@[ext] theorem complexPair_ext {z w : ComplexPair K} (hr : z.re = w.re) (hi : z.im = w.im) : z = w := by
  cases z; cases w; cases hr; cases hi; rfl

theorem complexPair_mul_comm (z w : ComplexPair K) : mul z w = mul w z := by
  apply complexPair_ext <;> simp [mul] <;> ring

theorem complexPair_conj_mul (z w : ComplexPair K) : conj (mul z w) = mul (conj z) (conj w) := by
  apply complexPair_ext <;> simp [mul, conj] <;> ring

theorem complexPair_norm_conj (z : ComplexPair K) : normSq (conj z) = normSq z := by
  simp [normSq, conj]

theorem unit_relative_identity (u₁ u₂ u₃ : ComplexPair K) (h₁ : normSq u₁ = 1) :
    mul (mul u₃ (conj u₁)) (conj (mul u₂ (conj u₁))) = mul u₃ (conj u₂) := by
  apply complexPair_ext
  · simp only [mul, conj]
    simp only [normSq] at h₁
    linear_combination (u₃.re * u₂.re + u₃.im * u₂.im) * h₁
  · simp only [mul, conj]
    simp only [normSq] at h₁
    linear_combination (u₃.im * u₂.re - u₃.re * u₂.im) * h₁

end Ring
section Field
variable {K : Type*} [Field K]

/-- Squared amplitude phase for z=conjugate(w), exactly q=w²/|w|². -/
def amplitudeUnit (z : ComplexPair K) : ComplexPair K :=
  scale (normSq z)⁻¹ (conj (mul z z))

/-- Normalization fixes the common phase by dividing by the first unit phase. -/
def relativePhase (z₁ z₂ : ComplexPair K) : ComplexPair K :=
  mul (amplitudeUnit z₂) (conj (amplitudeUnit z₁))

theorem amplitudeUnit_norm (z : ComplexPair K) (hz : normSq z ≠ 0) :
    normSq (amplitudeUnit z) = 1 := by
  simp only [normSq, amplitudeUnit, scale, conj, mul] at *
  field_simp
  ring

theorem relativePhase_norm (z₁ z₂ : ComplexPair K)
    (h₁ : normSq z₁ ≠ 0) (h₂ : normSq z₂ ≠ 0) :
    normSq (relativePhase z₁ z₂) = 1 := by
  rw [relativePhase, complex_norm_mul, complexPair_norm_conj,
    amplitudeUnit_norm _ h₁, amplitudeUnit_norm _ h₂, mul_one]

theorem relativePhase_composition (z₁ z₂ z₃ : ComplexPair K) (h₁ : normSq z₁ ≠ 0) :
    mul (relativePhase z₁ z₃) (conj (relativePhase z₁ z₂)) = relativePhase z₂ z₃ := by
  exact unit_relative_identity _ _ _ (amplitudeUnit_norm z₁ h₁)

/-- The phase normalization recovers the exact squared projector entry. -/
theorem relativePhase_projector_square (z₁ z₂ : ComplexPair K)
    (h₁ : normSq z₁ ≠ 0) (h₂ : normSq z₂ ≠ 0) :
    scale (normSq z₁ * normSq z₂) (relativePhase z₁ z₂) =
      mul (mul z₁ (conj z₂)) (mul z₁ (conj z₂)) := by
  apply complexPair_ext <;>
    simp only [scale, relativePhase, amplitudeUnit, mul, conj] <;>
    unfold normSq at * <;> field_simp <;> ring

/-- Both real and imaginary coupling contributions match the common spectrum. -/
theorem relativePhase_coupling (d z₁ z₂ : ComplexPair K)
    (h₁ : normSq z₁ ≠ 0) (h₂ : normSq z₂ ≠ 0) :
    mul d (mul (mul z₁ (conj z₂)) (mul z₁ (conj z₂))) =
      scale (normSq z₁ * normSq z₂) (mul d (relativePhase z₁ z₂)) := by
  rw [← relativePhase_projector_square z₁ z₂ h₁ h₂]
  apply complexPair_ext <;> simp only [mul, scale] <;> ring
end Field
section Contraction
variable {K : Type*} [CommRing K]

def amplitudeEdge (d z₁ z₂ : ComplexPair K) : ComplexPair K :=
  mul d (mul (mul z₁ (conj z₂)) (mul z₁ (conj z₂)))

/-- Contraction of component one of the rank-one operator equation with its
conjugate amplitude; effective pair coefficients already include b+c. -/
def amplitudeRow₁ (k : SpectrumData K) (z₁ z₂ z₃ : ComplexPair K) : ComplexPair K :=
  ⟨normSq z₁ * (k.a₁ * normSq z₁ + k.e₁₂ * normSq z₂ + k.e₁₃ * normSq z₃) +
      (amplitudeEdge k.d₁₂ z₁ z₂).re + (amplitudeEdge k.d₁₃ z₁ z₃).re,
    -(amplitudeEdge k.d₁₂ z₁ z₂).im - (amplitudeEdge k.d₁₃ z₁ z₃).im⟩
def amplitudeRow₂ (k : SpectrumData K) (z₁ z₂ z₃ : ComplexPair K) : ComplexPair K :=
  ⟨normSq z₂ * (k.e₁₂ * normSq z₁ + k.a₂ * normSq z₂ + k.e₂₃ * normSq z₃) +
      (amplitudeEdge k.d₁₂ z₁ z₂).re + (amplitudeEdge k.d₂₃ z₂ z₃).re,
    (amplitudeEdge k.d₁₂ z₁ z₂).im - (amplitudeEdge k.d₂₃ z₂ z₃).im⟩
def amplitudeRow₃ (k : SpectrumData K) (z₁ z₂ z₃ : ComplexPair K) : ComplexPair K :=
  ⟨normSq z₃ * (k.e₁₃ * normSq z₁ + k.e₂₃ * normSq z₂ + k.a₃ * normSq z₃) +
      (amplitudeEdge k.d₁₃ z₁ z₃).re + (amplitudeEdge k.d₂₃ z₂ z₃).re,
    (amplitudeEdge k.d₁₃ z₁ z₃).im + (amplitudeEdge k.d₂₃ z₂ z₃).im⟩

/-- Matrix eigenvalue or weighted generalized-eigenvalue equation after
component contraction. This definition also makes sense on support faces. -/
def AmplitudeEquations (k : SpectrumData K) (z₁ z₂ z₃ : ComplexPair K)
    (g₁ g₂ g₃ lam : K) : Prop :=
  amplitudeRow₁ k z₁ z₂ z₃ = ⟨lam * g₁ * normSq z₁, 0⟩ ∧
  amplitudeRow₂ k z₁ z₂ z₃ = ⟨lam * g₂ * normSq z₂, 0⟩ ∧
  amplitudeRow₃ k z₁ z₂ z₃ = ⟨lam * g₃ * normSq z₃, 0⟩
end Contraction

section AmplitudeBridge
variable {K : Type*} [Field K]

theorem amplitudeEdge_phase₁₂ (d z₁ z₂ : ComplexPair K)
    (h₁ : normSq z₁ ≠ 0) (h₂ : normSq z₂ ≠ 0) :
    amplitudeEdge d z₁ z₂ = scale (normSq z₁ * normSq z₂) (mul d (relativePhase z₁ z₂)) :=
  relativePhase_coupling d z₁ z₂ h₁ h₂

theorem amplitudeEdge_phase₂₃ (d z₁ z₂ z₃ : ComplexPair K)
    (h₁ : normSq z₁ ≠ 0) (h₂ : normSq z₂ ≠ 0) (h₃ : normSq z₃ ≠ 0) :
    amplitudeEdge d z₂ z₃ = scale (normSq z₂ * normSq z₃)
      (mul d (mul (relativePhase z₁ z₃) (conj (relativePhase z₁ z₂)))) := by
  rw [relativePhase_composition _ _ _ h₁]
  exact amplitudeEdge_phase₁₂ _ _ _ h₂ h₃

theorem amplitudeRow₁_phase (k : SpectrumData K) (z₁ z₂ z₃ : ComplexPair K)
    (h₁ : normSq z₁ ≠ 0) (h₂ : normSq z₂ ≠ 0) (h₃ : normSq z₃ ≠ 0) :
    let q := relativePhase z₁ z₂
    let v := relativePhase z₁ z₃
    amplitudeRow₁ k z₁ z₂ z₃ =
      ⟨normSq z₁ * twiceB₁ k q v (normSq z₁) (normSq z₂) (normSq z₃),
        -(normSq z₁ * normSq z₂ * (edge₁₂ k q).im) -
         normSq z₁ * normSq z₃ * (edge₁₃ k v).im⟩ := by
  dsimp only
  unfold amplitudeRow₁
  rw [amplitudeEdge_phase₁₂ _ _ _ h₁ h₂, amplitudeEdge_phase₁₂ _ _ _ h₁ h₃]
  apply complexPair_ext <;> simp only [scale, twiceB₁, edge₁₂, edge₁₃] <;> ring

theorem amplitudeRow₂_phase (k : SpectrumData K) (z₁ z₂ z₃ : ComplexPair K)
    (h₁ : normSq z₁ ≠ 0) (h₂ : normSq z₂ ≠ 0) (h₃ : normSq z₃ ≠ 0) :
    let q := relativePhase z₁ z₂
    let v := relativePhase z₁ z₃
    amplitudeRow₂ k z₁ z₂ z₃ =
      ⟨normSq z₂ * twiceB₂ k q v (normSq z₁) (normSq z₂) (normSq z₃),
        normSq z₁ * normSq z₂ * (edge₁₂ k q).im -
         normSq z₂ * normSq z₃ * (edge₂₃ k q v).im⟩ := by
  dsimp only
  unfold amplitudeRow₂
  rw [amplitudeEdge_phase₁₂ _ _ _ h₁ h₂, amplitudeEdge_phase₂₃ _ z₁ _ _ h₁ h₂ h₃]
  apply complexPair_ext <;> simp only [scale, twiceB₂, edge₁₂, edge₂₃] <;> ring

theorem amplitudeRow₃_phase (k : SpectrumData K) (z₁ z₂ z₃ : ComplexPair K)
    (h₁ : normSq z₁ ≠ 0) (h₂ : normSq z₂ ≠ 0) (h₃ : normSq z₃ ≠ 0) :
    let q := relativePhase z₁ z₂
    let v := relativePhase z₁ z₃
    amplitudeRow₃ k z₁ z₂ z₃ =
      ⟨normSq z₃ * twiceB₃ k q v (normSq z₁) (normSq z₂) (normSq z₃),
        normSq z₁ * normSq z₃ * (edge₁₃ k v).im +
         normSq z₂ * normSq z₃ * (edge₂₃ k q v).im⟩ := by
  dsimp only
  unfold amplitudeRow₃
  rw [amplitudeEdge_phase₁₂ _ _ _ h₁ h₃, amplitudeEdge_phase₂₃ _ z₁ _ _ h₁ h₂ h₃]
  apply complexPair_ext <;> simp only [scale, twiceB₃, edge₁₃, edge₂₃] <;> ring

/-- Splitting the actual contracted amplitude equation into real and imaginary
parts gives exactly the radial and conserved-current equations. -/
theorem amplitude_equations_iff (k : SpectrumData K) (z₁ z₂ z₃ : ComplexPair K)
    (g₁ g₂ g₃ lam : K) (h₁ : normSq z₁ ≠ 0) (h₂ : normSq z₂ ≠ 0) (h₃ : normSq z₃ ≠ 0) :
    let q := relativePhase z₁ z₂
    let v := relativePhase z₁ z₃
    AmplitudeEquations k z₁ z₂ z₃ g₁ g₂ g₃ lam ↔
    (CurrentEquations (normSq z₁) (normSq z₂) (normSq z₃)
      (edge₁₂ k q).im (edge₁₃ k v).im (edge₂₃ k q v).im ∧
     twiceB₁ k q v (normSq z₁) (normSq z₂) (normSq z₃) = lam * g₁ ∧
     twiceB₂ k q v (normSq z₁) (normSq z₂) (normSq z₃) = lam * g₂ ∧
     twiceB₃ k q v (normSq z₁) (normSq z₂) (normSq z₃) = lam * g₃) := by
  dsimp only
  unfold AmplitudeEquations
  rw [amplitudeRow₁_phase _ _ _ _ h₁ h₂ h₃,
    amplitudeRow₂_phase _ _ _ _ h₁ h₂ h₃, amplitudeRow₃_phase _ _ _ _ h₁ h₂ h₃]
  constructor
  · rintro ⟨he₁, he₂, he₃⟩
    have hr₁ := congrArg ComplexPair.re he₁
    have hr₂ := congrArg ComplexPair.re he₂
    have hr₃ := congrArg ComplexPair.re he₃
    have hi₂ := congrArg ComplexPair.im he₂
    have hi₃ := congrArg ComplexPair.im he₃
    dsimp only at hr₁ hr₂ hr₃ hi₂ hi₃
    refine ⟨⟨sub_eq_zero.mp hi₂, ?_⟩, ?_, ?_, ?_⟩
    · linear_combination hi₃
    · apply mul_left_cancel₀ h₁
      simpa only [mul_comm, mul_left_comm, _root_.mul_assoc] using hr₁
    · apply mul_left_cancel₀ h₂
      simpa only [mul_comm, mul_left_comm, _root_.mul_assoc] using hr₂
    · apply mul_left_cancel₀ h₃
      simpa only [mul_comm, mul_left_comm, _root_.mul_assoc] using hr₃
  · rintro ⟨hc, hr₁, hr₂, hr₃⟩
    refine ⟨?_, ?_, ?_⟩
    · apply complexPair_ext
      · dsimp only; rw [hr₁]; ring
      · dsimp only; linear_combination -hc.1 - hc.2
    · apply complexPair_ext
      · dsimp only; rw [hr₂]; ring
      · exact sub_eq_zero.mpr hc.1
    · apply complexPair_ext
      · dsimp only; rw [hr₃]; ring
      · dsimp only; linear_combination hc.2
end AmplitudeBridge

section FullAmplitude
variable {K : Type*} [Field K] [CharZero K]

theorem amplitude_implies_full_stationary (k : SpectrumData K) (z₁ z₂ z₃ : ComplexPair K)
    (g₁ g₂ g₃ lam : K) (h₁ : normSq z₁ ≠ 0) (h₂ : normSq z₂ ≠ 0) (h₃ : normSq z₃ ≠ 0)
    (hg₁ : g₁ ≠ 0) (hG : g₁ * normSq z₁ + g₂ * normSq z₂ + g₃ * normSq z₃ ≠ 0)
    (he : AmplitudeEquations k z₁ z₂ z₃ g₁ g₂ g₃ lam) :
    FullStationaryEquations k (relativePhase z₁ z₂) (relativePhase z₁ z₃)
      g₁ g₂ g₃ (normSq z₁) (normSq z₂) (normSq z₃) := by
  obtain ⟨hc, hr₁, hr₂, hr₃⟩ := (amplitude_equations_iff k z₁ z₂ z₃ g₁ g₂ g₃ lam h₁ h₂ h₃).mp he
  refine ⟨hc, ?_⟩
  apply (full_radial_cross_iff _ _ _ _ _ _ _ _ _ hg₁ hG).mpr
  rw [hr₁, hr₂, hr₃]
  constructor <;> ring

/-- Full-support weighted matrix stationarity is exactly the stationary system
already proved equivalent to the two explicit phase polynomials. -/
theorem exists_amplitude_iff_stationary (k : SpectrumData K) (z₁ z₂ z₃ : ComplexPair K)
    (g₁ g₂ g₃ : K) (h₁ : normSq z₁ ≠ 0) (h₂ : normSq z₂ ≠ 0) (h₃ : normSq z₃ ≠ 0)
    (hg₁ : g₁ ≠ 0) (hG : g₁ * normSq z₁ + g₂ * normSq z₂ + g₃ * normSq z₃ ≠ 0) :
    (∃ lam, AmplitudeEquations k z₁ z₂ z₃ g₁ g₂ g₃ lam) ↔
    FullStationaryEquations k (relativePhase z₁ z₂) (relativePhase z₁ z₃)
      g₁ g₂ g₃ (normSq z₁) (normSq z₂) (normSq z₃) := by
  constructor
  · rintro ⟨lam, he⟩
    exact amplitude_implies_full_stationary k z₁ z₂ z₃ g₁ g₂ g₃ lam h₁ h₂ h₃ hg₁ hG he
  · rintro ⟨hc, hr⟩
    refine ⟨2 * weightedQuotient k (relativePhase z₁ z₂) (relativePhase z₁ z₃)
      g₁ g₂ g₃ (normSq z₁) (normSq z₂) (normSq z₃) *
      (g₁ * normSq z₁ + g₂ * normSq z₂ + g₃ * normSq z₃), ?_⟩
    apply (amplitude_equations_iff k z₁ z₂ z₃ g₁ g₂ g₃ _ h₁ h₂ h₃).mpr
    exact ⟨hc, hr⟩
end FullAmplitude
end W3.Weighted
