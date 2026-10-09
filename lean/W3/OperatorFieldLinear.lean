import W3.Operator

/-! Charged linear-system and reconstruction algebra over arbitrary ordered fields. -/
noncomputable section
namespace W3.OperatorField
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- The exact exceptional denominator of the charged reconstruction. -/
def denominator (β a p : F) : F := β * p - a ^ 2

def ChargedEquations (β a p lam μ : F) : Prop :=
  β * lam + a * μ = 1 ∧ a * lam + p * μ = 0

theorem charged_equations_solution (β a p : F) (hD : denominator β a p ≠ 0) :
    ChargedEquations β a p (p / denominator β a p) (-a / denominator β a p) := by
  constructor <;> unfold denominator at * <;> field_simp [hD] <;> ring

theorem charged_equations_unique (β a p lam μ : F)
    (hD : denominator β a p ≠ 0) (h : ChargedEquations β a p lam μ) :
    lam = p / denominator β a p ∧ μ = -a / denominator β a p := by
  rcases h with ⟨h₁,h₂⟩
  constructor
  · apply (eq_div_iff hD).mpr
    unfold denominator
    linear_combination p * h₁ - a * h₂
  · apply (eq_div_iff hD).mpr
    unfold denominator
    linear_combination β * h₂ - a * h₁

/-- Complete classification of the singular 2×2 charged linear system. -/
theorem charged_equations_singular_iff (β a p lam μ : F)
    (hD : denominator β a p = 0) :
    ChargedEquations β a p lam μ ↔ a = 0 ∧ p = 0 ∧ β ≠ 0 ∧ lam = 1 / β := by
  constructor
  · rintro ⟨h₁,h₂⟩
    have hp : p = 0 := by
      unfold denominator at hD
      linear_combination -p * h₁ + a * h₂ + lam * hD
    have ha : a = 0 := by
      rw [hp] at hD
      unfold denominator at hD
      nlinarith [sq_nonneg a]
    have hb : β ≠ 0 := by intro hb; simp [ha, hb] at h₁
    refine ⟨ha,hp,hb,?_⟩
    apply (eq_div_iff hb).mpr
    simpa [ha, mul_comm] using h₁
  · rintro ⟨rfl,rfl,hb,rfl⟩
    constructor <;> simp [ChargedEquations, hb]

theorem charged_equations_zero_a (β p lam μ : F) (hp : p ≠ 0)
    (h : ChargedEquations β 0 p lam μ) :
    μ = 0 ∧ β ≠ 0 ∧ lam = 1 / β := by
  rcases h with ⟨h₁,h₂⟩
  have hm : μ = 0 := (mul_eq_zero.mp (by simpa using h₂)).resolve_left hp
  have hb : β ≠ 0 := by intro hb; simp [hb] at h₁
  refine ⟨hm,hb,(eq_div_iff hb).mpr ?_⟩
  simpa [mul_comm] using h₁

/-- A zero-energy candidate is valid algebraically; no division by p occurs. -/
theorem charged_equations_zero_p (β a : F) (ha : a ≠ 0) :
    denominator β a 0 ≠ 0 ∧ ChargedEquations β a 0 0 (1 / a) := by
  constructor
  · simp [denominator, ha]
  · constructor <;> simp [ha]

section Reconstruction
variable {M N : Type*} [AddCommGroup M] [Module F M]
  [AddCommGroup N] [Module F N]

/-- Equation (25), written without division by the energy numerator. -/
def reconstruction (β a p : F) (U V : M) : M :=
  (p / denominator β a p) • U - (a / denominator β a p) • V

theorem reconstruction_apply (β a p : F) (U V : M) (T : M →ₗ[F] N) :
    T (reconstruction β a p U V) =
      (p / denominator β a p) • T U - (a / denominator β a p) • T V := by
  simp [reconstruction]

theorem reconstruction_operator (β a p : F) (U V I P : M)
    (L : M →ₗ[F] M) (hU : L U = I) (hV : L V = P) :
    L (reconstruction β a p U V) =
      (p / denominator β a p) • I - (a / denominator β a p) • P := by
  simp [reconstruction, hU, hV]

theorem reconstruction_trace (β a p : F) (U V : M)
    (tr : M →ₗ[F] F) (hU : tr U = β) (hV : tr V = a)
    (hD : denominator β a p ≠ 0) :
    tr (reconstruction β a p U V) = 1 := by
  simp only [reconstruction, map_sub, map_smul, hU, hV, smul_eq_mul]
  have h := (charged_equations_solution β a p hD).1
  simpa only [neg_div, mul_neg, sub_eq_add_neg, mul_comm] using h

theorem reconstruction_expectation (β a p : F) (U V : M)
    (expect : M →ₗ[F] F) (hU : expect U = a) (hV : expect V = p) :
    expect (reconstruction β a p U V) = 0 := by
  simp [reconstruction, hU, hV]
  ring

/-- The kernel condition is exactly the numerator of projective stationarity,
including p=0. This theorem assumes no differential stationarity statement. -/
theorem reconstruction_kernel_iff (β a p : F) (U V : M)
    (T : M →ₗ[F] N) (hD : denominator β a p ≠ 0) :
    T (reconstruction β a p U V) = 0 ↔ T (a • V - p • U) = 0 := by
  have heq : T (a • V - p • U) =
      (-denominator β a p) • T (reconstruction β a p U V) := by
    simp only [reconstruction, map_sub, map_smul, smul_sub, smul_smul]
    have h₁ : -denominator β a p * (p / denominator β a p) = -p := by
      field_simp
    have h₂ : -denominator β a p * (a / denominator β a p) = -a := by
      field_simp
    rw [h₁,h₂,neg_smul,neg_smul]
    abel
  rw [heq, smul_eq_zero]
  simp [hD]

/-- From an invertible linear operator, the full charged equation is equivalent
 to the reconstructed point once the trace/expectation linear system is known. -/
theorem charged_reconstruction_unique (L : M ≃ₗ[F] M) (I P K : M)
    (β a p lam μ : F) (hD : denominator β a p ≠ 0)
    (hEq : ChargedEquations β a p lam μ) (hL : L K = lam • I + μ • P) :
    K = reconstruction β a p (L.symm I) (L.symm P) := by
  obtain ⟨rfl,rfl⟩ := charged_equations_unique β a p lam μ hD hEq
  apply L.injective
  simp [reconstruction, hL, neg_div, sub_eq_add_neg]

/-- Equation (25)'s energy, using the actual bilinear trace form when instantiated. -/
theorem reconstruction_energy (β a p : F) (U V I P : M)
    (L : M →ₗ[F] M) (B : M →ₗ[F] M →ₗ[F] F)
    (hU : L U = I) (hV : L V = P)
    (hI : B (reconstruction β a p U V) I = 1)
    (hP : B (reconstruction β a p U V) P = 0) :
    B (reconstruction β a p U V) (L (reconstruction β a p U V)) / 2 =
      p / (2 * denominator β a p) := by
  rw [reconstruction_operator β a p U V I P L hU hV]
  simp [hI, hP]
  ring

/-- Squared norm/purity numerator, valid for any symmetric bilinear form. -/
theorem reconstruction_purity (β a p : F) (U V : M)
    (B : M →ₗ[F] M →ₗ[F] F) (hB : B V U = B U V) :
    B (reconstruction β a p U V) (reconstruction β a p U V) =
      (p ^ 2 * B U U - 2 * p * a * B U V + a ^ 2 * B V V) /
        denominator β a p ^ 2 := by
  simp [reconstruction, map_sub, map_smul, hB]
  ring

/-- The a=0,p≠0 branch cannot have a kernel if U has none in that direction. -/
theorem charged_a_ne_zero (β a p lam μ : F) (U V K : M) (T : M →ₗ[F] N)
    (hD : denominator β a p ≠ 0) (hEq : ChargedEquations β a p lam μ)
    (hrep : K = lam • U + μ • V) (hker : T K = 0) (hU : T U ≠ 0) : a ≠ 0 := by
  intro ha
  have hp : p ≠ 0 := by
    intro hp; apply hD; simp [denominator, ha, hp]
  obtain ⟨hμ,hβ,hlam⟩ := charged_equations_zero_a β p lam μ hp (by simpa [ha] using hEq)
  have hl : lam ≠ 0 := by rw [hlam]; exact one_div_ne_zero hβ
  rw [hrep, map_add, map_smul, map_smul, hμ, zero_smul, add_zero] at hker
  exact hU ((smul_eq_zero.mp hker).resolve_left hl)

/-- The singular branch forces a nonzero projector coefficient whenever U has
no kernel in the tested direction. -/
theorem singular_mu_ne_zero (β a p lam μ : F) (U V K : M) (T : M →ₗ[F] N)
    (hD : denominator β a p = 0) (hEq : ChargedEquations β a p lam μ)
    (hrep : K = lam • U + μ • V) (hker : T K = 0) (hU : T U ≠ 0) : μ ≠ 0 := by
  obtain ⟨ha,hp,hβ,hlam⟩ := (charged_equations_singular_iff β a p lam μ hD).mp hEq
  intro hμ
  rw [hrep, map_add, map_smul, map_smul, hμ, zero_smul, add_zero] at hker
  have hl : lam ≠ 0 := by rw [hlam]; exact one_div_ne_zero hβ
  exact hU ((smul_eq_zero.mp hker).resolve_left hl)

/-- Equation (32), retaining the singular a=p=0 branch instead of dropping it. -/
theorem kernel_proportional (lam μ : F) (U V K : M) (T : M →ₗ[F] N)
    (hμ : μ ≠ 0) (hrep : K = lam • U + μ • V) (hker : T K = 0) :
    T V = (-lam / μ) • T U := by
  rw [hrep, map_add, map_smul, map_smul] at hker
  have hV : μ • T V = -(lam • T U) := by
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_comm] using hker
  calc
    T V = μ⁻¹ • (μ • T V) := by rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
    _ = μ⁻¹ • -(lam • T U) := by rw [hV]
    _ = (-lam / μ) • T U := by rw [smul_neg, smul_smul, ← neg_smul]; congr 1; ring

end Reconstruction

end W3.OperatorField
