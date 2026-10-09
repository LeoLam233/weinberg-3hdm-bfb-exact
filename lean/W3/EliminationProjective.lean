import W3.EliminationCertificate

noncomputable section
namespace W3.Elimination
open Polynomial

section ProjectiveRing
variable {R : Type*} [CommRing R]

def homQuad (a b c x y : R) : R := a * y ^ 2 + b * x * y + c * x ^ 2

/-- Equation (17), bihomogenized to bidegree (2,2). Coordinates are [t₀:t₁],[u₀:u₁]. -/
def phaseHom (p : PhaseRow R) (t₀ t₁ u₀ u₁ : R) : R :=
  (p.ai * (t₀ ^ 2 - t₁ ^ 2) + 2 * p.ar * t₀ * t₁) * (u₀ ^ 2 + u₁ ^ 2) +
  (p.bi * (u₀ ^ 2 - u₁ ^ 2) + 2 * p.br * u₀ * u₁) * (t₀ ^ 2 + t₁ ^ 2) +
  p.ci * ((t₀ ^ 2 - t₁ ^ 2) * (u₀ ^ 2 - u₁ ^ 2) + 4 * t₀ * t₁ * u₀ * u₁) +
  2 * p.cr * (u₀ * u₁ * (t₀ ^ 2 - t₁ ^ 2) - t₀ * t₁ * (u₀ ^ 2 - u₁ ^ 2))

/-- Resultant of the two restrictions to the divisor t₀=0. -/
def boundaryT (p q : PhaseRow R) : R :=
  resultant₂ (-p.ai - p.bi + p.ci) (2 * (p.br - p.cr)) (-p.ai + p.bi - p.ci)
    (-q.ai - q.bi + q.ci) (2 * (q.br - q.cr)) (-q.ai + q.bi - q.ci)

/-- Resultant of the two restrictions to the divisor u₀=0. -/
def boundaryU (p q : PhaseRow R) : R :=
  resultant₂ (-p.ai - p.bi + p.ci) (2 * (p.ar + p.cr)) (p.ai - p.bi - p.ci)
    (-q.ai - q.bi + q.ci) (2 * (q.ar + q.cr)) (q.ai - q.bi - q.ci)

theorem phaseHom_at_t_infinity (p : PhaseRow R) (t₁ u₀ u₁ : R) :
    phaseHom p 0 t₁ u₀ u₁ = t₁ ^ 2 *
      homQuad (-p.ai - p.bi + p.ci) (2 * (p.br - p.cr)) (-p.ai + p.bi - p.ci) u₀ u₁ := by
  unfold phaseHom homQuad
  ring

theorem phaseHom_at_u_infinity (p : PhaseRow R) (t₀ t₁ u₁ : R) :
    phaseHom p t₀ t₁ 0 u₁ = u₁ ^ 2 *
      homQuad (-p.ai - p.bi + p.ci) (2 * (p.ar + p.cr)) (p.ai - p.bi - p.ci) t₀ t₁ := by
  unfold phaseHom homQuad
  ring

end ProjectiveRing

section ProjectiveField
variable {K : Type*} [Field K]

theorem homogeneous_common_root_resultant (a b c d e f x y : K)
    (hxy : x ≠ 0 ∨ y ≠ 0) (hF : homQuad a b c x y = 0)
    (hG : homQuad d e f x y = 0) : resultant₂ a b c d e f = 0 := by
  by_cases hx : x = 0
  · have hy : y ≠ 0 := hxy.resolve_left (not_not_intro hx)
    have ha : a = 0 := by
      simpa [homQuad, hx, pow_ne_zero 2 hy] using hF
    have hd : d = 0 := by
      simpa [homQuad, hx, pow_ne_zero 2 hy] using hG
    simp [resultant₂, ha, hd]
  · have hF' : quad a b c (y / x) = 0 := by
      dsimp [quad]
      field_simp
      dsimp [homQuad] at hF
      linear_combination hF
    have hG' : quad d e f (y / x) = 0 := by
      dsimp [quad]
      field_simp
      dsimp [homQuad] at hG
      linear_combination hG
    exact common_root_resultant _ _ _ _ _ _ _ hF' hG'

/-- Boundary nonvanishing forces every projective solution into the finite (t,u) chart. -/
theorem phaseHom_denominators_ne_zero (p q : PhaseRow K) (t₀ t₁ u₀ u₁ : K)
    (ht : t₀ ≠ 0 ∨ t₁ ≠ 0) (hu : u₀ ≠ 0 ∨ u₁ ≠ 0)
    (hbt : boundaryT p q ≠ 0) (hbu : boundaryU p q ≠ 0)
    (hF : phaseHom p t₀ t₁ u₀ u₁ = 0) (hG : phaseHom q t₀ t₁ u₀ u₁ = 0) :
    t₀ ≠ 0 ∧ u₀ ≠ 0 := by
  constructor
  · intro ht0
    have ht1 : t₁ ≠ 0 := ht.resolve_left (not_not_intro ht0)
    rw [ht0, phaseHom_at_t_infinity] at hF hG
    have hf := (mul_eq_zero.mp hF).resolve_left (pow_ne_zero 2 ht1)
    have hg := (mul_eq_zero.mp hG).resolve_left (pow_ne_zero 2 ht1)
    exact hbt (homogeneous_common_root_resultant _ _ _ _ _ _ _ _ hu hf hg)
  · intro hu0
    have hu1 : u₁ ≠ 0 := hu.resolve_left (not_not_intro hu0)
    rw [hu0, phaseHom_at_u_infinity] at hF hG
    have hf := (mul_eq_zero.mp hF).resolve_left (pow_ne_zero 2 hu1)
    have hg := (mul_eq_zero.mp hG).resolve_left (pow_ne_zero 2 hu1)
    exact hbu (homogeneous_common_root_resultant _ _ _ _ _ _ _ _ ht hf hg)

theorem phaseHom_affine (p : PhaseRow K) (t₀ t₁ u₀ u₁ : K)
    (ht : t₀ ≠ 0) (hu : u₀ ≠ 0) :
    phaseHom p t₀ t₁ u₀ u₁ = t₀ ^ 2 * u₀ ^ 2 * phaseValue p (t₁ / t₀) (u₁ / u₀) := by
  unfold phaseHom phaseValue
  field_simp <;> ring

theorem phaseHom_zero_iff_affine (p : PhaseRow K) (t₀ t₁ u₀ u₁ : K)
    (ht : t₀ ≠ 0) (hu : u₀ ≠ 0) :
    phaseHom p t₀ t₁ u₀ u₁ = 0 ↔ phaseValue p (t₁ / t₀) (u₁ / u₀) = 0 := by
  rw [phaseHom_affine p t₀ t₁ u₀ u₁ ht hu]
  exact mul_eq_zero_iff_left (mul_ne_zero (pow_ne_zero 2 ht) (pow_ne_zero 2 hu))

end ProjectiveField

section Ordered
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem projective_phase_root_iff (p q : PhaseRow K) (A B : K[X])
    (hcert : BezoutCertificate (phaseSextic p q) (phaseLinearOne p q) A B)
    (t₀ t₁ u₀ u₁ : K) (ht : t₀ ≠ 0 ∨ t₁ ≠ 0) (hu : u₀ ≠ 0 ∨ u₁ ≠ 0)
    (hbt : boundaryT p q ≠ 0) (hbu : boundaryU p q ≠ 0) :
    (phaseHom p t₀ t₁ u₀ u₁ = 0 ∧ phaseHom q t₀ t₁ u₀ u₁ = 0) ↔
    (t₀ ≠ 0 ∧ u₀ ≠ 0 ∧ (phaseSextic p q).eval (t₁ / t₀) = 0 ∧
      u₁ / u₀ = -(phaseLinearZero p q).eval (t₁ / t₀) /
        (phaseLinearOne p q).eval (t₁ / t₀)) := by
  constructor
  · rintro ⟨hF, hG⟩
    obtain ⟨ht0, hu0⟩ := phaseHom_denominators_ne_zero p q t₀ t₁ u₀ u₁ ht hu hbt hbu hF hG
    refine ⟨ht0, hu0, ?_⟩
    apply (phase_root_iff p q A B hcert _ _).mp
    exact ⟨(phaseHom_zero_iff_affine p _ _ _ _ ht0 hu0).mp hF,
      (phaseHom_zero_iff_affine q _ _ _ _ ht0 hu0).mp hG⟩
  · rintro ⟨ht0, hu0, hS, hr⟩
    obtain ⟨hF, hG⟩ := (phase_root_iff p q A B hcert _ _).mpr ⟨hS, hr⟩
    exact ⟨(phaseHom_zero_iff_affine p _ _ _ _ ht0 hu0).mpr hF,
      (phaseHom_zero_iff_affine q _ _ _ _ ht0 hu0).mpr hG⟩

end Ordered
end W3.Elimination
