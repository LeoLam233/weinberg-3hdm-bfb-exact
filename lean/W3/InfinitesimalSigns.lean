import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Hom.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Dominant infinitesimal sign lemmas

These are supporting implications for Section 7, not the full W3 theorem.
The minimum estimate is proved from pointwise error and attained minima;
stationary-spectrum coverage is deliberately not assumed as a custom axiom.
-/

namespace W3.Infinitesimal

variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Field L] [LinearOrder L] [IsStrictOrderedRing L]

/-- Positive and smaller than every positive element of the embedded base field. -/
def PositiveInfinitesimal (ι : K →+*o L) (ε : L) : Prop :=
  0 < ε ∧ ∀ r : K, 0 < r → ε < ι r

/-- The elementary minimization estimate, without any compactness or coverage premise hidden
inside the definition: both actual minimizers and the pointwise estimate are explicit. -/
theorem minimum_perturbation_bound {X : Type*} {D : Set X} {f g : X → L}
    {x₀ x₁ : X} (hx₀ : x₀ ∈ D) (hx₁ : x₁ ∈ D)
    (hf : ∀ x ∈ D, f x₀ ≤ f x) (hg : ∀ x ∈ D, g x₁ ≤ g x)
    {ε B : L} (hbound : ∀ x ∈ D, |g x - f x - ε| ≤ B) :
    |g x₁ - f x₀ - ε| ≤ B := by
  have h₀ := (abs_le.mp (hbound x₀ hx₀)).2
  have h₁ := (abs_le.mp (hbound x₁ hx₁)).1
  have hmin₀ := hf x₁ hx₁
  have hmin₁ := hg x₀ hx₀
  apply abs_le.mpr
  constructor <;> linarith

/-- A negative base-field constant dominates the positive infinitesimal deformation. -/
theorem negative_of_negative_base (ι : K →+*o L) {ε B y : L} {m : K}
    (hε : PositiveInfinitesimal ι ε) (hB : B < ε)
    (hy : |y - ι m - ε| ≤ B) (hm : m < 0) : y < 0 := by
  have he := hε.2 (-m / 3) (div_pos (neg_pos.mpr hm) (by norm_num))
  have hmap : ι (-m / 3) = -ι m / 3 := by simp only [map_div₀, map_neg, map_ofNat]
  rw [hmap] at he
  have hepos := hε.1
  have hu := (abs_le.mp hy).2
  linarith

/-- A positive base-field constant exceeds twice the dominant infinitesimal after deformation. -/
theorem above_threshold_of_positive_base (ι : K →+*o L) {ε B y : L} {m : K}
    (hε : PositiveInfinitesimal ι ε) (hB : B < ε)
    (hy : |y - ι m - ε| ≤ B) (hm : 0 < m) : 2 * ε < y := by
  have he := hε.2 (m / 3) (by positivity)
  have hmap : ι (m / 3) = ι m / 3 := by simp only [map_div₀, map_neg, map_ofNat]
  rw [hmap] at he
  have hepos := hε.1
  have hl := (abs_le.mp hy).1
  linarith

/-- At zero the deformed minimum is strictly between the two exact thresholds. -/
theorem between_thresholds_of_zero_base (ι : K →+*o L) {ε B y : L}
    (hB : B < ε) (hy : |y - ι 0 - ε| ≤ B) : 0 < y ∧ y < 2 * ε := by
  simp only [map_zero] at hy
  rcases abs_le.mp hy with ⟨hl, hu⟩
  constructor <;> linarith

/-- All four strict/non-strict scalar tests in equation (3), conditional only on the
explicit scalar perturbation estimate and genuine positive infinitesimal hypotheses. -/
theorem sign_thresholds (ι : K →+*o L) {ε B y : L} {m : K}
    (hε : PositiveInfinitesimal ι ε) (hB : B < ε)
    (hy : |y - ι m - ε| ≤ B) :
    (0 ≤ m ↔ 0 < y) ∧ (0 < m ↔ 2 * ε < y) ∧
      (m < 0 ↔ y < 0) ∧ (m = 0 ↔ 0 < y ∧ y < 2 * ε) := by
  have hneg := negative_of_negative_base ι hε hB hy
  have hpos := above_threshold_of_positive_base ι hε hB hy
  have hzero : m = 0 → 0 < y ∧ y < 2 * ε := by
    intro hm
    subst m
    exact between_thresholds_of_zero_base ι hB hy
  have he := hε.1
  constructor
  · constructor
    · intro hm
      rcases eq_or_lt_of_le hm with hm | hm
      · exact (hzero hm.symm).1
      · have := hpos hm
        linarith
    · intro hypos
      by_contra hm
      have := hneg (lt_of_not_ge hm)
      linarith
  constructor
  · constructor
    · exact hpos
    · intro hyt
      rcases lt_trichotomy m 0 with hm | hm | hm
      · have := hneg hm
        linarith
      · have := (hzero hm).2
        linarith
      · exact hm
  constructor
  · constructor
    · exact hneg
    · intro hyn
      rcases lt_trichotomy m 0 with hm | hm | hm
      · exact hm
      · have := (hzero hm).1
        linarith
      · have := hpos hm
        linarith
  · constructor
    · exact hzero
    · rintro ⟨hyp, hyt⟩
      rcases lt_trichotomy m 0 with hm | hm | hm
      · have := hneg hm
        linarith
      · exact hm
      · have := hpos hm
        linarith

#print axioms minimum_perturbation_bound
#print axioms sign_thresholds

end W3.Infinitesimal
