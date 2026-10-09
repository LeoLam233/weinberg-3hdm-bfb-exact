import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open scoped BigOperators
open ComplexConjugate
namespace W3

/-- Three completely unrestricted complex electroweak doublets. -/
abbrev Fields := EuclideanSpace ℂ (Fin 2 × Fin 3)

/-- The fifteen real coordinates, with pairs ordered 01,02,12. -/
structure Couplings where
  a : Fin 3 → ℝ
  b : Fin 3 → ℝ
  c : Fin 3 → ℝ
  d : Fin 3 → ℂ

/-- Physical Gram matrix, with exactly the source's conjugation convention. -/
def gram (φ : Fields) : Matrix (Fin 3) (Fin 3) ℂ := fun i j =>
  ∑ k : Fin 2, conj (φ (k,i)) * φ (k,j)

def radius (φ : Fields) (i : Fin 3) : ℝ :=
  ∑ k : Fin 2, Complex.normSq (φ (k,i))

def pairTerm (κ : Couplings) (φ : Fields) (edge i j : Fin 3) : ℝ :=
  κ.b edge * radius φ i * radius φ j + κ.c edge * Complex.normSq (gram φ i j) +
    (κ.d edge * gram φ i j ^ 2).re

/-- The full complex Weinberg quartic, without CP, support, or coupling restrictions. -/
def quartic (κ : Couplings) (φ : Fields) : ℝ :=
  (∑ i : Fin 3, κ.a i * radius φ i ^ 2) / 2 +
    pairTerm κ φ 0 0 1 + pairTerm κ φ 1 0 2 + pairTerm κ φ 2 1 2

lemma gram_diag (φ : Fields) (i : Fin 3) : gram φ i i = (radius φ i : ℂ) := by
  apply Complex.ext <;> simp [gram, radius, Fin.sum_univ_two, Complex.normSq] <;> ring

lemma radius_nonneg (φ : Fields) (i : Fin 3) : 0 ≤ radius φ i := by
  exact Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

lemma continuous_gram (i j : Fin 3) : Continuous (fun φ : Fields => gram φ i j) := by
  unfold gram
  fun_prop

lemma continuous_radius (i : Fin 3) : Continuous (fun φ : Fields => radius φ i) := by
  unfold radius
  fun_prop

lemma continuous_quartic (κ : Couplings) : Continuous (quartic κ) := by
  unfold quartic pairTerm
  have hg := continuous_gram
  have hr := continuous_radius
  fun_prop

lemma total_radius (φ : Fields) : (∑ i : Fin 3, radius φ i) = ‖φ‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [radius, Complex.normSq_eq_norm_sq, Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma radius_smul (t : ℝ) (φ : Fields) (i : Fin 3) :
    radius (t • φ) i = t ^ 2 * radius φ i := by
  simp [radius, Fin.sum_univ_two, Complex.normSq, pow_two]
  <;> ring

lemma gram_smul (t : ℝ) (φ : Fields) (i j : Fin 3) :
    gram (t • φ) i j = (t : ℂ) ^ 2 * gram φ i j := by
  apply Complex.ext <;> simp [gram, Fin.sum_univ_two, pow_two] <;> ring

lemma quartic_smul (κ : Couplings) (t : ℝ) (φ : Fields) :
    quartic κ (t • φ) = t ^ 4 * quartic κ φ := by
  simp [quartic, pairTerm, radius_smul, gram_smul, Fin.sum_univ_three,
    Complex.normSq, pow_two]
  <;> ring

@[simp] lemma quartic_zero (κ : Couplings) : quartic κ 0 = 0 := by
  simp [quartic, pairTerm, radius, gram]

/-- Actual minimum attainment on the normalized twelve-real-dimensional field sphere. -/
theorem exists_normalized_minimum (κ : Couplings) :
    ∃ φ : Fields, ‖φ‖ = 1 ∧ ∀ ψ : Fields, ‖ψ‖ = 1 → quartic κ φ ≤ quartic κ ψ := by
  obtain ⟨φ,hφ,hmin⟩ := (isCompact_sphere (0 : Fields) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1))
    (continuous_quartic κ).continuousOn
  refine ⟨φ, by simpa using hφ, ?_⟩
  intro ψ hψ
  exact hmin (by simpa using hψ)

lemma normalized_norm (φ : Fields) (hφ : φ ≠ 0) : ‖(‖φ‖⁻¹ : ℝ) • φ‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hφ))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hφ)

/-- Homogeneous normalization covers all physical fields, including zero. -/
theorem nonnegative_iff_normalized (κ : Couplings) :
    (∀ φ : Fields, 0 ≤ quartic κ φ) ↔
    (∀ φ : Fields, ‖φ‖ = 1 → 0 ≤ quartic κ φ) := by
  constructor
  · intro h φ _; exact h φ
  · intro h φ
    by_cases hz : φ = 0
    · simp [hz]
    · have hn := h ((‖φ‖⁻¹ : ℝ) • φ) (normalized_norm φ hz)
      rw [quartic_smul] at hn
      exact nonneg_of_mul_nonneg_right hn (pow_pos (inv_pos.mpr (norm_pos_iff.mpr hz)) 4)

/-- Strict quartic positivity means positivity at every nonzero physical field. -/
theorem positive_iff_normalized (κ : Couplings) :
    (∀ φ : Fields, φ ≠ 0 → 0 < quartic κ φ) ↔
    (∀ φ : Fields, ‖φ‖ = 1 → 0 < quartic κ φ) := by
  constructor
  · intro h φ hn
    apply h φ
    intro hz; simpa [hz] using hn
  · intro h φ hz
    have hn := h ((‖φ‖⁻¹ : ℝ) • φ) (normalized_norm φ hz)
    rw [quartic_smul] at hn
    exact pos_of_mul_pos_right hn (le_of_lt (pow_pos (inv_pos.mpr (norm_pos_iff.mpr hz)) 4))

/-- The exact normalized minimum detects weak and strict stability simultaneously. -/
theorem exists_minimum_with_stability (κ : Couplings) :
    ∃ φ : Fields, ‖φ‖ = 1 ∧
      (∀ ψ : Fields, ‖ψ‖ = 1 → quartic κ φ ≤ quartic κ ψ) ∧
      ((∀ ψ : Fields, 0 ≤ quartic κ ψ) ↔ 0 ≤ quartic κ φ) ∧
      ((∀ ψ : Fields, ψ ≠ 0 → 0 < quartic κ ψ) ↔ 0 < quartic κ φ) := by
  obtain ⟨φ,hφ,hmin⟩ := exists_normalized_minimum κ
  refine ⟨φ,hφ,hmin,?_,?_⟩
  · rw [nonnegative_iff_normalized]
    exact ⟨fun h => h φ hφ, fun h ψ hψ => h.trans (hmin ψ hψ)⟩
  · rw [positive_iff_normalized]
    exact ⟨fun h => h φ hφ, fun h ψ hψ => h.trans_le (hmin ψ hψ)⟩

#print axioms exists_minimum_with_stability
end W3
