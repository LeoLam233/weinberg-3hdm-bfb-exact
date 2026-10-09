import W3.InfinitesimalRelativeResidue
import Mathlib.Algebra.Polynomial.Inductions

/-! # First nonzero epsilon coefficient and selected algebraic residue
A bounded root of a nonzero bivariate polynomial in epsilon and X has an actual
relative residue. Common epsilon powers are extracted by finite Horner recursion.
-/
noncomputable section
namespace W3.Infinitesimal
open Polynomial

variable (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Boundedness relative to the complete preceding field, not just relative to ℝ. -/
def BaseBounded (x : Extension K) : Prop :=
  ∃ C : K, 0 < C ∧ |x| ≤ embed K C

@[simp] lemma embed_abs (r : K) : embed K |r| = |embed K r| := Filter.Germ.const_abs r

lemma baseBounded_embed (r : K) : BaseBounded K (embed K r) := by
  refine ⟨|r| + 1, add_pos_of_nonneg_of_pos (abs_nonneg r) zero_lt_one, ?_⟩
  rw [← embed_abs]
  exact (embed_le_iff K).mpr (le_add_of_nonneg_right zero_le_one)

lemma baseBounded_add {x y : Extension K} (hx : BaseBounded K x) (hy : BaseBounded K y) :
    BaseBounded K (x + y) := by
  obtain ⟨C, hC, hx⟩ := hx
  obtain ⟨D, hD, hy⟩ := hy
  refine ⟨C + D, add_pos hC hD, ?_⟩
  rw [map_add]
  exact (abs_add_le x y).trans (add_le_add hx hy)

lemma baseBounded_mul {x y : Extension K} (hx : BaseBounded K x) (hy : BaseBounded K y) :
    BaseBounded K (x * y) := by
  obtain ⟨C, hC, hx⟩ := hx
  obtain ⟨D, hD, hy⟩ := hy
  refine ⟨C * D, mul_pos hC hD, ?_⟩
  rw [abs_mul, map_mul]
  have hC' : 0 ≤ embed K C := by
    simpa only [map_zero] using (embed_le_iff K).mpr hC.le
  exact mul_le_mul hx hy (abs_nonneg _) hC'

lemma baseBounded_epsilon : BaseBounded K (epsilon K) := by
  refine ⟨1, zero_lt_one, ?_⟩
  rw [abs_of_pos (epsilon_pos K)]
  exact (epsilon_lt_embed K zero_lt_one).le

lemma baseBounded_one : BaseBounded K (1 : Extension K) := by
  simpa only [map_one] using baseBounded_embed K 1

lemma baseBounded_pow {x : Extension K} (hx : BaseBounded K x) (n : ℕ) :
    BaseBounded K (x ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using baseBounded_one K
  | succ n ih => simpa only [pow_succ] using baseBounded_mul K ih hx

lemma baseBounded_polynomial_eval₂ {R : Type*} [CommRing R]
    (f : R →+* Extension K) (hf : ∀ r, BaseBounded K (f r))
    {x : Extension K} (hx : BaseBounded K x) (p : R[X]) :
    BaseBounded K (p.eval₂ f x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.eval₂_add]
    exact baseBounded_add K hp hq
  | monomial n a =>
    rw [Polynomial.eval₂_monomial]
    exact baseBounded_mul K (hf a) (baseBounded_pow K hx n)

/-- An infinitesimal multiplied by any base-bounded quantity remains infinitesimal. -/
lemma epsilon_mul_baseBounded_small {z : Extension K} (hz : BaseBounded K z)
    {δ : K} (hδ : 0 < δ) : |epsilon K * z| < embed K δ := by
  obtain ⟨C, hC, hz⟩ := hz
  have he := epsilon_lt_embed K (div_pos hδ hC)
  rw [map_div₀] at he
  have hC' : 0 < embed K C := by
    simpa only [map_zero] using (embed_lt_iff K).mpr hC
  have hprod := (lt_div_iff₀ hC').mp he
  rw [abs_mul, abs_of_pos (epsilon_pos K)]
  exact (mul_le_mul_of_nonneg_left hz (epsilon_pos K).le).trans_lt hprod

/-- Evaluate an outer epsilon polynomial whose coefficients are polynomials in x. -/
def bivariateEval (P : K[X][X]) (x : Extension K) : Extension K :=
  P.eval₂ (Polynomial.eval₂RingHom (embed K).toRingHom x) (epsilon K)

lemma baseBounded_bivariateEval (P : K[X][X]) {x : Extension K} (hx : BaseBounded K x) :
    BaseBounded K (bivariateEval K P x) := by
  exact baseBounded_polynomial_eval₂ K _
    (fun p => baseBounded_polynomial_eval₂ K _ (baseBounded_embed K) hx p)
    (baseBounded_epsilon K) P

/-- For a normalized annihilator, its epsilon-zero coefficient evaluates to an
infinitesimal at every bounded root. No simple-root hypothesis is used. -/
theorem constantCoefficient_small_of_annihilator (P : K[X][X]) {x : Extension K}
    (hx : BaseBounded K x) (hP : bivariateEval K P x = 0) :
    ∀ δ : K, 0 < δ → |(P.coeff 0).eval₂ (embed K).toRingHom x| < embed K δ := by
  have hd := congrArg
    (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (embed K).toRingHom x) (epsilon K))
    (Polynomial.divX_mul_X_add P)
  simp only [map_add, map_mul, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X, Polynomial.eval₂_C] at hd
  change bivariateEval K P.divX x * epsilon K +
    (P.coeff 0).eval₂ (embed K).toRingHom x = bivariateEval K P x at hd
  rw [hP] at hd
  have hzero : (P.coeff 0).eval₂ (embed K).toRingHom x =
      -(epsilon K * bivariateEval K P.divX x) := by
    rw [mul_comm] at hd
    linarith
  intro δ hδ
  rw [hzero, abs_neg]
  exact epsilon_mul_baseBounded_small K (baseBounded_bivariateEval K P.divX hx) hδ

/-- Remove the largest common initial power of X by the terminating Horner
recursor. The residual polynomial has a nonzero constant coefficient. -/
theorem extract_initial_X_power {R : Type*} [CommRing R] (P : R[X]) (hP : P ≠ 0) :
    ∃ n : ℕ, ∃ Q : R[X], Q.coeff 0 ≠ 0 ∧ P = X ^ n * Q := by
  revert hP
  induction P using Polynomial.recOnHorner with
  | M0 => intro h; exact (h rfl).elim
  | MC p a hp ha _ =>
    intro _
    refine ⟨0, p + C a, ?_, ?_⟩
    · simpa only [Polynomial.coeff_add, Polynomial.coeff_C_zero, hp, zero_add] using ha
    · simp only [pow_zero, one_mul]
  | MX p hp ih =>
    intro _
    obtain ⟨n, Q, hQ, heq⟩ := ih hp
    refine ⟨n + 1, Q, hQ, ?_⟩
    rw [heq, pow_succ]
    ring

/-- The selected bounded bivariate algebraic root has an actual residue in the
preceding tower field, and that residue is a root of the computed nonzero
first epsilon coefficient after removal of the common epsilon power. -/
theorem tower_bivariate_algebraic_relativeResidue (k : ℕ)
    (P : (Tower realModel k)[X][X]) (hP : P ≠ 0)
    {x : Extension (Tower realModel k)} (hx : BaseBounded (Tower realModel k) x)
    (hroot : bivariateEval (Tower realModel k) P x = 0) :
    ∃ n : ℕ, ∃ Q : (Tower realModel k)[X][X],
      Q.coeff 0 ≠ 0 ∧ P = X ^ n * Q ∧
      ∃ q : Tower realModel k, (Q.coeff 0).IsRoot q ∧
        HasRelativeResidue (Tower realModel k) x q := by
  obtain ⟨n, Q, hQ, heq⟩ := extract_initial_X_power P hP
  have hrootQ : bivariateEval (Tower realModel k) Q x = 0 := by
    unfold bivariateEval at hroot ⊢
    rw [heq, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X] at hroot
    exact (mul_eq_zero.mp hroot).resolve_left (pow_ne_zero _ (epsilon_pos _).ne')
  obtain ⟨B, hB, hbound⟩ := hx
  refine ⟨n, Q, hQ, heq, ?_⟩
  exact tower_relativeResidue_of_infinitesimal_polynomial k hQ hbound
    (constantCoefficient_small_of_annihilator (Tower realModel k) Q ⟨B, hB, hbound⟩ hrootQ)

#print axioms extract_initial_X_power
#print axioms tower_bivariate_algebraic_relativeResidue
end W3.Infinitesimal
