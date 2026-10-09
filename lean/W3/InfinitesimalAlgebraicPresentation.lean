import W3.InfinitesimalAnnihilator
import W3.InfinitesimalRationalPresentation
import Mathlib.Algebra.Polynomial.Bivariate

/-! # From rational-function algebraicity to a selected relative residue. -/
noncomputable section
namespace W3.Infinitesimal
open Polynomial

variable (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]

lemma aevalAeval_eq_eval₂ (u v : Extension K) (P : K[X][X]) :
    Polynomial.aevalAeval u v P =
      P.eval₂ (Polynomial.eval₂RingHom (embed K).toRingHom u) v := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [map_add, Polynomial.eval₂_add, hP, hQ]
  | monomial n p =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
      Polynomial.aevalAeval_C, Polynomial.aevalAeval_Y,
      Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X]
    rfl

lemma bivariateEval_swap (P : K[X][X]) (x : Extension K) :
    bivariateEval K (Polynomial.Bivariate.swap P) x =
      P.eval₂ (epsilonPolynomialHom K) x := by
  have h := Polynomial.Bivariate.aevalAeval_swap x (epsilon K) P
  rw [aevalAeval_eq_eval₂, aevalAeval_eq_eval₂] at h
  exact h

/-- The supplied algebraicity predicate uses the actual rational-function embedding,
so clearing denominators and swapping variables produce the required nonzero
bivariate annihilator for the chosen element. -/
theorem ratfunc_algebraic_bivariate_annihilator {x : Extension K}
    (hx : letI := epsilonRatFuncAlgebra K; IsAlgebraic (RatFunc K) x) :
    ∃ P : K[X][X], P ≠ 0 ∧ bivariateEval K P x = 0 := by
  obtain ⟨Q, hQ, hroot⟩ := ratfunc_algebraic_cleared_annihilator K hx
  refine ⟨Polynomial.Bivariate.swap Q, ?_, ?_⟩
  · intro h
    apply hQ
    apply (Polynomial.Bivariate.swap (R := K)).injective
    simpa only [map_zero] using h
  · rw [bivariateEval_swap]
    exact hroot

/-- Every base-bounded element algebraic over the actual E(epsilon) has a unique
relative residue in E. This excludes arbitrary bounded ultrapower elements. -/
theorem tower_ratfunc_algebraic_relativeResidue (k : ℕ)
    {x : Extension (Tower realModel k)} (hx : BaseBounded (Tower realModel k) x)
    (halg : letI := epsilonRatFuncAlgebra (Tower realModel k);
      IsAlgebraic (RatFunc (Tower realModel k)) x) :
    ∃! q : Tower realModel k, HasRelativeResidue (Tower realModel k) x q := by
  obtain ⟨P, hP, hroot⟩ := ratfunc_algebraic_bivariate_annihilator (Tower realModel k) halg
  obtain ⟨_, _, _, _, q, _, hq⟩ := tower_bivariate_algebraic_relativeResidue k P hP hx hroot
  exact ⟨q, hq, fun r hr => relativeResidue_unique (Tower realModel k) hr hq⟩

/-- Closed base-field interval bounds survive the relative residue. -/
theorem relativeResidue_interval {x : Extension K} {q a b : K}
    (hq : HasRelativeResidue K x q) (ha : embed K a ≤ x) (hb : x ≤ embed K b) :
    a ≤ q ∧ q ≤ b := by
  constructor
  · by_contra h
    exact ha.not_gt (relativeResidue_lt K hq (lt_of_not_ge h))
  · by_contra h
    exact hb.not_gt (lt_relativeResidue K hq (lt_of_not_ge h))

#print axioms ratfunc_algebraic_bivariate_annihilator
#print axioms tower_ratfunc_algebraic_relativeResidue
end W3.Infinitesimal
