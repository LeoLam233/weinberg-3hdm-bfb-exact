import W3.InfinitesimalAlgebraicPresentation

/-! # Residue descent with an explicit coefficient subfield
Denominator clearing and initial-coefficient normalization are performed over F,
not over the larger preceding ultrapower. Consequently the selected residue
remains algebraic over F, which is the invariant required for iteration.
-/
noncomputable section
namespace W3.Infinitesimal
open Polynomial
open scoped nonZeroDivisors

variable {F K : Type*} [Field F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def epsilonPolynomialHomAlong (f : F →+* K) : F[X] →+* Extension K :=
  (epsilonPolynomialHom K).comp (Polynomial.mapRingHom f)

lemma epsilonPolynomialHomAlong_injective (f : F →+* K) :
    Function.Injective (epsilonPolynomialHomAlong f) :=
  (epsilonPolynomialHom_injective K).comp (Polynomial.map_injective f f.injective)

lemma epsilonPolynomialHomAlong_nonZeroDivisors (f : F →+* K) :
    F[X]⁰ ≤ (Extension K)⁰.comap (epsilonPolynomialHomAlong f) := by
  intro p hp
  change epsilonPolynomialHomAlong f p ∈ (Extension K)⁰
  rw [mem_nonZeroDivisors_iff_ne_zero] at hp ⊢
  intro h
  exact hp ((epsilonPolynomialHomAlong_injective f) (h.trans (map_zero _).symm))

def epsilonRatFuncHomAlong (f : F →+* K) : RatFunc F →+* Extension K :=
  RatFunc.liftRingHom (epsilonPolynomialHomAlong f)
    (epsilonPolynomialHomAlong_nonZeroDivisors f)

@[instance_reducible] def epsilonRatFuncAlgebraAlong (f : F →+* K) :
    Algebra (RatFunc F) (Extension K) := (epsilonRatFuncHomAlong f).toAlgebra

@[simp] lemma epsilonRatFuncHomAlong_polynomial (f : F →+* K) (p : F[X]) :
    epsilonRatFuncHomAlong f (algebraMap F[X] (RatFunc F) p) =
      epsilonPolynomialHomAlong f p := RatFunc.liftRingHom_algebraMap _ _ p

lemma clear_ratfunc_annihilator_along (f : F →+* K) {p : (RatFunc F)[X]}
    (hp : p ≠ 0) {x : Extension K}
    (hroot : p.eval₂ (epsilonRatFuncHomAlong f) x = 0) :
    ∃ P : F[X][X], P ≠ 0 ∧ P.eval₂ (epsilonPolynomialHomAlong f) x = 0 := by
  let P := IsLocalization.integerNormalization F[X]⁰ p
  refine ⟨P, ?_, ?_⟩
  · intro h
    exact hp ((IsLocalization.integerNormalization_eq_zero_iff
      (M := F[X]⁰) le_rfl p).mp h)
  · have h := IsLocalization.integerNormalization_eval₂_eq_zero F[X]⁰
      (epsilonRatFuncHomAlong f) p hroot
    rwa [show (epsilonRatFuncHomAlong f).comp (algebraMap F[X] (RatFunc F)) =
      epsilonPolynomialHomAlong f from RatFunc.liftRingHom_comp_algebraMap _ _] at h

/-- Apply the coefficient embedding to both levels of a bivariate polynomial. -/
def mapBivariate (f : F →+* K) : F[X][X] →+* K[X][X] :=
  Polynomial.mapRingHom (Polynomial.mapRingHom f)

lemma mapBivariate_injective (f : F →+* K) : Function.Injective (mapBivariate f) :=
  Polynomial.map_injective _ (Polynomial.map_injective f f.injective)

lemma mapBivariate_coeff (f : F →+* K) (P : F[X][X]) (n : ℕ) :
    (mapBivariate f P).coeff n = (P.coeff n).map f := Polynomial.coeff_map _ _

lemma bivariateEval_map_swap (f : F →+* K) (P : F[X][X]) (x : Extension K) :
    bivariateEval K (mapBivariate f (Polynomial.Bivariate.swap P)) x =
      P.eval₂ (epsilonPolynomialHomAlong f) x := by
  have hswap : mapBivariate f (Polynomial.Bivariate.swap P) =
      Polynomial.Bivariate.swap (mapBivariate f P) := by
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ => simpa only [map_add] using congrArg₂ (· + ·) hP hQ
    | monomial n p =>
      induction p using Polynomial.induction_on' with
      | add p q hp hq => simpa only [map_add] using congrArg₂ (· + ·) hp hq
      | monomial m a =>
        simp [mapBivariate, Polynomial.Bivariate.swap_monomial]
  rw [hswap, bivariateEval_swap]
  exact Polynomial.eval₂_map _ _ _

/-- A finite coefficient-field annihilator survives denominator clearing and swapping. -/
theorem coefficient_bivariate_annihilator (f : F →+* K) {x : Extension K}
    (hx : letI := epsilonRatFuncAlgebraAlong f; IsAlgebraic (RatFunc F) x) :
    ∃ P : F[X][X], P ≠ 0 ∧ bivariateEval K (mapBivariate f P) x = 0 := by
  letI := epsilonRatFuncAlgebraAlong f
  obtain ⟨p, hp, hroot⟩ := hx
  obtain ⟨Q, hQ, hQroot⟩ := clear_ratfunc_annihilator_along f hp hroot
  refine ⟨Polynomial.Bivariate.swap Q, ?_, ?_⟩
  · intro h
    exact hQ ((Polynomial.Bivariate.swap (R := F)).injective
      (h.trans (map_zero _).symm))
  · rw [bivariateEval_map_swap]
    exact hQroot

/-- One residue step preserves algebraicity over the smaller coefficient field F. -/
theorem tower_coefficient_algebraic_relativeResidue (k : ℕ)
    {F : Type*} [Field F] (f : F →+* Tower realModel k)
    {x : Extension (Tower realModel k)} (hx : BaseBounded (Tower realModel k) x)
    (halg : letI := epsilonRatFuncAlgebraAlong f; IsAlgebraic (RatFunc F) x) :
    ∃ q : Tower realModel k, HasRelativeResidue (Tower realModel k) x q ∧
      (letI := f.toAlgebra; IsAlgebraic F q) := by
  obtain ⟨P, hP, hroot⟩ := coefficient_bivariate_annihilator f halg
  obtain ⟨n, Q, hQ, heq⟩ := extract_initial_X_power P hP
  have hrootQ : bivariateEval (Tower realModel k) (mapBivariate f Q) x = 0 := by
    unfold bivariateEval at hroot ⊢
    rw [heq, map_mul, map_pow] at hroot
    have hX : mapBivariate f Polynomial.X = Polynomial.X := Polynomial.map_X _
    rw [hX, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X] at hroot
    exact (mul_eq_zero.mp hroot).resolve_left (pow_ne_zero _ (epsilon_pos _).ne')
  have hQmap : ((mapBivariate f Q).coeff 0) ≠ 0 := by
    rw [mapBivariate_coeff]
    exact (Polynomial.map_ne_zero_iff f.injective).mpr hQ
  obtain ⟨B, hB, hbound⟩ := hx
  obtain ⟨q, hq, hres⟩ := tower_relativeResidue_of_infinitesimal_polynomial k hQmap hbound
    (constantCoefficient_small_of_annihilator _ _ ⟨B, hB, hbound⟩ hrootQ)
  refine ⟨q, hres, ?_⟩
  letI := f.toAlgebra
  refine ⟨Q.coeff 0, hQ, ?_⟩
  change (Q.coeff 0).eval₂ f q = 0
  rw [Polynomial.eval₂_eq_eval_map]
  rw [mapBivariate_coeff] at hq
  exact hq

#print axioms tower_coefficient_algebraic_relativeResidue
end W3.Infinitesimal
