import W3.InfinitesimalFiniteResidue
import W3.InfinitesimalFiniteDenominators
import W3.InfinitesimalPresentedExpression

/-! # A finite residue program retaining the smaller coefficient presentation
Normalize before embedding coefficients, so the selected output comes with a
nonzero root equation over the preceding rational presentation.
-/
noncomputable section
namespace W3.Infinitesimal
open Polynomial

variable {F K : Type*} [Field F] [DecidableEq F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Explicit annihilator transformation: finite numerator/denominator products,
followed by swapping epsilon and the selected-value variable. -/
def clearedBivariate (p : (RatFunc F)[X]) : F[X][X] :=
  Polynomial.Bivariate.swap (clearFiniteDenominators p)

lemma clearedBivariate_ne_zero {p : (RatFunc F)[X]} (hp : p ≠ 0) : clearedBivariate p ≠ 0 := by
  intro h
  exact clearFiniteDenominators_ne_zero hp ((Polynomial.Bivariate.swap (R := F)).injective
    (h.trans (map_zero _).symm))

lemma clearedBivariate_root (f : F →+* K) (p : (RatFunc F)[X]) {x : Extension K}
    (hroot : p.eval₂ (epsilonRatFuncHomAlong f) x = 0) :
    bivariateEval K (mapBivariate f (clearedBivariate p)) x = 0 := by
  rw [clearedBivariate, bivariateEval_map_swap]
  have h := clearFiniteDenominators_eval₂ (epsilonRatFuncHomAlong f) p hroot
  rwa [show (epsilonRatFuncHomAlong f).comp (algebraMap F[X] (RatFunc F)) =
      epsilonPolynomialHomAlong f from RatFunc.liftRingHom_comp_algebraMap _ _] at h

/-- Input polynomial coefficients and normalization stay in F; only root solving
and comparisons are interpreted in the preceding ordered field K. -/
def coefficientResidueProgram (f : F →+* K) (oracle : RealRootEnumeration K)
    (P : F[X][X]) (x : Extension K) : Option K :=
  selectEnumeratedRoot K x (oracle.roots (((normalizeInitial P).2.coeff 0).map f))

/-- The program returns the unique residue together with its actual normalized
nonzero root equation over the smaller coefficient field. -/
theorem coefficientResidueProgram_correct (k : ℕ)
    {F : Type*} [Field F] [DecidableEq F] (f : F →+* Tower realModel k)
    (oracle : RealRootEnumeration (Tower realModel k)) (P : F[X][X]) (hP : P ≠ 0)
    {x : Extension (Tower realModel k)} (hx : BaseBounded (Tower realModel k) x)
    (hroot : bivariateEval (Tower realModel k) (mapBivariate f P) x = 0) :
    ∃ q : Tower realModel k,
      coefficientResidueProgram f oracle P x = some q ∧
      HasRelativeResidue (Tower realModel k) x q ∧
      ((normalizeInitial P).2.coeff 0).eval₂ f q = 0 := by
  obtain ⟨hQ, heq⟩ := normalizeInitial_correct P hP
  have hrootQ : bivariateEval (Tower realModel k) (mapBivariate f (normalizeInitial P).2) x = 0 := by
    unfold bivariateEval at hroot ⊢
    rw [heq, map_mul, map_pow] at hroot
    have hX : mapBivariate f Polynomial.X = Polynomial.X := Polynomial.map_X _
    rw [hX, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X] at hroot
    exact (mul_eq_zero.mp hroot).resolve_left (pow_ne_zero _ (epsilon_pos _).ne')
  have hQmap : ((mapBivariate f (normalizeInitial P).2).coeff 0) ≠ 0 := by
    rw [mapBivariate_coeff]
    exact (Polynomial.map_ne_zero_iff f.injective).mpr hQ
  obtain ⟨B, hB, hbound⟩ := hx
  obtain ⟨q, hq, hres⟩ := tower_relativeResidue_of_infinitesimal_polynomial k hQmap hbound
    (constantCoefficient_small_of_annihilator _ _ ⟨B, hB, hbound⟩ hrootQ)
  rw [mapBivariate_coeff] at hQmap hq
  exact ⟨q, selectEnumeratedRoot_eq _ oracle hQmap hq hres, hres,
    (Polynomial.eval_map f q).symm.trans hq⟩

/-- Crucially, the output has a finite selected-root expression over F, using
exactly the normalized polynomial computed by this residue step. -/
theorem coefficientResidueProgram_output_presented (k : ℕ)
    {F : Type*} [Field F] [DecidableEq F] (f : F →+* Tower realModel k)
    (oracle : RealRootEnumeration (Tower realModel k)) (P : F[X][X]) (hP : P ≠ 0)
    {x : Extension (Tower realModel k)} (hx : BaseBounded (Tower realModel k) x)
    (hroot : bivariateEval (Tower realModel k) (mapBivariate f P) x = 0) :
    ∃ q : Tower realModel k,
      coefficientResidueProgram f oracle P x = some q ∧
      HasRelativeResidue (Tower realModel k) x q ∧
      (letI := f.toAlgebra; Presented F q) := by
  obtain ⟨q, hprog, hres, hrootq⟩ := coefficientResidueProgram_correct k f oracle P hP hx hroot
  refine ⟨q, hprog, hres, ?_⟩
  letI := f.toAlgebra
  exact presented_selectedRoot ((normalizeInitial P).2.coeff 0)
    (normalizeInitial_correct P hP).1 hrootq

#print axioms coefficientResidueProgram_output_presented
end W3.Infinitesimal
