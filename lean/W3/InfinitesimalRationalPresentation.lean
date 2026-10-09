import W3.InfinitesimalTranscendence
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Localization.Integral

/-! # The exact rational-function coefficient field and denominator clearing
The embedding evaluates the rational indeterminate at the actual transcendental
epsilon, so every nonzero denominator remains nonzero.
-/
noncomputable section
namespace W3.Infinitesimal
open Polynomial
open scoped nonZeroDivisors

variable (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def epsilonPolynomialHom : K[X] →+* Extension K :=
  Polynomial.eval₂RingHom (embed K).toRingHom (epsilon K)

theorem epsilonPolynomialHom_injective : Function.Injective (epsilonPolynomialHom K) :=
  transcendental_iff_injective.mp (epsilon_transcendental K)

theorem epsilonPolynomialHom_nonZeroDivisors :
    K[X]⁰ ≤ (Extension K)⁰.comap (epsilonPolynomialHom K) := by
  intro p hp
  change epsilonPolynomialHom K p ∈ (Extension K)⁰
  rw [mem_nonZeroDivisors_iff_ne_zero] at hp ⊢
  intro h
  apply hp
  apply epsilonPolynomialHom_injective K
  simpa only [map_zero] using h

/-- A genuine field embedding of E(epsilon) into the constructed extension of E. -/
def epsilonRatFuncHom : RatFunc K →+* Extension K :=
  RatFunc.liftRingHom (epsilonPolynomialHom K) (epsilonPolynomialHom_nonZeroDivisors K)

@[instance_reducible] def epsilonRatFuncAlgebra : Algebra (RatFunc K) (Extension K) :=
  (epsilonRatFuncHom K).toAlgebra

@[simp] lemma epsilonRatFuncHom_polynomial (p : K[X]) :
    epsilonRatFuncHom K (algebraMap K[X] (RatFunc K) p) = epsilonPolynomialHom K p :=
  RatFunc.liftRingHom_algebraMap _ _ p

lemma epsilonRatFuncHom_comp_polynomial :
    (epsilonRatFuncHom K).comp (algebraMap K[X] (RatFunc K)) = epsilonPolynomialHom K :=
  RatFunc.liftRingHom_comp_algebraMap _ _

/-- Clear all rational-function denominators of a selected annihilator.
The resulting two-variable polynomial is nonzero and still annihilates the
selected x; no rational-interval approximation is introduced. -/
theorem clear_ratfunc_annihilator {p : (RatFunc K)[X]} (hp : p ≠ 0)
    {x : Extension K} (hroot : p.eval₂ (epsilonRatFuncHom K) x = 0) :
    ∃ P : K[X][X], P ≠ 0 ∧ P.eval₂ (epsilonPolynomialHom K) x = 0 := by
  let P : K[X][X] := IsLocalization.integerNormalization K[X]⁰ p
  have hP : P ≠ 0 := by
    intro h
    apply hp
    exact (IsLocalization.integerNormalization_eq_zero_iff (M := K[X]⁰) le_rfl p).mp h
  refine ⟨P, hP, ?_⟩
  have h := IsLocalization.integerNormalization_eval₂_eq_zero K[X]⁰
    (epsilonRatFuncHom K) p hroot
  rwa [epsilonRatFuncHom_comp_polynomial] at h

/-- Algebraicity over the actual rational-function field supplies a nonzero
finite polynomial annihilator before denominator clearing. -/
theorem ratfunc_algebraic_cleared_annihilator {x : Extension K}
    (hx : letI := epsilonRatFuncAlgebra K; IsAlgebraic (RatFunc K) x) :
    ∃ P : K[X][X], P ≠ 0 ∧ P.eval₂ (epsilonPolynomialHom K) x = 0 := by
  letI := epsilonRatFuncAlgebra K
  obtain ⟨p, hp, hroot⟩ := hx
  exact clear_ratfunc_annihilator K hp hroot

#print axioms epsilonRatFuncHom
#print axioms ratfunc_algebraic_cleared_annihilator
end W3.Infinitesimal
