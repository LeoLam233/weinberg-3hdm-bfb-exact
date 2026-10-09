import W3.InfinitesimalFiniteNormalization
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision

/-! A finite arithmetic construction of a monic annihilator for a selected
nonzero denominator's inverse. Initial X factors are removed by the previously
verified fuel-bounded coefficient algorithm, then coefficients are reversed
and the leading coefficient is inverted. No minimal-polynomial oracle is used. -/
noncomputable section
namespace W3.Infinitesimal
open Polynomial
variable {F L : Type*} [Field F] [Field L] [Algebra F L] [DecidableEq F]

/-- Explicit finite coefficient operations on the supplied annihilator. -/
def inverseAnnihilator (p : F[X]) : F[X] :=
  (normalizeInitial p).2.reverse * C ((normalizeInitial p).2.reverse.leadingCoeff)⁻¹

lemma normalizedInitial_ne_zero (p : F[X]) (hp : p ≠ 0) : (normalizeInitial p).2 ≠ 0 := by
  intro h
  have hc := (normalizeInitial_correct p hp).1
  exact hc (by rw [h,coeff_zero])

/-- Removing initial powers of X preserves a nonzero selected root. -/
lemma normalizedInitial_aeval (p : F[X]) (hp : p ≠ 0) (x : L)
    (hx : x ≠ 0) (hroot : aeval x p = 0) : aeval x (normalizeInitial p).2 = 0 := by
  have hf := (normalizeInitial_correct p hp).2
  rw [hf,map_mul,map_pow,aeval_X] at hroot
  exact (mul_eq_zero.mp hroot).resolve_left (pow_ne_zero _ hx)

theorem inverseAnnihilator_monic (p : F[X]) (hp : p ≠ 0) : (inverseAnnihilator p).Monic := by
  apply monic_mul_leadingCoeff_inv
  exact mt reverse_eq_zero.mp (normalizedInitial_ne_zero p hp)

theorem inverseAnnihilator_ne_zero (p : F[X]) (hp : p ≠ 0) : inverseAnnihilator p ≠ 0 :=
  (inverseAnnihilator_monic p hp).ne_zero

/-- The constructed monic polynomial annihilates the actual selected inverse. -/
theorem inverseAnnihilator_aeval (p : F[X]) (hp : p ≠ 0) (x : L)
    (hx : x ≠ 0) (hroot : aeval x p = 0) : aeval x⁻¹ (inverseAnnihilator p) = 0 := by
  have hq := normalizedInitial_aeval p hp x hx hroot
  letI : Invertible x := invertibleOfNonzero hx
  have hr := (eval₂_reverse_eq_zero_iff (algebraMap F L) x (normalizeInitial p).2).mpr hq
  have hr' : aeval x⁻¹ (normalizeInitial p).2.reverse = 0 := by
    simpa only [aeval_def,invOf_eq_inv] using hr
  simp only [inverseAnnihilator,map_mul,hr',zero_mul]

/-- A usable nonconstant root-adjunction polynomial, proved from the branch data. -/
theorem inverseAnnihilator_natDegree_pos (p : F[X]) (hp : p ≠ 0) (x : L)
    (hx : x ≠ 0) (hroot : aeval x p = 0) : 0 < (inverseAnnihilator p).natDegree := by
  exact natDegree_pos_of_aeval_root (inverseAnnihilator_ne_zero p hp)
    (inverseAnnihilator_aeval p hp x hx hroot) (fun a ha => (algebraMap F L).injective (by simpa using ha))

/-- Packaged finite root relation for use in a denominator adjunction. -/
theorem inverseAnnihilator_spec (p : F[X]) (hp : p ≠ 0) (x : L)
    (hx : x ≠ 0) (hroot : aeval x p = 0) :
    (inverseAnnihilator p).Monic ∧ 0 < (inverseAnnihilator p).natDegree ∧
      aeval x⁻¹ (inverseAnnihilator p) = 0 :=
  ⟨inverseAnnihilator_monic p hp,inverseAnnihilator_natDegree_pos p hp x hx hroot,
    inverseAnnihilator_aeval p hp x hx hroot⟩

#print axioms inverseAnnihilator_spec
end W3.Infinitesimal
