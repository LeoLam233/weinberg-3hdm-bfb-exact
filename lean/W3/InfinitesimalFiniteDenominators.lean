import W3.InfinitesimalRationalPresentation

/-! # Explicit finite denominator clearing
The output coefficients are finite products of the exact numerator/denominator
presentation of each rational-function coefficient; no unspecified localization
choice is used in this arithmetic routine.
-/
noncomputable section
namespace W3.Infinitesimal
open Polynomial

variable {F : Type*} [Field F]

def denominatorProduct (p : (RatFunc F)[X]) : F[X] :=
  ∏ i ∈ p.support, (p.coeff i).denom

def clearFiniteDenominators (p : (RatFunc F)[X]) : F[X][X] :=
  ∑ i ∈ p.support, Polynomial.monomial i
    ((p.coeff i).num * ∏ j ∈ p.support.erase i, (p.coeff j).denom)

lemma denominatorProduct_ne_zero (p : (RatFunc F)[X]) : denominatorProduct p ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => RatFunc.denom_ne_zero (p.coeff i))

lemma clearFiniteDenominators_map (p : (RatFunc F)[X]) :
    (clearFiniteDenominators p).map (algebraMap F[X] (RatFunc F)) =
      Polynomial.C (algebraMap F[X] (RatFunc F) (denominatorProduct p)) * p := by
  classical
  let f := algebraMap F[X] (RatFunc F)
  change (clearFiniteDenominators p).map f = Polynomial.C (f (denominatorProduct p)) * p
  conv_rhs => arg 2; rw [p.as_sum_support]
  rw [Finset.mul_sum]
  unfold clearFiniteDenominators
  rw [Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.map_monomial]
  have hprod : (p.coeff i).denom * (∏ j ∈ p.support.erase i, (p.coeff j).denom) =
      denominatorProduct p := Finset.mul_prod_erase _ _ hi
  have hnum : f (p.coeff i).num = p.coeff i * f (p.coeff i).denom := by
    have h := RatFunc.num_div_denom (p.coeff i)
    exact (div_eq_iff (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero _))).mp h
  rw [← Polynomial.C_mul_X_pow_eq_monomial, ← Polynomial.C_mul_X_pow_eq_monomial,
    map_mul, hnum, mul_assoc, ← map_mul, hprod, Polynomial.C_mul]
  ring

lemma clearFiniteDenominators_ne_zero {p : (RatFunc F)[X]} (hp : p ≠ 0) :
    clearFiniteDenominators p ≠ 0 := by
  intro h
  have he := clearFiniteDenominators_map p
  rw [h, Polynomial.map_zero] at he
  exact (mul_ne_zero (Polynomial.C_ne_zero.mpr
    (RatFunc.algebraMap_ne_zero (denominatorProduct_ne_zero p))) hp) he.symm

lemma clearFiniteDenominators_eval₂ {L : Type*} [Field L] (f : RatFunc F →+* L)
    (p : (RatFunc F)[X]) {x : L} (hx : p.eval₂ f x = 0) :
    (clearFiniteDenominators p).eval₂ (f.comp (algebraMap F[X] (RatFunc F))) x = 0 := by
  have h := congrArg (Polynomial.eval₂RingHom f x) (clearFiniteDenominators_map p)
  simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_map,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, hx, mul_zero] at h
  exact h

#print axioms clearFiniteDenominators_map
#print axioms clearFiniteDenominators_eval₂
end W3.Infinitesimal
