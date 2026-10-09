import W3.InfinitesimalExtension
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Algebraic.Basic

/-! # Every constructed epsilon is transcendental over its complete preceding field. -/
noncomputable section
namespace W3.Infinitesimal
open Filter Polynomial

variable (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]

instance extensionAlgebra : Algebra K (Extension K) := (embed K).toRingHom.toAlgebra

/-- Polynomial evaluation in the index germ is coordinatewise evaluation. -/
theorem eval₂_omega (p : K[X]) :
    p.eval₂ (embed K).toRingHom (omega K) =
      ((fun x : K => p.eval x) : Germ (extensionUltrafilter K : Filter K) K) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.eval₂_add, hp, hq]
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (fun x => Polynomial.eval_add.symm)
  | monomial n a =>
    rw [Polynomial.eval₂_monomial]
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (fun x => Polynomial.eval_monomial.symm)

/-- A nonzero base-field polynomial cannot vanish at the index germ. -/
theorem eval₂_omega_ne_zero {p : K[X]} (hp : p ≠ 0) :
    p.eval₂ (embed K).toRingHom (omega K) ≠ 0 := by
  rw [eval₂_omega]
  intro h
  have heval : ∀ᶠ x in (extensionUltrafilter K : Filter K), p.eval x = 0 :=
    Germ.coe_eq.mp h
  obtain ⟨b, hb⟩ := p.exists_max_root hp
  have htail : ∀ᶠ x in (extensionUltrafilter K : Filter K), b < x :=
    (eventually_gt_atTop b).filter_mono (Ultrafilter.of_le (atTop : Filter K))
  obtain ⟨x, hx, hx'⟩ := (heval.and htail).exists
  exact (hb x hx).not_gt hx'

theorem omega_transcendental : Transcendental K (omega K) := by
  rintro ⟨p, hp, heval⟩
  exact eval₂_omega_ne_zero K hp heval

/-- Full base-field transcendence, including when the base field is itself
non-Archimedean. Repeated construction thus adds a new independent variable. -/
theorem epsilon_transcendental : Transcendental K (epsilon K) := by
  intro h
  apply omega_transcendental K
  have hi := h.inv
  simpa only [epsilon, inv_inv] using hi

#print axioms epsilon_transcendental
end W3.Infinitesimal
