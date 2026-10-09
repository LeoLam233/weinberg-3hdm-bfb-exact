import W3.InfinitesimalTranscendence
import W3.InfinitesimalRealClosed
import W3.InfinitesimalHierarchy
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Data.Set.Finite.Lemmas

/-! # Finite-root ingredients for selected algebraic residues
These lemmas do not assert that an arbitrary bounded ultrapower element has a
residue in its non-Archimedean base field.
-/
noncomputable section
namespace W3.Infinitesimal
open Filter Polynomial

variable (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]

lemma polynomial_eval₂_germ (p : K[X]) (g : K → K) :
    p.eval₂ (embed K).toRingHom (germRingHom K g) =
      germRingHom K (fun i : K => p.eval (g i)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.eval₂_add, hp, hq]
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall (fun _ => Polynomial.eval_add.symm)
  | monomial n a =>
    rw [Polynomial.eval₂_monomial]
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall (fun _ => Polynomial.eval_monomial.symm)

/-- An ultrapower creates no new roots of a nonzero polynomial with base-field
coefficients. The ultrafilter must select one of its finitely many base roots. -/
theorem constant_polynomial_root_is_embedded {p : K[X]} (hp : p ≠ 0)
    {x : Extension K} (hx : p.eval₂ (embed K).toRingHom x = 0) :
    ∃ q : K, p.IsRoot q ∧ x = embed K q := by
  induction x using Germ.inductionOn with
  | h g =>
    change p.eval₂ (embed K).toRingHom (germRingHom K g) = 0 at hx
    rw [polynomial_eval₂_germ] at hx
    have he : ∀ᶠ i in (extensionUltrafilter K : Filter K), p.IsRoot (g i) := Germ.coe_eq.mp hx
    have hex : ∀ᶠ i in (extensionUltrafilter K : Filter K),
        ∃ q ∈ {q : K | p.IsRoot q}, g i = q :=
      he.mono (fun i hi => ⟨g i, hi, rfl⟩)
    obtain ⟨q, hq, hg⟩ :=
      (Ultrafilter.eventually_exists_mem_iff (p.finite_setOfPred_isRoot hp)).mp hex
    exact ⟨q, hq, Germ.coe_eq.mpr hg⟩

/-- x has relative residue q if their difference is smaller in absolute value
than every positive base-field constant. This is a property, not an assumed map. -/
def HasRelativeResidue (x : Extension K) (q : K) : Prop :=
  ∀ δ : K, 0 < δ → |x - embed K q| < embed K δ

/-- Arbitrarily-close finite roots give one fixed root as residue: select a root
minimizing distance in the ordered extension, then compare to each approximation. -/
theorem relativeResidue_of_root_approximations {p : K[X]} (hp : p ≠ 0) {x : Extension K}
    (h : ∀ δ : K, 0 < δ → ∃ q : K, p.IsRoot q ∧ |x - embed K q| < embed K δ) :
    ∃ q : K, p.IsRoot q ∧ HasRelativeResidue K x q := by
  obtain ⟨q₀, hq₀, _⟩ := h 1 zero_lt_one
  obtain ⟨q, hq, hmin⟩ := Set.exists_min_image {q : K | p.IsRoot q}
    (fun q => |x - embed K q|) (p.finite_setOfPred_isRoot hp) ⟨q₀, hq₀⟩
  refine ⟨q, hq, ?_⟩
  intro δ hδ
  obtain ⟨r, hr, hclose⟩ := h δ hδ
  exact (hmin r hr).trans_lt hclose

lemma relativeResidue_lt {x : Extension K} {q r : K}
    (hx : HasRelativeResidue K x q) (hqr : q < r) : x < embed K r := by
  have h := hx (r - q) (sub_pos.mpr hqr)
  rw [map_sub] at h
  have hu := (abs_lt.mp h).2
  linarith

lemma lt_relativeResidue {x : Extension K} {q r : K}
    (hx : HasRelativeResidue K x q) (hrq : r < q) : embed K r < x := by
  have h := hx (q - r) (sub_pos.mpr hrq)
  rw [map_sub] at h
  have hl := (abs_lt.mp h).1
  linarith

theorem relativeResidue_unique {x : Extension K} {q r : K}
    (hq : HasRelativeResidue K x q) (hr : HasRelativeResidue K x r) : q = r := by
  rcases lt_trichotomy q r with h | h | h
  · obtain ⟨s, hqs, hsr⟩ := exists_between h
    exact ((relativeResidue_lt K hq hqs).not_gt (lt_relativeResidue K hr hsr)).elim
  · exact h
  · obtain ⟨s, hrs, hsq⟩ := exists_between h
    exact ((relativeResidue_lt K hr hrs).not_gt (lt_relativeResidue K hq hsq)).elim

/-- Exact comparisons with any non-root cut, including the midpoints between
consecutive distinct roots, identify the selected residue without a tolerance. -/
theorem residue_comparison_at_nonroot {p : K[X]} {x : Extension K} {q r : K}
    (hq : p.IsRoot q) (hr : ¬p.IsRoot r) (hx : HasRelativeResidue K x q) :
    (x < embed K r ↔ q < r) := by
  constructor
  · intro hxr
    rcases lt_trichotomy q r with h | h | h
    · exact h
    · exact (hr (h ▸ hq)).elim
    · exact (hxr.not_gt (lt_relativeResidue K hx h)).elim
  · exact relativeResidue_lt K hx

#print axioms constant_polynomial_root_is_embedded
#print axioms relativeResidue_of_root_approximations
#print axioms residue_comparison_at_nonroot
end W3.Infinitesimal
