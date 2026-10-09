import W3.InfinitesimalExtension
import Mathlib.Algebra.Order.Ring.StandardPart

/-!
# The genuine real standard-part bridge

The residue map below is constructed from Mathlib's finite valuation ring and
its residue field. This is a genuine order-preserving ring homomorphism on the
bounded elements. It is not a finite algebraic residue algorithm over a general
preceding non-Archimedean field, and is not labeled as that algorithm.
-/

noncomputable section
namespace W3.Infinitesimal
open ArchimedeanClass

variable {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]

/-- The canonical real residue on the ring of finite elements. -/
def realResidue : FiniteElement L →+*o ℝ :=
  OrderRingHom.comp Classical.ofNonempty FiniteResidueField.mk

theorem realResidue_eq_stdPart (x : FiniteElement L) :
    realResidue x = stdPart x.val := by
  symm
  exact stdPart_of_mk_nonneg Classical.ofNonempty x.property

/-- Embedded real coefficients are fixed by the residue. -/
theorem realResidue_real (ι : ℝ →+*o L) (r : ℝ) :
    realResidue (FiniteElement.mk (ι r) (mk_map_nonneg_of_archimedean ι r)) = r := by
  rw [realResidue_eq_stdPart]
  change stdPart (ι r) = r
  exact stdPart_map_real ι r

/-- Entrywise finite real bounds suffice for membership in the residue domain. -/
def boundedElement (ι : ℝ →+*o L) (x : L) {a b : ℝ}
    (ha : ι a ≤ x) (hb : x ≤ ι b) : FiniteElement L :=
  FiniteElement.mk x (mk_nonneg_of_le_of_le_of_archimedean ι ha hb)

/-- A genuine positive real-relative infinitesimal has zero residue. -/
theorem stdPart_infinitesimal (ι : ℝ →+*o L) {ε : L}
    (hε : PositiveInfinitesimal ι ε) : stdPart ε = 0 := by
  apply stdPart_eq ι
  · intro s hs
    have hs' : ι s ≤ 0 := by
      have h : ι s ≤ ι 0 := ι.monotone' hs.le
      simpa only [map_zero] using h
    exact hs'.trans hε.1.le
  · intro s hs
    exact (hε.2 s hs).le

/-- Equation (40) forces the real residue to be the original minimum.
No real-closedness, field construction, or candidate coverage is assumed here. -/
theorem stdPart_of_perturbation_bound (ι : ℝ →+*o L) {ε B y : L} {m : ℝ}
    (hε : PositiveInfinitesimal ι ε) (hB : B < ε)
    (hy : |y - ι m - ε| ≤ B) : stdPart y = m := by
  apply stdPart_eq ι
  · intro s hs
    have he := hε.2 ((m - s) / 3) (div_pos (sub_pos.mpr hs) (by norm_num))
    rw [map_div₀, map_sub, map_ofNat] at he
    have hl := (abs_le.mp hy).1
    have hepos := hε.1
    linarith
  · intro s hs
    have he := hε.2 ((s - m) / 3) (div_pos (sub_pos.mpr hs) (by norm_num))
    rw [map_div₀, map_sub, map_ofNat] at he
    have hu := (abs_le.mp hy).2
    have hepos := hε.1
    linarith

/-- Ring identities and nonnegative inequalities are preserved by actual residue. -/
theorem residue_preserves_equation {x y : FiniteElement L} (h : x = y) :
    realResidue x = realResidue y := congrArg realResidue h

theorem residue_preserves_nonneg {x : FiniteElement L} (h : 0 ≤ x) :
    0 ≤ realResidue x := by
  have h' : realResidue (0 : FiniteElement L) ≤ realResidue x :=
    (realResidue (L := L)).monotone' h
  simpa only [map_zero] using h'

#print axioms realResidue
#print axioms stdPart_of_perturbation_bound

end W3.Infinitesimal
