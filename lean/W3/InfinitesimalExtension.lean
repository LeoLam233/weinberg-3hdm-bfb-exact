import W3.InfinitesimalSigns
import Mathlib.Order.Filter.FilterProduct
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# An actual ordered-field infinitesimal extension

This constructs an ultrapower indexed by the entire preceding ordered field, with
an ultrafilter extending `atTop`. It therefore works over non-Archimedean base
fields: the new epsilon is below *every* positive base-field element.
No real-closedness or algebraic residue algorithm is claimed in this module.
-/

noncomputable section

namespace W3.Infinitesimal
open Filter

variable (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- An ultrafilter extending the unbounded tails of the complete base field. -/
def extensionUltrafilter : Ultrafilter K := Ultrafilter.of (atTop : Filter K)

/-- One genuine field extension, with coefficients modulo eventual equality. -/
def Extension : Type _ := Germ (extensionUltrafilter K : Filter K) K

instance extensionField : Field (Extension K) := inferInstanceAs (Field (Germ _ _))
instance extensionLinearOrder : LinearOrder (Extension K) :=
  inferInstanceAs (LinearOrder (Germ _ _))
instance extensionIsStrictOrderedRing : IsStrictOrderedRing (Extension K) :=
  inferInstanceAs (IsStrictOrderedRing (Germ _ _))

/-- Canonical order-preserving field embedding. -/
def embed : K →+*o Extension K where
  toFun := Germ.const
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  monotone' _ _ := Germ.const_le_iff.mpr

@[simp] theorem embed_lt_iff {x y : K} : embed K x < embed K y ↔ x < y :=
  Germ.const_lt_iff

@[simp] theorem embed_le_iff {x y : K} : embed K x ≤ embed K y ↔ x ≤ y :=
  Germ.const_le_iff

/-- The germ of the index exceeds every base-field constant. -/
def omega : Extension K := ((fun x : K => x) : Germ (extensionUltrafilter K : Filter K) K)

theorem embed_lt_omega (r : K) : embed K r < omega K := by
  apply Germ.coe_lt.mpr
  exact (eventually_gt_atTop r).filter_mono (Ultrafilter.of_le (atTop : Filter K))

theorem omega_pos : 0 < omega K := by
  simpa only [map_zero] using embed_lt_omega K 0

/-- The inverse index is the new, strictly positive infinitesimal. -/
def epsilon : Extension K := (omega K)⁻¹

theorem epsilon_pos : 0 < epsilon K := inv_pos.mpr (omega_pos K)

theorem epsilon_lt_embed {r : K} (hr : 0 < r) : epsilon K < embed K r := by
  have hr' : 0 < embed K r := by simpa only [map_zero] using (embed_lt_iff K).mpr hr
  have hinf := embed_lt_omega K r⁻¹
  rw [map_inv₀] at hinf
  exact (inv_lt_comm₀ (omega_pos K) hr').mpr hinf

/-- The full non-Archimedean-strength infinitesimal condition is derived,
not postulated. -/
theorem epsilon_is_positiveInfinitesimal : PositiveInfinitesimal (embed K) (epsilon K) :=
  ⟨epsilon_pos K, fun _ hr => epsilon_lt_embed K hr⟩

/-- A later infinitesimal is smaller even than the earlier infinitesimal divided
by any positive base-field factor. -/
theorem nested_epsilon_dominance {C : Extension K} (hC : 0 < C) :
    epsilon (Extension K) < embed (Extension K) (epsilon K / C) :=
  epsilon_lt_embed (Extension K) (div_pos (epsilon_pos K) hC)

#print axioms epsilon_is_positiveInfinitesimal
#print axioms nested_epsilon_dominance

end W3.Infinitesimal
