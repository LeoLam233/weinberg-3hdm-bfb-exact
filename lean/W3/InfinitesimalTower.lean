import W3.InfinitesimalExtension
import Mathlib.Basic.Real.Basic

/-! # Explicit finite iteration of the ordered-field construction
This is an actual recursively constructed field tower, not an existence axiom.
It is not yet a real-closed algebraic Puiseux tower.
-/
noncomputable section
namespace W3.Infinitesimal

universe u

/-- A bundled ordered field, used only to keep recursive instance data coherent. -/
structure OrderedFieldModel where
  Carrier : Type u
  instField : Field Carrier
  instLinearOrder : LinearOrder Carrier
  instStrictOrderedRing : @IsStrictOrderedRing Carrier instField.toSemiring instLinearOrder.toPartialOrder

attribute [instance] OrderedFieldModel.instField OrderedFieldModel.instLinearOrder
  OrderedFieldModel.instStrictOrderedRing

/-- The already-proved ultrapower step, as a bundled ordered field. -/
def extendModel (M : OrderedFieldModel) : OrderedFieldModel where
  Carrier := Extension M.Carrier
  instField := inferInstance
  instLinearOrder := inferInstance
  instStrictOrderedRing := inferInstance

/-- A finite but arbitrarily long actual tower. -/
def towerModel (M : OrderedFieldModel) : ℕ → OrderedFieldModel
  | 0 => M
  | n + 1 => extendModel (towerModel M n)

abbrev Tower (M : OrderedFieldModel) (n : ℕ) := (towerModel M n).Carrier

/-- The embedding at each consecutive level. -/
def stepEmbed (M : OrderedFieldModel) (n : ℕ) : Tower M n →+*o Tower M (n + 1) :=
  embed (Tower M n)

/-- The new infinitesimal at level n+1. -/
def stepEpsilon (M : OrderedFieldModel) (n : ℕ) : Tower M (n + 1) :=
  epsilon (Tower M n)

theorem stepEpsilon_infinitesimal (M : OrderedFieldModel) (n : ℕ) :
    PositiveInfinitesimal (stepEmbed M n) (stepEpsilon M n) :=
  epsilon_is_positiveInfinitesimal (Tower M n)

/-- Embedding of the original base field into every level. -/
def baseEmbed (M : OrderedFieldModel) : (n : ℕ) → M.Carrier →+*o Tower M n
  | 0 => OrderRingHom.id M.Carrier
  | n + 1 => (stepEmbed M n).comp (baseEmbed M n)

def realModel : OrderedFieldModel where
  Carrier := ℝ
  instField := inferInstance
  instLinearOrder := inferInstance
  instStrictOrderedRing := inferInstance

/-- Sixteen actual levels, indexed by epsilon_0 through epsilon_15. -/
abbrev SixteenLevelField := Tower realModel 16

/-- The final real embedding is constructed, not assumed. -/
def realEmbedding16 : ℝ →+*o SixteenLevelField := baseEmbed realModel 16

/-- In particular, epsilon_15 is smaller than every positive element at level 15. -/
theorem last_epsilon_full_dominance {r : Tower realModel 15} (hr : 0 < r) :
    stepEpsilon realModel 15 < stepEmbed realModel 15 r :=
  (stepEpsilon_infinitesimal realModel 15).2 r hr

#print axioms last_epsilon_full_dominance

end W3.Infinitesimal
