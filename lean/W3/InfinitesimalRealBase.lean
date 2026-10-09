import W3.InfinitesimalRealClosed
import W3.InfinitesimalTower
import W3.InfinitesimalRealClosedReal

/-! # The real base and the actual sixteen-level real-closed field. -/
noncomputable section
namespace W3.Infinitesimal
open Polynomial

/-- Every finite stage of the constructed real tower is real closed. -/
instance realTowerIsRealClosed (n : ℕ) : IsRealClosed (Tower realModel n) := by
  induction n with
  | zero => exact realIsRealClosed
  | succ n ih =>
    letI := ih
    exact extensionIsRealClosed (Tower realModel n)

example : IsRealClosed SixteenLevelField := inferInstance
#print axioms realIsRealClosed
#print axioms realTowerIsRealClosed
end W3.Infinitesimal
