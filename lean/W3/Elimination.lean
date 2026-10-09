import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! Universal quadratic elimination used by the W3 phase spectrum. -/
namespace W3.Elimination

section Ring
variable {R : Type*} [CommRing R]

def quad (a b c u : R) : R := a * u ^ 2 + b * u + c

def linearOne (a b d e : R) : R := d * b - a * e

def linearZero (a c d f : R) : R := d * c - a * f

/-- The usual degree-(2,2) Sylvester resultant, including specialized lower-degree cases. -/
def resultant₂ (a b c d e f : R) : R :=
  (a * f - c * d) ^ 2 - (a * e - b * d) * (b * f - c * e)

theorem eliminate_linear (a b c d e f u : R)
    (hF : quad a b c u = 0) (hG : quad d e f u = 0) :
    linearOne a b d e * u + linearZero a c d f = 0 := by
  have h := congrArg₂ (fun x y : R => d * x - a * y) hF hG
  dsimp [quad, linearOne, linearZero] at *
  linear_combination h

theorem resultant_remainder_left (a b c d e f : R) :
    a * resultant₂ a b c d e f =
      a * (linearZero a c d f) ^ 2 -
      b * linearZero a c d f * linearOne a b d e +
      c * (linearOne a b d e) ^ 2 := by
  unfold resultant₂ linearZero linearOne
  ring

theorem resultant_remainder_right (a b c d e f : R) :
    d * resultant₂ a b c d e f =
      d * (linearZero a c d f) ^ 2 -
      e * linearZero a c d f * linearOne a b d e +
      f * (linearOne a b d e) ^ 2 := by
  unfold resultant₂ linearZero linearOne
  ring

/-- A common root annihilates the quadratic Sylvester determinant, without leading-term assumptions. -/
theorem common_root_resultant (a b c d e f u : R)
    (hF : quad a b c u = 0) (hG : quad d e f u = 0) :
    resultant₂ a b c d e f = 0 := by
  have hc : c = -(a * u ^ 2 + b * u) := by
    dsimp [quad] at hF
    linear_combination hF
  have hf : f = -(d * u ^ 2 + e * u) := by
    dsimp [quad] at hG
    linear_combination hG
  rw [hc, hf]
  unfold resultant₂
  ring

/-- Shifting the shared base point to zero supplies the universal factor. -/
theorem shifted_resultant_factor (a b c d e f t z x y : R)
    (hF : quad a b c t = z * x) (hG : quad d e f t = z * y) :
    resultant₂ a b c d e f =
      z * (z * (a * y - d * x) ^ 2 -
        (a * e - d * b) * ((b + 2 * a * t) * y - x * (e + 2 * d * t))) := by
  have hc : c = z * x - a * t ^ 2 - b * t := by
    dsimp [quad] at hF
    linear_combination hF
  have hf : f = z * y - d * t ^ 2 - e * t := by
    dsimp [quad] at hG
    linear_combination hG
  rw [hc, hf]
  unfold resultant₂
  ring

end Ring

section Field
variable {K : Type*} [Field K]

theorem recover_common_root (a b c d e f u : K)
    (hL : linearOne a b d e ≠ 0)
    (hF : quad a b c u = 0) (hG : quad d e f u = 0) :
    u = -linearZero a c d f / linearOne a b d e := by
  apply (eq_div_iff hL).2
  have h := eliminate_linear a b c d e f u hF hG
  linear_combination h

theorem resultant_root_recovers_left (a b c d e f : K)
    (hL : linearOne a b d e ≠ 0) (hR : resultant₂ a b c d e f = 0) :
    quad a b c (-linearZero a c d f / linearOne a b d e) = 0 := by
  dsimp [quad]
  field_simp
  have h := resultant_remainder_left a b c d e f
  rw [hR, mul_zero] at h
  linear_combination -h

theorem resultant_root_recovers_right (a b c d e f : K)
    (hL : linearOne a b d e ≠ 0) (hR : resultant₂ a b c d e f = 0) :
    quad d e f (-linearZero a c d f / linearOne a b d e) = 0 := by
  dsimp [quad]
  field_simp
  have h := resultant_remainder_right a b c d e f
  rw [hR, mul_zero] at h
  linear_combination -h

theorem unique_common_root (a b c d e f u v : K)
    (hL : linearOne a b d e ≠ 0)
    (huF : quad a b c u = 0) (huG : quad d e f u = 0)
    (hvF : quad a b c v = 0) (hvG : quad d e f v = 0) : u = v := by
  rw [recover_common_root a b c d e f u hL huF huG,
    recover_common_root a b c d e f v hL hvF hvG]

end Field
end W3.Elimination
