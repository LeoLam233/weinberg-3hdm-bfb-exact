import W3.OperatorModel
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Field-gradient stationarity derived from the full complex polynomial and
unconstrained homogeneous normalization, without a Lagrange multiplier assumption. -/
noncomputable section
namespace W3.Operator
open ComplexConjugate Matrix
open scoped BigOperators

/-- Real Euclidean pairing on the actual twelve-real-dimensional field space. -/
def fieldPair (φ ψ : W3.Fields) : ℝ :=
  ∑ k : Fin 2, ∑ i : Fin 3, (conj (φ (k,i)) * ψ (k,i)).re

lemma fieldPair_self (φ : W3.Fields) : fieldPair φ φ = ‖φ‖ ^ 2 := by
  rw [← W3.total_radius]
  simp only [fieldPair, W3.radius, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  exact Finset.sum_comm

lemma fieldPair_sub_smul (φ ψ χ : W3.Fields) (t : ℝ) :
    fieldPair φ (ψ - t • χ) = fieldPair φ ψ - t * fieldPair φ χ := by
  simp [fieldPair, Fin.sum_univ_two, Fin.sum_univ_three]
  ring

/-- Action of a Hermitian 3×3 matrix on the right of the two-row field matrix. -/
def fieldAction (X : Coordinates) (φ : W3.Fields) : W3.Fields :=
  WithLp.toLp 2 (fun ki => ∑ j : Fin 3, φ (ki.1,j) * coordinateMatrix X j ki.2)

def fieldCross (φ ψ : W3.Fields) : Coordinates :=
  (fun i => 2 * ∑ k : Fin 2, (conj (φ (k,i)) * ψ (k,i)).re,
    ![∑ k : Fin 2, (conj (φ (k,0)) * ψ (k,1) + conj (ψ (k,0)) * φ (k,1)),
      ∑ k : Fin 2, (conj (φ (k,0)) * ψ (k,2) + conj (ψ (k,0)) * φ (k,2)),
      ∑ k : Fin 2, (conj (φ (k,1)) * ψ (k,2) + conj (ψ (k,1)) * φ (k,2))])

/-- Exact affine-field Gram expansion, including every complex phase. -/
theorem fieldCoordinates_affine (φ ψ : W3.Fields) (t : ℝ) :
    fieldCoordinates (φ + t • ψ) =
      fieldCoordinates φ + t • fieldCross φ ψ + (t ^ 2) • fieldCoordinates ψ := by
  apply Prod.ext
  · funext i
    simp [fieldCoordinates, fieldCross, W3.radius, Fin.sum_univ_two,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_two]
    ring
  · funext i
    fin_cases i <;> apply Complex.ext <;>
      simp [fieldCoordinates, fieldCross, W3.gram, Fin.sum_univ_two,
        Complex.mul_re, Complex.mul_im, pow_two] <;> ring

/-- The exact first variation is the matrix field gradient 2 Φ L(K). -/
theorem cross_pair_action (φ ψ : W3.Fields) (X : Coordinates) :
    coordinatePair (fieldCross φ ψ) X = 2 * fieldPair ψ (fieldAction X φ) := by
  simp [coordinatePair, fieldCross, fieldPair, fieldAction, coordinateMatrix,
    Fin.sum_univ_two, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im]
  ring

lemma field_norm_sq_affine (φ ψ : W3.Fields) (t : ℝ) :
    ‖φ + t • ψ‖ ^ 2 = ‖φ‖ ^ 2 + 2 * t * fieldPair ψ φ + t ^ 2 * ‖ψ‖ ^ 2 := by
  rw [← W3.total_radius, ← W3.total_radius, ← W3.total_radius]
  simp [W3.radius, fieldPair, Fin.sum_univ_two, Fin.sum_univ_three,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_two]
  ring

/-- A degree-four expansion in one real direction; no limit is hidden in the statement. -/
theorem coordinateEnergy_affine_quadratic (κ : W3.Couplings) (x h y : Coordinates) (t : ℝ) :
    coordinateEnergy κ (x + t • h + t ^ 2 • y) =
      coordinateEnergy κ x + t * coordinatePair h (couplingOperator κ x) +
      t ^ 2 * (coordinatePair y (couplingOperator κ x) + coordinateEnergy κ h) +
      t ^ 3 * coordinatePair y (couplingOperator κ h) + t ^ 4 * coordinateEnergy κ y := by
  have hs (u v : Coordinates) :
      coordinateBilinear u (couplingOperator κ v) =
        coordinateBilinear v (couplingOperator κ u) := by
    change coordinatePair u _ = coordinatePair v _
    rw [couplingOperator_selfadjoint, coordinatePair_symmetric]
  simp only [coordinateEnergy_eq_half_pair, ← coordinateBilinear_apply,
    map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hs x h, hs x y, hs h y]
  ring

lemma polynomial4_derivative (a b c d e : ℝ) :
    HasDerivAt (fun t : ℝ => a + t * b + t ^ 2 * c + t ^ 3 * d + t ^ 4 * e) b 0 := by
  convert ((((hasDerivAt_const (0 : ℝ) a).add ((hasDerivAt_id (0 : ℝ)).mul_const b)).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const c)).add
    (((hasDerivAt_id (0 : ℝ)).pow 3).mul_const d)).add
    (((hasDerivAt_id (0 : ℝ)).pow 4).mul_const e) using 1 <;> norm_num <;> rfl

/-- Actual directional derivative of the source quartic in all field directions. -/
theorem quartic_directional_derivative (κ : W3.Couplings) (φ ψ : W3.Fields) :
    HasDerivAt (fun t : ℝ => W3.quartic κ (φ + t • ψ))
      (2 * fieldPair ψ (fieldAction (couplingOperator κ (fieldCoordinates φ)) φ)) 0 := by
  have h := polynomial4_derivative (coordinateEnergy κ (fieldCoordinates φ))
    (coordinatePair (fieldCross φ ψ) (couplingOperator κ (fieldCoordinates φ)))
    (coordinatePair (fieldCoordinates ψ) (couplingOperator κ (fieldCoordinates φ)) +
      coordinateEnergy κ (fieldCross φ ψ))
    (coordinatePair (fieldCoordinates ψ) (couplingOperator κ (fieldCross φ ψ)))
    (coordinateEnergy κ (fieldCoordinates ψ))
  simp only [cross_pair_action] at h
  convert h using 1
  funext t
  rw [quartic_eq_coordinateEnergy, fieldCoordinates_affine, coordinateEnergy_affine_quadratic,
    cross_pair_action]

lemma norm_four_directional_derivative (φ ψ : W3.Fields) :
    HasDerivAt (fun t : ℝ => ‖φ + t • ψ‖ ^ 4)
      (4 * ‖φ‖ ^ 2 * fieldPair ψ φ) 0 := by
  have h := (((hasDerivAt_const (0 : ℝ) (‖φ‖ ^ 2)).add
    ((hasDerivAt_id (0 : ℝ)).mul_const (2 * fieldPair ψ φ))).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (‖ψ‖ ^ 2))).pow 2
  convert h using 1
  · funext t
    change ‖φ + t • ψ‖ ^ 4 = (‖φ‖ ^ 2 + t * (2 * fieldPair ψ φ) + t ^ 2 * ‖ψ‖ ^ 2) ^ 2
    rw [show ‖φ + t • ψ‖ ^ 4 = (‖φ + t • ψ‖ ^ 2) ^ 2 by ring,
      field_norm_sq_affine]
    ring
  · norm_num
    ring

/-- Homogeneity turns a normalized minimum into a global polynomial inequality. -/
theorem normalized_minimum_global_bound (κ : W3.Couplings) (φ : W3.Fields)
    (hmin : ∀ ψ : W3.Fields, ‖ψ‖ = 1 → W3.quartic κ φ ≤ W3.quartic κ ψ)
    (ψ : W3.Fields) :
    W3.quartic κ φ * ‖ψ‖ ^ 4 ≤ W3.quartic κ ψ := by
  by_cases hψ : ψ = 0
  · rw [hψ, norm_zero, zero_pow (by decide), mul_zero, W3.quartic_zero]
  have hn : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hψ
  have h := hmin ((‖ψ‖⁻¹ : ℝ) • ψ) (W3.normalized_norm ψ hψ)
  rw [W3.quartic_smul] at h
  calc
    W3.quartic κ φ * ‖ψ‖ ^ 4 ≤ ‖ψ‖ ^ 4 * (‖ψ‖⁻¹ ^ 4 * W3.quartic κ ψ) := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left h (pow_nonneg (norm_nonneg ψ) 4)
    _ = (‖ψ‖ * ‖ψ‖⁻¹) ^ 4 * W3.quartic κ ψ := by ring
    _ = W3.quartic κ ψ := by rw [mul_inv_cancel₀ hn]; norm_num

/-- Full field stationarity at every normalized global minimum. This does not
assume rank, support, operator invertibility, or Lagrange stationarity. -/
theorem normalized_minimum_field_stationarity (κ : W3.Couplings) (φ : W3.Fields)
    (hφ : ‖φ‖ = 1)
    (hmin : ∀ ψ : W3.Fields, ‖ψ‖ = 1 → W3.quartic κ φ ≤ W3.quartic κ ψ) :
    fieldAction (couplingOperator κ (fieldCoordinates φ)) φ = (2 * W3.quartic κ φ) • φ := by
  let G := fieldAction (couplingOperator κ (fieldCoordinates φ)) φ
  have hzero (ψ : W3.Fields) :
      2 * fieldPair ψ G - W3.quartic κ φ * (4 * ‖φ‖ ^ 2 * fieldPair ψ φ) = 0 := by
    have hd := (quartic_directional_derivative κ φ ψ).sub
      ((norm_four_directional_derivative φ ψ).const_mul (W3.quartic κ φ))
    have hm : IsLocalMin (fun t : ℝ => W3.quartic κ (φ + t • ψ) -
        W3.quartic κ φ * ‖φ + t • ψ‖ ^ 4) 0 := by
      apply Filter.Eventually.of_forall
      intro t
      simpa [hφ] using sub_nonneg.mpr
        (normalized_minimum_global_bound κ φ hmin (φ + t • ψ))
    exact hm.hasDerivAt_eq_zero hd
  have hp : fieldPair (G - (2 * W3.quartic κ φ) • φ)
      (G - (2 * W3.quartic κ φ) • φ) = 0 := by
    rw [fieldPair_sub_smul]
    have h := hzero (G - (2 * W3.quartic κ φ) • φ)
    rw [hφ] at h
    nlinarith
  rw [fieldPair_self] at hp
  have hz : G - (2 * W3.quartic κ φ) • φ = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (G - (2 * W3.quartic κ φ) • φ)]
  exact sub_eq_zero.mp hz

#print axioms quartic_directional_derivative
#print axioms normalized_minimum_field_stationarity
end W3.Operator
