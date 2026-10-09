import W3.OperatorGenericCharged

/-! Independence of all charged scalar tests from square-root/sign choices. -/
noncomputable section
namespace W3.Operator
open ComplexConjugate Matrix
open W3.Weighted
open scoped BigOperators

/-- The source's sign-independent rank-one data: diagonal radii, off-diagonal
magnitudes, and squared off-diagonal phases. -/
def QuadraticCoordinatesEq (X Y : Coordinates) : Prop :=
  X.1 = Y.1 ∧ ∀ i, Complex.normSq (X.2 i) = Complex.normSq (Y.2 i) ∧ (X.2 i) ^ 2 = (Y.2 i) ^ 2

lemma block_pair_identity (c : ℝ) (d z : ℂ) :
    z.re * (block c d z).re + z.im * (block c d z).im =
      c * Complex.normSq z + (d * z ^ 2).re := by
  simp [block, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_two]
  ring

lemma block_normSq_identity (c : ℝ) (d z : ℂ) :
    Complex.normSq (block c d z) =
      (c ^ 2 + Complex.normSq d) * Complex.normSq z + 2 * c * (d * z ^ 2).re := by
  simp [block, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_two]
  ring

lemma coordinatePair_structured (A : Matrix (Fin 3) (Fin 3) ℝ)
    (c : Fin 3 → ℝ) (d : Fin 3 → ℂ) (X : Coordinates) :
    coordinatePair X (structuredLinear A c d X) =
      (∑ i, X.1 i * (A *ᵥ X.1) i) +
      2 * ∑ i, (c i * Complex.normSq (X.2 i) + (d i * X.2 i ^ 2).re) := by
  change (∑ i, X.1 i * (A *ᵥ X.1) i) +
    2 * ∑ i, ((X.2 i).re * (block (c i) (d i) (X.2 i)).re +
      (X.2 i).im * (block (c i) (d i) (X.2 i)).im) = _
  simp_rw [block_pair_identity]

lemma coordinatePair_self_sum (X : Coordinates) :
    coordinatePair X X = (∑ i, X.1 i ^ 2) + 2 * ∑ i, Complex.normSq (X.2 i) := by
  simp [coordinatePair, Complex.normSq_apply, pow_two]

lemma structured_pair_invariant (A : Matrix (Fin 3) (Fin 3) ℝ)
    (c : Fin 3 → ℝ) (d : Fin 3 → ℂ) (X Y : Coordinates) (h : QuadraticCoordinatesEq X Y) :
    coordinatePair X (structuredLinear A c d X) = coordinatePair Y (structuredLinear A c d Y) := by
  rw [coordinatePair_structured, coordinatePair_structured, h.1]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  rw [(h.2 i).1,(h.2 i).2]

lemma structured_norm_invariant (A : Matrix (Fin 3) (Fin 3) ℝ)
    (c : Fin 3 → ℝ) (d : Fin 3 → ℂ) (X Y : Coordinates) (h : QuadraticCoordinatesEq X Y) :
    coordinatePair (structuredLinear A c d X) (structuredLinear A c d X) =
      coordinatePair (structuredLinear A c d Y) (structuredLinear A c d Y) := by
  rw [coordinatePair_self_sum, coordinatePair_self_sum]
  change (∑ i, (A *ᵥ X.1) i ^ 2) + 2 * ∑ i, Complex.normSq (block (c i) (d i) (X.2 i)) =
    (∑ i, (A *ᵥ Y.1) i ^ 2) + 2 * ∑ i, Complex.normSq (block (c i) (d i) (Y.2 i))
  rw [h.1]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  rw [block_normSq_identity,block_normSq_identity,(h.2 i).1,(h.2 i).2]

lemma diagonal_pair_invariant (U X Y : Coordinates)
    (hU : ∀ i, U.2 i = 0) (hXY : X.1 = Y.1) : coordinatePair U X = coordinatePair U Y := by
  simp [coordinatePair,hU,hXY]

/-- All scalar data in equations (24) and (26) are unchanged by admissible
square-root choices. The proof uses the actual structured inverse operator. -/
theorem dual_scalars_invariant (A : Matrix (Fin 3) (Fin 3) ℝ)
    (c : Fin 3 → ℝ) (d : Fin 3 → ℂ) (hA : A.det ≠ 0)
    (hΔ : ∀ i, blockDet (c i) (d i) ≠ 0) (z w : Fin 3 → ℂ)
    (h : QuadraticCoordinatesEq (projectorCoordinates z) (projectorCoordinates w)) :
    let R := (structuredEquiv A c d hA hΔ).symm
    dualA R z = dualA R w ∧ dualP R z = dualP R w ∧ dualPurity R z = dualPurity R w := by
  dsimp only
  let R := (structuredEquiv A c d hA hΔ).symm
  have hU : ∀ i, (R identityCoordinates).2 i = 0 := by
    intro i
    simp [R,structuredEquiv_symm_apply,structuredInverse,identityCoordinates,inverseBlock]
  have ha : dualA R z = dualA R w := by
    unfold dualA
    rw [coordinatePair_symmetric (projectorCoordinates z), coordinatePair_symmetric (projectorCoordinates w)]
    exact diagonal_pair_invariant _ _ _ hU h.1
  have hp : dualP R z = dualP R w := by
    change coordinatePair _ (structuredInverse A c d _) = coordinatePair _ (structuredInverse A c d _)
    rw [structuredInverse_eq_linear, structuredInverse_eq_linear]
    exact structured_pair_invariant _ _ _ _ _ h
  have ha2 : coordinatePair (R identityCoordinates) (R (projectorCoordinates z)) =
      coordinatePair (R identityCoordinates) (R (projectorCoordinates w)) := by
    apply diagonal_pair_invariant _ _ _ hU
    change A⁻¹ *ᵥ (projectorCoordinates z).1 = A⁻¹ *ᵥ (projectorCoordinates w).1
    rw [h.1]
  have hp2 : coordinatePair (R (projectorCoordinates z)) (R (projectorCoordinates z)) =
      coordinatePair (R (projectorCoordinates w)) (R (projectorCoordinates w)) := by
    change coordinatePair (structuredInverse A c d _) (structuredInverse A c d _) =
      coordinatePair (structuredInverse A c d _) (structuredInverse A c d _)
    simp only [structuredInverse_eq_linear]
    exact structured_norm_invariant _ _ _ _ _ h
  refine ⟨ha,hp,?_⟩
  change dualPurity R z = dualPurity R w
  unfold dualPurity
  rw [ha,hp,ha2,hp2]

#print axioms dual_scalars_invariant
end W3.Operator
