import W3.ActualGenericity
import W3.InfinitesimalW3Minimum
import W3.InfinitesimalBoundsTransfer

/-! The source's strict sign tests for an actual attained deformed minimum,
with all physical perturbation bounds discharged. Spectrum identification is
proved separately; it is not silently assumed in this module. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace W3.Infinitesimal
open W3.RealModel

section Natural
variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Field L] [LinearOrder L] [IsStrictOrderedRing L]

lemma mass_map (ι : K →+* L) (x : RealFields K) :
    mass (fun i => ι (x i)) = ι (mass x) := by simp [mass]

lemma twiceQuartic_map (ι : K →+* L) (κ : Parameters K) (x : RealFields K) :
    twiceQuartic (fun i => ι (κ i)) (fun i => ι (x i)) = ι (twiceQuartic κ x) := by
  simp [twiceQuartic, radii, offRe, offIm, map_ofNat]

lemma quarticReal_map (ι : K →+* L) (κ : Parameters K) (x : RealFields K) :
    quarticReal (fun i => ι (κ i)) (fun i => ι (x i)) = ι (quarticReal κ x) := by
  simp only [quarticReal, twiceQuartic_map, map_div₀, map_ofNat]
end Natural

/-- Fixed real minima remain lower bounds on every extension direction. -/
theorem w3_real_lower_bound_tower (κ : Parameters ℝ) (m : ℝ)
    (hm : ∀ y : RealFields ℝ, mass y = 1 → m ≤ quarticReal κ y) :
    ∀ y : RealFields SixteenLevelField, mass y = 1 →
      realEmbedding16 m ≤ quarticReal (fun i => realEmbedding16 (κ i)) y := by
  have hb : PolynomialLowerBound potentialPolynomial w3DomainPolynomials κ (2*m) := by
    intro y hy
    have hmass : mass y = 1 := by
      have h := hy 0
      change intPolynomialEval massConstraintPolynomial y = 0 at h
      rw [w3_mass_intEval] at h
      exact sub_eq_zero.mp h
    rw [w3_potential_intEval]
    have h := hm y hmass
    dsimp only [quarticReal] at h
    linarith
  have he := polynomialLowerBound_tower potentialPolynomial w3DomainPolynomials realModel κ (2*m : ℝ) hb 16
  intro y hy
  have h := he y (fun j => by
    change intPolynomialEval massConstraintPolynomial y = 0
    rw [w3_mass_intEval, hy, sub_self])
  rw [w3_potential_intEval] at h
  change realEmbedding16 (2*m) ≤ twiceQuartic (fun j => realEmbedding16 (κ j)) y at h
  rw [map_mul, map_ofNat] at h
  dsimp only [quarticReal]
  linarith

/-- A canonical real minimizing point is chosen only from the proved compactness theorem. -/
def realMinimumPoint (κ : Parameters ℝ) : RealFields ℝ := (real_minimum κ).choose

def realMinimum (κ : Parameters ℝ) : ℝ := quarticReal κ (realMinimumPoint κ)

lemma realMinimumPoint_spec (κ : Parameters ℝ) : mass (realMinimumPoint κ) = 1 ∧
    ∀ y : RealFields ℝ, mass y = 1 → realMinimum κ ≤ quarticReal κ y := by
  have h := (real_minimum κ).choose_spec
  refine ⟨h.1,?_⟩
  intro y hy
  exact div_le_div_of_nonneg_right (h.2 y hy) (by norm_num)

/-- An actual deformed minimizing point, with no stationary-coverage assumption. -/
def deformedMinimumPoint (κ : Parameters ℝ) : RealFields SixteenLevelField :=
  (w3_sixteen_level_minimum (actualParameters κ)).choose

def deformedMinimum (κ : Parameters ℝ) : SixteenLevelField :=
  quarticReal (actualParameters κ) (deformedMinimumPoint κ)

lemma deformedMinimumPoint_spec (κ : Parameters ℝ) : mass (deformedMinimumPoint κ) = 1 ∧
    ∀ y : RealFields SixteenLevelField, mass y = 1 →
      deformedMinimum κ ≤ quarticReal (actualParameters κ) y := by
  have h := (w3_sixteen_level_minimum (actualParameters κ)).choose_spec
  refine ⟨h.1,?_⟩
  intro y hy
  exact div_le_div_of_nonneg_right (h.2 y hy) (by norm_num)

/-- Pointwise equation (39), with actual physical monomial bounds. -/
theorem actual_pointwise_bound (κ : Parameters ℝ) (x : RealFields SixteenLevelField)
    (hx : mass x = 1) :
    |quarticReal (actualParameters κ) x -
      quarticReal (fun i => realEmbedding16 (κ i)) x - chronologicalEpsilon 0| ≤
      (9/2)*chronologicalEpsilon 1 := by
  rw [actualParameters, quarticReal_deformed, hx]
  have he : quarticReal (fun i => realEmbedding16 (κ i)) x +
      chronologicalEpsilon 0 * (1:SixteenLevelField)^2 +
      ∑ i, coefficientEpsilon i * monomials x i -
      quarticReal (fun i => realEmbedding16 (κ i)) x - chronologicalEpsilon 0 =
      ∑ i, coefficientEpsilon i * monomials x i := by ring
  rw [he]
  exact actual_fifteen_coordinate_bound (monomials x) (monomials_bound x hx)

/-- Equation (40) for actual attained minima in the actual ordered field. -/
theorem actual_minimum_bound (κ : Parameters ℝ) :
    |deformedMinimum κ - realEmbedding16 (realMinimum κ) - chronologicalEpsilon 0| ≤
      (9/2)*chronologicalEpsilon 1 := by
  let x0 : RealFields SixteenLevelField := fun i => realEmbedding16 (realMinimumPoint κ i)
  have hx0 : mass x0 = 1 := by
    change mass (fun i => realEmbedding16 (realMinimumPoint κ i)) = 1
    exact (mass_map realEmbedding16.toRingHom (realMinimumPoint κ)).trans
      (by rw [(realMinimumPoint_spec κ).1, map_one])
  have hx1 := (deformedMinimumPoint_spec κ).1
  have h0 : quarticReal (fun i => realEmbedding16 (κ i)) x0 =
      realEmbedding16 (realMinimum κ) := quarticReal_map realEmbedding16.toRingHom κ _
  have hf := w3_real_lower_bound_tower κ (realMinimum κ) (realMinimumPoint_spec κ).2
  have h := minimum_perturbation_bound (D := {x : RealFields SixteenLevelField | mass x = 1})
    (f := quarticReal (fun i => realEmbedding16 (κ i)))
    (g := quarticReal (actualParameters κ)) hx0 hx1
    (fun x hx => by rw [h0]; exact hf x hx)
    (deformedMinimumPoint_spec κ).2 (actual_pointwise_bound κ)
  rwa [h0] at h

/-- Every sign and the real standard part now follows unconditionally for the
original arbitrary fifteen real coefficients, including all zero/degenerate data. -/
theorem actual_minimum_signs_and_residue (κ : Parameters ℝ) :
    (0 ≤ realMinimum κ ↔ 0 < deformedMinimum κ) ∧
    (0 < realMinimum κ ↔ 2*chronologicalEpsilon 0 < deformedMinimum κ) ∧
    (realMinimum κ < 0 ↔ deformedMinimum κ < 0) ∧
    (realMinimum κ = 0 ↔ 0 < deformedMinimum κ ∧ deformedMinimum κ < 2*chronologicalEpsilon 0) ∧
    ArchimedeanClass.stdPart (deformedMinimum κ) = realMinimum κ :=
  actual_signs_and_residue (actual_minimum_bound κ)

#print axioms actual_minimum_bound
#print axioms actual_minimum_signs_and_residue
end W3.Infinitesimal
