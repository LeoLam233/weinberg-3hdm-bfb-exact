import W3.FiniteInputResidueNormalization

/-! # Finite coded clearing of an entire annihilator
The common denominator is the structural product of the explicitly decoded
coefficient denominators. It does not use RatFunc.num/denom or an arbitrary
representation of an unknown coefficient. -/
noncomputable section
namespace W3.FiniteInput
open Polynomial W3.Infinitesimal
set_option backward.isDefEq.respectTransparency false

def polynomialStep (n : Nat) : (RationalTower n)[X] →+* RationalTower (n+1) :=
  algebraMap (RationalTower n)[X] (RatFunc (RationalTower n))

variable {n : Nat} [DecidableEq (RationalTower n)]

def denominatorCodes (u : Fin 15 → ℝ) : List (CoefficientCode (n+1)) → List (CoefficientCode n)
  | [] => [.rational 1]
  | a :: as => PolynomialCode.mul (a.fraction u).denominator (denominatorCodes u as)

def clearedCodes (u : Fin 15 → ℝ) : List (CoefficientCode (n+1)) → BivariateCode n
  | [] => []
  | a :: as => BivariateCode.add
      [PolynomialCode.mul (a.fraction u).numerator (denominatorCodes u as)]
      ([] :: BivariateCode.scale (a.fraction u).denominator (clearedCodes u as))

theorem denominatorCodes_ne_zero (u : Fin 15 → ℝ) (cs : List (CoefficientCode (n+1))) :
    stagePolynomial u (denominatorCodes u cs) ≠ 0 := by
  induction cs with
  | nil => simp [denominatorCodes, stagePolynomial, CoefficientCode.eval]
  | cons a as ih =>
    simpa only [denominatorCodes, stagePolynomial, PolynomialCode.eval_mul] using
      mul_ne_zero (a.fraction_spec u).1 ih

/-- The exact finite cleared coefficient list represents the original polynomial
multiplied by its nonzero, explicitly synthesized denominator product. -/
theorem clearedCodes_map (u : Fin 15 → ℝ) (cs : List (CoefficientCode (n+1))) :
    (bivariatePolynomial u (clearedCodes u cs)).map
      (polynomialStep n) =
    C (polynomialStep n
      (stagePolynomial u (denominatorCodes u cs))) * stagePolynomial u cs := by
  induction cs with
  | nil => simp [clearedCodes, stagePolynomial]
  | cons a as ih =>
    have hden : polynomialStep n (stagePolynomial u (a.fraction u).denominator) ≠ 0 :=
      RatFunc.algebraMap_ne_zero (a.fraction_spec u).1
    have hv := (a.fraction_spec u).2
    unfold FractionCode.value at hv
    change polynomialStep n (stagePolynomial u (a.fraction u).numerator) /
      polynomialStep n (stagePolynomial u (a.fraction u).denominator) = _ at hv
    have hnum := (div_eq_iff hden).mp hv
    simp only [clearedCodes, BivariateCode.eval_add, BivariateCode.eval_cons,
      BivariateCode.eval_nil, BivariateCode.eval_scale,
      stagePolynomial, PolynomialCode.eval_nil, PolynomialCode.eval_mul,
      PolynomialCode.eval_cons, denominatorCodes, mul_zero, add_zero, map_zero,
      zero_add, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, map_mul] at *
    rw [ih, hnum]
    simp only [map_mul]
    ring

theorem clearedCodes_ne_zero (u : Fin 15 → ℝ) (cs : List (CoefficientCode (n+1)))
    (hcs : stagePolynomial u cs ≠ 0) : bivariatePolynomial u (clearedCodes u cs) ≠ 0 := by
  intro hz
  have h := clearedCodes_map u cs
  rw [hz, Polynomial.map_zero] at h
  exact (mul_ne_zero (Polynomial.C_ne_zero.mpr
    (RatFunc.algebraMap_ne_zero (denominatorCodes_ne_zero u cs))) hcs) h.symm

def normalizedResidueCoefficients (u : Fin 15 → ℝ) (cs : List (CoefficientCode (n+1))) :
    List (CoefficientCode n) := BivariateCode.normalize u (BivariateCode.swap (clearedCodes u cs))

@[simp] theorem normalizedResidueCoefficients_eval (u : Fin 15 → ℝ)
    (cs : List (CoefficientCode (n+1))) :
    stagePolynomial u (normalizedResidueCoefficients u cs) =
      (normalizeInitial (Polynomial.Bivariate.swap (bivariatePolynomial u (clearedCodes u cs)))).2.coeff 0 := by
  rw [normalizedResidueCoefficients, BivariateCode.eval_normalize, BivariateCode.eval_swap]

theorem swappedClearedCodes_ne_zero (u : Fin 15 → ℝ) (cs : List (CoefficientCode (n+1)))
    (hcs : stagePolynomial u cs ≠ 0) :
    Polynomial.Bivariate.swap (bivariatePolynomial u (clearedCodes u cs)) ≠ 0 := by
  intro hz
  exact clearedCodes_ne_zero u cs hcs ((Polynomial.Bivariate.swap (R := RationalTower n)).injective
    (hz.trans (map_zero _).symm))

theorem normalizedResidueCoefficients_ne_zero (u : Fin 15 → ℝ)
    (cs : List (CoefficientCode (n+1))) (hcs : stagePolynomial u cs ≠ 0) :
    stagePolynomial u (normalizedResidueCoefficients u cs) ≠ 0 := by
  rw [normalizedResidueCoefficients_eval]
  exact (normalizeInitial_correct _ (swappedClearedCodes_ne_zero u cs hcs)).1

/-- The coded variable-swap polynomial is an actual equation of the source value. -/
theorem swappedClearedCodes_root (u : Fin 15 → ℝ) (cs : List (CoefficientCode (n+1)))
    {x : Tower realModel (n+1)}
    (hx : (stagePolynomial u cs).eval₂ (rationalTowerHom (n+1)) x = 0) :
    bivariateEval (Tower realModel n)
      (mapBivariate (rationalTowerHom n)
        (Polynomial.Bivariate.swap (bivariatePolynomial u (clearedCodes u cs)))) x = 0 := by
  change Extension (Tower realModel n) at x
  rw [bivariateEval_map_swap]
  have h := congrArg (Polynomial.eval₂RingHom (rationalTowerHom (n+1)) x) (clearedCodes_map u cs)
  simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_map,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, hx, mul_zero] at h
  change (bivariatePolynomial u (clearedCodes u cs)).eval₂
    ((epsilonRatFuncHomAlong (rationalTowerHom n)).comp
      (algebraMap (RationalTower n)[X] (RatFunc (RationalTower n)))) x = 0 at h
  rw [show (epsilonRatFuncHomAlong (rationalTowerHom n)).comp
      (algebraMap (RationalTower n)[X] (RatFunc (RationalTower n))) =
      epsilonPolynomialHomAlong (rationalTowerHom n) from
      RatFunc.liftRingHom_comp_algebraMap _ _] at h
  exact h

#print axioms normalizedResidueCoefficients_eval
#print axioms swappedClearedCodes_root
end W3.FiniteInput
