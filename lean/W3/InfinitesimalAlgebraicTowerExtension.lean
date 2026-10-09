import W3.InfinitesimalAlgebraicInvariance

/-! # Algebraicity over each preceding algebraic field with the new epsilon
This supplies the missing field-semantic distinction: the restricted next stage
is algebraic over H(epsilon), whereas the whole ultrapower is not.
-/
noncomputable section
namespace W3.Infinitesimal
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped nonZeroDivisors
attribute [local instance] rationalTowerAlgebra

variable {F G K : Type*} [Field F] [Field G] [Field K]

private lemma ratFuncCoefficientMap_denoms (f : F →+* G) :
    F[X]⁰ ≤ (RatFunc G)⁰.comap
      ((algebraMap G[X] (RatFunc G)).comp (Polynomial.mapRingHom f)) := by
  intro p hp
  rw [mem_nonZeroDivisors_iff_ne_zero] at hp
  change algebraMap G[X] (RatFunc G) (p.map f) ∈ (RatFunc G)⁰
  rw [mem_nonZeroDivisors_iff_ne_zero]
  exact RatFunc.algebraMap_ne_zero ((Polynomial.map_ne_zero_iff f.injective).mpr hp)

def ratFuncCoefficientMap (f : F →+* G) : RatFunc F →+* RatFunc G :=
  RatFunc.liftRingHom ((algebraMap G[X] (RatFunc G)).comp (Polynomial.mapRingHom f))
    (ratFuncCoefficientMap_denoms f)

@[simp] lemma ratFuncCoefficientMap_polynomial (f : F →+* G) (p : F[X]) :
    ratFuncCoefficientMap f (algebraMap F[X] (RatFunc F) p) =
      algebraMap G[X] (RatFunc G) (p.map f) := RatFunc.liftRingHom_algebraMap _ _ _

variable [LinearOrder K] [IsStrictOrderedRing K]

lemma epsilonPolynomialHomAlong_map (f : F →+* G) (g : G →+* K) (p : F[X]) :
    epsilonPolynomialHomAlong g (p.map f) = epsilonPolynomialHomAlong (g.comp f) p := by
  change epsilonPolynomialHom K ((p.map f).map g) = epsilonPolynomialHom K (p.map (g.comp f))
  rw [Polynomial.map_map]

lemma epsilonRatFuncHomAlong_natural (f : F →+* G) (g : G →+* K) :
    (epsilonRatFuncHomAlong g).comp (ratFuncCoefficientMap f) =
      epsilonRatFuncHomAlong (g.comp f) := by
  ext r
  rw [← RatFunc.num_div_denom r]
  simp only [RingHom.comp_apply, map_div₀, ratFuncCoefficientMap_polynomial,
    epsilonRatFuncHomAlong_polynomial, epsilonPolynomialHomAlong_map]

/-- Rational functions over the actual preceding real-closed algebraic field,
with their variable evaluated at the next infinitesimal. -/
def algebraicTowerRatFuncHom (n : ℕ) : RatFunc (AlgebraicTower n) →+* Tower realModel (n + 1) :=
  epsilonRatFuncHomAlong (algebraMap (AlgebraicTower n) (Tower realModel n))

/-- Every element of the restricted next field is algebraic over the preceding
restricted field with its fresh epsilon. Thus this is an iterated algebraic
real-closed extension, not a relabeling of the larger ultrapower. -/
theorem algebraicTower_step_isAlgebraic (n : ℕ) (x : AlgebraicTower (n + 1)) :
    letI := (algebraicTowerRatFuncHom n).toAlgebra
    IsAlgebraic (RatFunc (AlgebraicTower n)) (x : Tower realModel (n + 1)) := by
  letI := (algebraicTowerRatFuncHom n).toAlgebra
  let f : RationalTower n →+* AlgebraicTower n := algebraMap _ _
  let g : AlgebraicTower n →+* Tower realModel n := algebraMap _ _
  have hcomp : g.comp f = rationalTowerHom n := by ext r; rfl
  have heval : (algebraicTowerRatFuncHom n).comp (ratFuncCoefficientMap f) =
      rationalTowerHom (n + 1) := by
    change (epsilonRatFuncHomAlong g).comp (ratFuncCoefficientMap f) = _
    rw [epsilonRatFuncHomAlong_natural, hcomp]
    rfl
  obtain ⟨p, hp, hroot⟩ := mem_algebraicClosure_iff.mp x.property
  refine ⟨p.map (ratFuncCoefficientMap f),
    (Polynomial.map_ne_zero_iff (ratFuncCoefficientMap f).injective).mpr hp, ?_⟩
  change (p.map (ratFuncCoefficientMap f)).eval₂ (algebraicTowerRatFuncHom n)
    (x : Tower realModel (n + 1)) = 0
  rw [Polynomial.eval₂_map, heval]
  exact hroot

/-- Polynomial evaluation commutes with the restricted stage inclusions. -/
lemma algebraicTower_polynomial_eval (n : ℕ) (p : (AlgebraicTower n)[X]) :
    ((p.eval₂ (algebraicTowerStep n).toRingHom (algebraicTowerEpsilon n) :
      AlgebraicTower (n + 1)) : Tower realModel (n + 1)) =
      epsilonPolynomialHomAlong
        (algebraMap (AlgebraicTower n) (Tower realModel n)) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.eval₂_add, map_add, ← hp, ← hq]
    rfl
  | monomial m a =>
    rw [Polynomial.eval₂_monomial]
    change (stepEmbed realModel n (a : Tower realModel n)) * (stepEpsilon realModel n) ^ m =
      epsilonPolynomialHom (Tower realModel n)
        ((Polynomial.monomial m a).map (algebraMap (AlgebraicTower n) (Tower realModel n)))
    rw [Polynomial.map_monomial]
    exact (Polynomial.eval₂_monomial _ _).symm

/-- The whole rational function field H_n(epsilon_n) embeds into H_(n+1). -/
theorem algebraicTowerRatFuncHom_mem (n : ℕ) (r : RatFunc (AlgebraicTower n)) :
    algebraicTowerRatFuncHom n r ∈ AlgebraicTower (n + 1) := by
  let a : AlgebraicTower (n + 1) := r.num.eval₂ (algebraicTowerStep n).toRingHom
    (algebraicTowerEpsilon n)
  let b : AlgebraicTower (n + 1) := r.denom.eval₂ (algebraicTowerStep n).toRingHom
    (algebraicTowerEpsilon n)
  have ha := algebraicTower_polynomial_eval n r.num
  have hb := algebraicTower_polynomial_eval n r.denom
  have heq : algebraicTowerRatFuncHom n r = ((a / b : AlgebraicTower (n + 1)) :
      Tower realModel (n + 1)) := by
    rw [← RatFunc.num_div_denom r, map_div₀]
    change epsilonRatFuncHomAlong _ (algebraMap _ _ r.num) /
      epsilonRatFuncHomAlong _ (algebraMap _ _ r.denom) = _
    rw [epsilonRatFuncHomAlong_polynomial, epsilonRatFuncHomAlong_polynomial,
      ← ha, ← hb]
    rfl
  rw [heq]
  exact (a / b).property

/-- Actual coefficient-field embedding into the restricted algebraic stage. -/
def algebraicTowerRatFuncEmbedding (n : ℕ) :
    RatFunc (AlgebraicTower n) →+* AlgebraicTower (n + 1) where
  toFun r := ⟨algebraicTowerRatFuncHom n r, algebraicTowerRatFuncHom_mem n r⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- Each restricted successor really is an algebraic real-closed extension of
its preceding field with the new positive infinitesimal adjoined. -/
theorem algebraicTower_algebraic_extension (n : ℕ) :
    letI := (algebraicTowerRatFuncEmbedding n).toAlgebra
    Algebra.IsAlgebraic (RatFunc (AlgebraicTower n)) (AlgebraicTower (n + 1)) := by
  letI := (algebraicTowerRatFuncEmbedding n).toAlgebra
  constructor
  intro x
  obtain ⟨p, hp, hroot⟩ := algebraicTower_step_isAlgebraic n x
  refine ⟨p, hp, ?_⟩
  change p.eval₂ (algebraicTowerRatFuncEmbedding n) x = 0
  apply (algebraMap (AlgebraicTower (n + 1)) (Tower realModel (n + 1))).injective
  rw [map_zero]
  have h := Polynomial.hom_eval₂ p (algebraicTowerRatFuncEmbedding n)
    (algebraMap (AlgebraicTower (n + 1)) (Tower realModel (n + 1))) x
  rw [h]
  exact hroot

#print axioms algebraicTower_algebraic_extension
#print axioms algebraicTower_step_isAlgebraic
end W3.Infinitesimal
