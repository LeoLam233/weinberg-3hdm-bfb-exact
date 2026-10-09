import W3.InfinitesimalCoefficientPresentation
import W3.InfinitesimalHierarchy

/-! # A finite rational presentation of every tower infinitesimal
The smaller rational coefficient fields are embedded into the actual ordered
ultrapower fields. Their embeddings commute with the base and each new variable.
-/
noncomputable section
namespace W3.Infinitesimal
open Polynomial

structure RationalFieldModel where
  Carrier : Type
  instField : Field Carrier
attribute [instance] RationalFieldModel.instField

def rationalTowerModel : ℕ → RationalFieldModel
  | 0 => ⟨ℝ, inferInstance⟩
  | n + 1 => ⟨RatFunc (rationalTowerModel n).Carrier, inferInstance⟩

abbrev RationalTower (n : ℕ) := (rationalTowerModel n).Carrier

def rationalTowerHom : (n : ℕ) → RationalTower n →+* Tower realModel n
  | 0 => RingHom.id ℝ
  | n + 1 => epsilonRatFuncHomAlong (rationalTowerHom n)

@[instance_reducible] def rationalTowerAlgebra (n : ℕ) :
    Algebra (RationalTower n) (Tower realModel n) := (rationalTowerHom n).toAlgebra

def rationalStep (n : ℕ) : RationalTower n →+* RationalTower (n + 1) :=
  (algebraMap (RationalTower n)[X] (RatFunc (RationalTower n))).comp Polynomial.C

def rationalVariable (n : ℕ) : RationalTower (n + 1) :=
  algebraMap (RationalTower n)[X] (RatFunc (RationalTower n)) Polynomial.X

@[simp] lemma rationalTowerHom_step (n : ℕ) (x : RationalTower n) :
    rationalTowerHom (n + 1) (rationalStep n x) =
      stepEmbed realModel n (rationalTowerHom n x) := by
  change epsilonRatFuncHomAlong (rationalTowerHom n)
    (algebraMap (RationalTower n)[X] (RatFunc (RationalTower n)) (Polynomial.C x)) = _
  rw [epsilonRatFuncHomAlong_polynomial]
  change (epsilonPolynomialHom (Tower realModel n))
    ((Polynomial.C x).map (rationalTowerHom n)) = _
  rw [Polynomial.map_C]
  exact Polynomial.eval₂_C _ _

@[simp] lemma rationalTowerHom_variable (n : ℕ) :
    rationalTowerHom (n + 1) (rationalVariable n) = stepEpsilon realModel n := by
  change epsilonRatFuncHomAlong (rationalTowerHom n)
    (algebraMap (RationalTower n)[X] (RatFunc (RationalTower n)) Polynomial.X) = _
  rw [epsilonRatFuncHomAlong_polynomial]
  change (epsilonPolynomialHom (Tower realModel n))
    (Polynomial.X.map (rationalTowerHom n)) = _
  rw [Polynomial.map_X]
  exact Polynomial.eval₂_X _ _

def rationalBase : (n : ℕ) → ℝ →+* RationalTower n
  | 0 => RingHom.id ℝ
  | n + 1 => (rationalStep n).comp (rationalBase n)

@[simp] theorem rationalTowerHom_base (n : ℕ) (r : ℝ) :
    rationalTowerHom n (rationalBase n r) = baseEmbed realModel n r := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change rationalTowerHom (n + 1) (rationalStep n (rationalBase n r)) = _
    rw [rationalTowerHom_step, ih]
    rfl

def rationalCoordinates : (n : ℕ) → Fin n → RationalTower n
  | 0 => Fin.elim0
  | n + 1 => Fin.cases (rationalVariable n) (fun i => rationalStep n (rationalCoordinates n i))

@[simp] theorem rationalTowerHom_coordinates (n : ℕ) (i : Fin n) :
    rationalTowerHom n (rationalCoordinates n i) = towerCoordinates realModel n i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (rationalTowerHom_variable n).trans (towerCoordinates_zero realModel n).symm
    · change rationalTowerHom (n + 1) (rationalStep n (rationalCoordinates n j)) = _
      rw [rationalTowerHom_step, ih, towerCoordinates_succ]

/-- The same chronological order used in the physical deformation. -/
def rationalChronologicalEpsilon (i : Fin 16) : RationalTower 16 := rationalCoordinates 16 i.rev

@[simp] theorem rationalTowerHom_chronologicalEpsilon (i : Fin 16) :
    rationalTowerHom 16 (rationalChronologicalEpsilon i) = chronologicalEpsilon i :=
  rationalTowerHom_coordinates 16 i.rev

/-- Algebraicity descends through a residue step in the finite rational presentation. -/
theorem rationalTower_residue_step (n : ℕ) {x : Tower realModel (n + 1)}
    (hbound : BaseBounded (Tower realModel n) x)
    (halg : letI := rationalTowerAlgebra (n + 1); IsAlgebraic (RationalTower (n + 1)) x) :
    ∃ q : Tower realModel n, HasRelativeResidue (Tower realModel n) x q ∧
      (letI := rationalTowerAlgebra n; IsAlgebraic (RationalTower n) q) :=
  tower_coefficient_algebraic_relativeResidue n (rationalTowerHom n) hbound halg

#print axioms rationalTower_residue_step
#print axioms rationalTowerHom_chronologicalEpsilon
end W3.Infinitesimal
