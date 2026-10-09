import W3.InfinitesimalTranscendence
import W3.InfinitesimalTower
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Joint independence of the actual finite tower
Polynomial evaluation is proved injective by induction through the entire tower.
In particular this does not confuse pairwise transcendence with joint independence.
-/
noncomputable section
namespace W3.Infinitesimal

/-- Evaluate n variables, newest first, at the actual tower infinitesimals. -/
def towerPolynomialEval (M : OrderedFieldModel) : (n : ℕ) →
    MvPolynomial (Fin n) M.Carrier →+* Tower M n
  | 0 => (MvPolynomial.isEmptyRingEquiv M.Carrier (Fin 0)).toRingHom
  | n + 1 => (Polynomial.aeval (epsilon (Tower M n))).toRingHom.comp
      ((Polynomial.mapRingHom (towerPolynomialEval M n)).comp
        (MvPolynomial.finSuccEquiv M.Carrier n).toRingHom)

theorem towerPolynomialEval_injective (M : OrderedFieldModel) (n : ℕ) :
    Function.Injective (towerPolynomialEval M n) := by
  induction n with
  | zero => exact (MvPolynomial.isEmptyRingEquiv M.Carrier (Fin 0)).injective
  | succ n ih =>
    exact (transcendental_iff_injective.mp (epsilon_transcendental (Tower M n))).comp
      ((Polynomial.map_injective (towerPolynomialEval M n) ih).comp
        (MvPolynomial.finSuccEquiv M.Carrier n).injective)

@[simp] theorem towerPolynomialEval_C (M : OrderedFieldModel) (n : ℕ) (r : M.Carrier) :
    towerPolynomialEval M n (MvPolynomial.C r) = baseEmbed M n r := by
  induction n with
  | zero =>
    exact (MvPolynomial.isEmptyRingEquiv M.Carrier (Fin 0)).apply_symm_apply r
  | succ n ih =>
    change (Polynomial.aeval (epsilon (Tower M n)))
      (((MvPolynomial.finSuccEquiv M.Carrier n) (MvPolynomial.C r)).map
        (towerPolynomialEval M n)) = _
    simp only [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C,
      RingHom.comp_apply, Polynomial.map_C, Polynomial.aeval_C, ih]
    rfl

/-- Coordinates of the actual tower, newest first. -/
def towerCoordinates (M : OrderedFieldModel) (n : ℕ) (i : Fin n) : Tower M n :=
  towerPolynomialEval M n (MvPolynomial.X i)

theorem towerPolynomialEval_eq_eval₂Hom (M : OrderedFieldModel) (n : ℕ) :
    towerPolynomialEval M n =
      MvPolynomial.eval₂Hom (baseEmbed M n).toRingHom (towerCoordinates M n) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [towerPolynomialEval_C, MvPolynomial.eval₂Hom_C]
    rfl
  · intro i
    rw [MvPolynomial.eval₂Hom_X']
    rfl

/-- The selected epsilon at the newest index is exactly the freshly constructed epsilon. -/
@[simp] theorem towerCoordinates_zero (M : OrderedFieldModel) (n : ℕ) :
    towerCoordinates M (n + 1) 0 = stepEpsilon M n := by
  change (Polynomial.aeval (epsilon (Tower M n)))
    (((MvPolynomial.finSuccEquiv M.Carrier n) (MvPolynomial.X 0)).map
      (towerPolynomialEval M n)) = _
  rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X, Polynomial.aeval_X]
  rfl

/-- All old coordinates are embedded coherently into the next level. -/
@[simp] theorem towerCoordinates_succ (M : OrderedFieldModel) (n : ℕ) (i : Fin n) :
    towerCoordinates M (n + 1) i.succ = stepEmbed M n (towerCoordinates M n i) := by
  change (Polynomial.aeval (epsilon (Tower M n)))
    (((MvPolynomial.finSuccEquiv M.Carrier n) (MvPolynomial.X i.succ)).map
      (towerPolynomialEval M n)) = _
  rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C, Polynomial.aeval_C]
  rfl

#print axioms towerPolynomialEval_injective
end W3.Infinitesimal
