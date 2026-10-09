import W3.InfinitesimalIndependence
import Mathlib.RingTheory.AlgebraicIndependent.Defs

/-! # Translated tower coordinates stay jointly algebraically independent. -/
noncomputable section
namespace W3.Infinitesimal

variable {R σ : Type*} [CommRing R]

/-- Polynomial translation by arbitrary base-field constants. -/
def translateVariables (t : σ → R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (t i))

theorem translateVariables_leftInverse (t : σ → R) :
    Function.LeftInverse (translateVariables (fun i => -t i)) (translateVariables t) := by
  have h : (translateVariables (fun i => -t i)).comp (translateVariables t) =
      AlgHom.id R (MvPolynomial σ R) := by
    ext i
    simp [translateVariables]
  intro p
  exact congrArg (fun f : MvPolynomial σ R →ₐ[R] MvPolynomial σ R => f p) h

theorem translateVariables_injective (t : σ → R) :
    Function.Injective (translateVariables t) :=
  (translateVariables_leftInverse t).injective

/-- Fixed translations of actual independent tower coordinates. -/
def translatedCoordinates (M : OrderedFieldModel) (n : ℕ) (t : Fin n → M.Carrier)
    (i : Fin n) : Tower M n :=
  towerCoordinates M n i + baseEmbed M n (t i)

theorem translated_eval_eq (M : OrderedFieldModel) (n : ℕ) (t : Fin n → M.Carrier) :
    MvPolynomial.eval₂Hom (baseEmbed M n).toRingHom (translatedCoordinates M n t) =
      (towerPolynomialEval M n).comp (translateVariables t).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
    change baseEmbed M n r = towerPolynomialEval M n ((translateVariables t) (MvPolynomial.C r))
    simp [translateVariables]
  · intro i
    rw [MvPolynomial.eval₂Hom_X']
    change translatedCoordinates M n t i =
      towerPolynomialEval M n ((translateVariables t) (MvPolynomial.X i))
    simp only [translateVariables, MvPolynomial.aeval_X, map_add, towerPolynomialEval_C]
    rfl

theorem translated_eval_injective (M : OrderedFieldModel) (n : ℕ) (t : Fin n → M.Carrier) :
    Function.Injective
      (MvPolynomial.eval₂Hom (baseEmbed M n).toRingHom (translatedCoordinates M n t)) := by
  rw [translated_eval_eq]
  exact (towerPolynomialEval_injective M n).comp (translateVariables_injective t)

/-- A nonzero exceptional polynomial cannot vanish at any fixed translates of the tower epsilons. -/
theorem translated_eval_ne_zero (M : OrderedFieldModel) (n : ℕ) (t : Fin n → M.Carrier)
    {p : MvPolynomial (Fin n) M.Carrier} (hp : p ≠ 0) :
    MvPolynomial.eval₂Hom (baseEmbed M n).toRingHom (translatedCoordinates M n t) p ≠ 0 := by
  intro h
  apply hp
  apply translated_eval_injective M n t
  simpa only [map_zero] using h

/-- The algebra structure induced by the already constructed base embedding. -/
def towerAlgebra (M : OrderedFieldModel) (n : ℕ) : Algebra M.Carrier (Tower M n) :=
  (baseEmbed M n).toRingHom.toAlgebra

theorem towerCoordinates_algebraicIndependent (M : OrderedFieldModel) (n : ℕ) :
    letI := towerAlgebra M n
    AlgebraicIndependent M.Carrier (towerCoordinates M n) := by
  letI := towerAlgebra M n
  change Function.Injective
    (MvPolynomial.eval₂Hom (baseEmbed M n).toRingHom (towerCoordinates M n))
  rw [← towerPolynomialEval_eq_eval₂Hom]
  exact towerPolynomialEval_injective M n

theorem translatedCoordinates_algebraicIndependent (M : OrderedFieldModel) (n : ℕ)
    (t : Fin n → M.Carrier) :
    letI := towerAlgebra M n
    AlgebraicIndependent M.Carrier (translatedCoordinates M n t) := by
  letI := towerAlgebra M n
  exact translated_eval_injective M n t

/-- All sixteen actual coordinates are jointly independent over the reals. -/
theorem sixteen_algebraicIndependent :
    letI : Algebra ℝ (Tower realModel 16) := towerAlgebra realModel 16
    AlgebraicIndependent ℝ (towerCoordinates realModel 16) :=
  towerCoordinates_algebraicIndependent realModel 16

/-- The fifteen perturbation coordinates, including arbitrary translations by
original couplings and epsilon_0, are independent over the *whole* first field.
This is stronger than independence over the rational function field ℝ(epsilon_0). -/
theorem fifteen_translated_algebraicIndependent
    (t : Fin 15 → (extendModel realModel).Carrier) :
    letI := towerAlgebra (extendModel realModel) 15
    AlgebraicIndependent (extendModel realModel).Carrier
      (translatedCoordinates (extendModel realModel) 15 t) :=
  translatedCoordinates_algebraicIndependent (extendModel realModel) 15 t

#print axioms sixteen_algebraicIndependent
#print axioms fifteen_translated_algebraicIndependent
end W3.Infinitesimal
