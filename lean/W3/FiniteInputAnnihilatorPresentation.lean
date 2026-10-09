import W3.FiniteInputAnnihilatorRing
import W3.InfinitesimalTensorPresentation

/-! Explicit power-product presentations over the free coefficient ring.
All bases come from singleton, tensor, and monic quotient power bases. -/
noncomputable section
namespace W3.FiniteInput
open Polynomial
open scoped TensorProduct
universe u v

structure RingPresentation (R : Type u) (K : Type v) [CommRing R] [CommRing K]
    [Algebra R K] where
  Carrier : Type u
  instCommRing : CommRing Carrier
  instAlgebra : Algebra R Carrier
  Index : Type u
  instFintype : Fintype Index
  instDecidableEq : DecidableEq Index
  basis : Module.Basis Index R Carrier
  evaluate : Carrier →ₐ[R] K
attribute [instance] RingPresentation.instCommRing RingPresentation.instAlgebra
  RingPresentation.instFintype RingPresentation.instDecidableEq

variable {R : Type u} {K : Type v} [CommRing R] [CommRing K] [Algebra R K]
namespace RingPresentation

def base : RingPresentation R K where
  Carrier := R
  instCommRing := inferInstance
  instAlgebra := inferInstance
  Index := PUnit
  instFintype := inferInstance
  instDecidableEq := inferInstance
  basis := Module.Basis.singleton PUnit R
  evaluate := Algebra.ofId R K

def adjoin (P : RingPresentation R K) (p : P.Carrier[X]) (hp : p.Monic)
    (x : K) (hx : p.eval₂ P.evaluate.toRingHom x = 0) : RingPresentation R K where
  Carrier := AdjoinRoot p
  instCommRing := inferInstance
  instAlgebra := inferInstance
  Index := P.Index × Fin p.natDegree
  instFintype := inferInstance
  instDecidableEq := inferInstance
  basis := P.basis.smulTower (AdjoinRoot.powerBasis' hp).basis
  evaluate := AdjoinRoot.liftAlgHom p P.evaluate x hx

@[simp] theorem adjoin_evaluate_root (P : RingPresentation R K)
    (p : P.Carrier[X]) (hp : p.Monic) (x : K) (hx : p.eval₂ P.evaluate.toRingHom x = 0) :
    (P.adjoin p hp x hx).evaluate (AdjoinRoot.root p) = x :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

def tensor (P Q : RingPresentation R K) : RingPresentation R K where
  Carrier := P.Carrier ⊗[R] Q.Carrier
  instCommRing := inferInstance
  instAlgebra := inferInstance
  Index := P.Index × Q.Index
  instFintype := inferInstance
  instDecidableEq := inferInstance
  basis := P.basis.tensorProduct Q.basis
  evaluate := Algebra.TensorProduct.lift P.evaluate Q.evaluate (fun a b => Commute.all _ _)

def tensorLeft (P Q : RingPresentation R K) : P.Carrier →ₐ[R] (P.tensor Q).Carrier :=
  Algebra.TensorProduct.includeLeft

def tensorRight (P Q : RingPresentation R K) : Q.Carrier →ₐ[R] (P.tensor Q).Carrier :=
  Algebra.TensorProduct.includeRight

@[simp] theorem tensor_evaluate_left (P Q : RingPresentation R K) (a : P.Carrier) :
    (P.tensor Q).evaluate (P.tensorLeft Q a) = P.evaluate a := by
  change P.evaluate a * Q.evaluate 1 = P.evaluate a
  rw [map_one, mul_one]

@[simp] theorem tensor_evaluate_right (P Q : RingPresentation R K) (a : Q.Carrier) :
    (P.tensor Q).evaluate (P.tensorRight Q a) = Q.evaluate a := by
  change P.evaluate 1 * Q.evaluate a = Q.evaluate a
  rw [map_one, one_mul]

def annihilator (P : RingPresentation R K) (a : P.Carrier) : R[X] :=
  (Algebra.leftMulMatrix P.basis a).charpoly

theorem annihilator_monic (P : RingPresentation R K) (a : P.Carrier) :
    (P.annihilator a).Monic := Matrix.charpoly_monic _

theorem annihilator_eval (P : RingPresentation R K) (a : P.Carrier) :
    Polynomial.aeval (P.evaluate a) (P.annihilator a) = 0 := by
  letI : Module.Finite R P.Carrier := Module.Finite.of_basis P.basis
  letI : Module.Free R P.Carrier := Module.Free.of_basis P.basis
  have h : Polynomial.aeval a (P.annihilator a) = 0 := by
    change Polynomial.aeval a
      (LinearMap.toMatrix P.basis P.basis (Algebra.lmul R P.Carrier a)).charpoly = 0
    rw [LinearMap.charpoly_toMatrix]
    exact Algebra.aeval_self_charpoly_lmul _
  have hmap := congrArg P.evaluate h
  simpa only [← Polynomial.aeval_algHom_apply, map_zero] using hmap
end RingPresentation

structure RingExpressionPresentation (x : K) where
  presentation : RingPresentation R K
  value : presentation.Carrier
  evaluate_value : presentation.evaluate value = x
namespace RingExpressionPresentation

def constant (a : R) : RingExpressionPresentation (R := R) (algebraMap R K a) where
  presentation := RingPresentation.base
  value := a
  evaluate_value := rfl

def add {x y : K} (A : RingExpressionPresentation (R := R) x)
    (B : RingExpressionPresentation (R := R) y) : RingExpressionPresentation (R := R) (x+y) where
  presentation := A.presentation.tensor B.presentation
  value := A.presentation.tensorLeft B.presentation A.value + A.presentation.tensorRight B.presentation B.value
  evaluate_value := by
    rw [map_add, RingPresentation.tensor_evaluate_left, RingPresentation.tensor_evaluate_right,
      A.evaluate_value, B.evaluate_value]

def mul {x y : K} (A : RingExpressionPresentation (R := R) x)
    (B : RingExpressionPresentation (R := R) y) : RingExpressionPresentation (R := R) (x*y) where
  presentation := A.presentation.tensor B.presentation
  value := A.presentation.tensorLeft B.presentation A.value * A.presentation.tensorRight B.presentation B.value
  evaluate_value := by
    rw [map_mul, RingPresentation.tensor_evaluate_left, RingPresentation.tensor_evaluate_right,
      A.evaluate_value, B.evaluate_value]

def neg {x : K} (A : RingExpressionPresentation (R := R) x) :
    RingExpressionPresentation (R := R) (-x) where
  presentation := A.presentation
  value := -A.value
  evaluate_value := by rw [map_neg, A.evaluate_value]

def selectedRoot (p : R[X]) (hp : p.Monic) (x : K) (hx : aeval x p = 0) :
    RingExpressionPresentation (R := R) x :=
  ⟨RingPresentation.base.adjoin p hp x hx, AdjoinRoot.root p,
    RingPresentation.adjoin_evaluate_root _ _ _ _ _⟩

def squareRoot {r : K} (A : RingExpressionPresentation (R := R) r) (x : K) (hx : x^2=r) :
    RingExpressionPresentation (R := R) x := by
  let q : A.presentation.Carrier[X] := X^2-C A.value
  have hq : q.Monic := monic_X_pow_sub_C A.value (by decide : (2 : Nat) ≠ 0)
  have hr : q.eval₂ A.presentation.evaluate.toRingHom x = 0 := by
    simp only [q, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    change x^2-A.presentation.evaluate A.value=0
    rw [hx, A.evaluate_value, sub_self]
  exact ⟨A.presentation.adjoin q hq x hr, AdjoinRoot.root q,
    RingPresentation.adjoin_evaluate_root _ _ _ _ _⟩

def annihilator {x : K} (A : RingExpressionPresentation (R := R) x) : R[X] :=
  A.presentation.annihilator A.value

theorem annihilator_monic {x : K} (A : RingExpressionPresentation (R := R) x) :
    A.annihilator.Monic := A.presentation.annihilator_monic A.value

theorem annihilator_aeval {x : K} (A : RingExpressionPresentation (R := R) x) :
    aeval x A.annihilator=0 := by
  simpa only [annihilator, A.evaluate_value] using A.presentation.annihilator_eval A.value
end RingExpressionPresentation
end W3.FiniteInput
