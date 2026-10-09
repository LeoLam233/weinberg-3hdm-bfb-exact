import W3.InfinitesimalFinitePresentation
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.AlgebraTower

/-! # Explicit finite power-basis presentations of selected algebraic root towers
The quotient algebra need not be a field or reduced. A selected-root evaluation
homomorphism retains the chosen real branch, while the finite power basis is
constructed directly from the monic equation, without factoring a minimal polynomial.
-/
noncomputable section
namespace W3.Infinitesimal
open Polynomial
universe u v

structure FiniteRootPresentation (F : Type u) (L : Type v) [Field F] [Field L] [Algebra F L] where
  Carrier : Type u
  instCommRing : CommRing Carrier
  instAlgebra : Algebra F Carrier
  Index : Type u
  instFintype : Fintype Index
  instDecidableEq : DecidableEq Index
  basis : Module.Basis Index F Carrier
  evaluate : Carrier →ₐ[F] L

attribute [instance] FiniteRootPresentation.instCommRing FiniteRootPresentation.instAlgebra
  FiniteRootPresentation.instFintype FiniteRootPresentation.instDecidableEq

variable {F : Type u} {L : Type v} [Field F] [Field L] [Algebra F L]

namespace FiniteRootPresentation

def base : FiniteRootPresentation F L where
  Carrier := F
  instCommRing := inferInstance
  instAlgebra := inferInstance
  Index := PUnit
  instFintype := inferInstance
  instDecidableEq := inferInstance
  basis := Module.Basis.singleton PUnit F
  evaluate := Algebra.ofId F L

/-- Adjoin one selected root of a monic equation using the explicit quotient
power basis, tensor-composed with the preceding presentation basis. -/
def adjoin (P : FiniteRootPresentation F L) (p : P.Carrier[X]) (hp : p.Monic)
    (x : L) (hx : p.eval₂ P.evaluate.toRingHom x = 0) : FiniteRootPresentation F L where
  Carrier := AdjoinRoot p
  instCommRing := inferInstance
  instAlgebra := inferInstance
  Index := P.Index × Fin p.natDegree
  instFintype := inferInstance
  instDecidableEq := inferInstance
  basis := P.basis.smulTower (AdjoinRoot.powerBasis' hp).basis
  evaluate := AdjoinRoot.liftAlgHom p P.evaluate x hx

@[simp] theorem adjoin_evaluate_root (P : FiniteRootPresentation F L)
    (p : P.Carrier[X]) (hp : p.Monic) (x : L) (hx : p.eval₂ P.evaluate.toRingHom x = 0) :
    (P.adjoin p hp x hx).evaluate (AdjoinRoot.root p) = x :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

@[simp] theorem adjoin_evaluate_old (P : FiniteRootPresentation F L)
    (p : P.Carrier[X]) (hp : p.Monic) (x : L) (hx : p.eval₂ P.evaluate.toRingHom x = 0)
    (a : P.Carrier) :
    (P.adjoin p hp x hx).evaluate (AdjoinRoot.of p a) = P.evaluate a :=
  AdjoinRoot.liftAlgHom_of _ _ _ _ _

/-- A concrete multiplication matrix in the power-product basis. -/
def annihilator (P : FiniteRootPresentation F L) (a : P.Carrier) : F[X] :=
  (Algebra.leftMulMatrix P.basis a).charpoly

theorem annihilator_monic (P : FiniteRootPresentation F L) (a : P.Carrier) :
    (P.annihilator a).Monic := Matrix.charpoly_monic _

theorem annihilator_degree (P : FiniteRootPresentation F L) (a : P.Carrier) :
    (P.annihilator a).natDegree = Fintype.card P.Index := Matrix.charpoly_natDegree_eq_dim _

theorem annihilator_eval (P : FiniteRootPresentation F L) (a : P.Carrier) :
    Polynomial.aeval (P.evaluate a) (P.annihilator a) = 0 := by
  letI : Module.Finite F P.Carrier := Module.Finite.of_basis P.basis
  letI : Module.Free F P.Carrier := Module.Free.of_basis P.basis
  have h : Polynomial.aeval a (P.annihilator a) = 0 := by
    change Polynomial.aeval a
      (LinearMap.toMatrix P.basis P.basis (Algebra.lmul F P.Carrier a)).charpoly = 0
    rw [LinearMap.charpoly_toMatrix]
    exact Algebra.aeval_self_charpoly_lmul _
  have hmap := congrArg P.evaluate h
  simpa only [← Polynomial.aeval_algHom_apply, map_zero] using hmap

end FiniteRootPresentation
#print axioms FiniteRootPresentation.adjoin
#print axioms FiniteRootPresentation.annihilator_eval
end W3.Infinitesimal
