import W3.InfinitesimalRootPresentation
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Maps

/-! Combining two explicit finite root presentations by their product basis.
The selected branch evaluation multiplies the two given evaluations, so no
minimal polynomial or field-basis oracle is introduced. -/
noncomputable section
namespace W3.Infinitesimal
open scoped TensorProduct
universe u v
variable {F : Type u} {L : Type v} [Field F] [Field L] [Algebra F L]
namespace FiniteRootPresentation

def tensor (P Q : FiniteRootPresentation F L) : FiniteRootPresentation F L where
  Carrier := P.Carrier ⊗[F] Q.Carrier
  instCommRing := inferInstance
  instAlgebra := inferInstance
  Index := P.Index × Q.Index
  instFintype := inferInstance
  instDecidableEq := inferInstance
  basis := P.basis.tensorProduct Q.basis
  evaluate := Algebra.TensorProduct.lift P.evaluate Q.evaluate (fun a b => Commute.all _ _)

def tensorLeft (P Q : FiniteRootPresentation F L) : P.Carrier →ₐ[F] (P.tensor Q).Carrier :=
  Algebra.TensorProduct.includeLeft

def tensorRight (P Q : FiniteRootPresentation F L) : Q.Carrier →ₐ[F] (P.tensor Q).Carrier :=
  Algebra.TensorProduct.includeRight

@[simp] theorem tensor_evaluate_left (P Q : FiniteRootPresentation F L) (a : P.Carrier) :
    (P.tensor Q).evaluate (P.tensorLeft Q a) = P.evaluate a := by
  change P.evaluate a * Q.evaluate 1 = P.evaluate a
  rw [map_one,mul_one]

@[simp] theorem tensor_evaluate_right (P Q : FiniteRootPresentation F L) (a : Q.Carrier) :
    (P.tensor Q).evaluate (P.tensorRight Q a) = Q.evaluate a := by
  change P.evaluate 1 * Q.evaluate a = Q.evaluate a
  rw [map_one,one_mul]

end FiniteRootPresentation
#print axioms FiniteRootPresentation.tensor
end W3.Infinitesimal
