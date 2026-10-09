import W3.InfinitesimalRationalPresentation
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # Finite multiplication-matrix annihilators
The arithmetic interface is an explicitly finite extension basis. From its
multiplication table, a determinant gives a monic annihilator. Existence of a
presentation is separate from an effective representation/basis-construction oracle.
-/
noncomputable section
namespace W3.Infinitesimal
open Polynomial IntermediateField

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- An exact finite field presentation containing the selected element. The basis
coordinates supply all finite multiplication-table entries used by the algorithm. -/
structure FiniteFieldPresentation (x : L) where
  field : IntermediateField F L
  dimension : ℕ
  basis : Module.Basis (Fin dimension) F field
  contains : x ∈ field

/-- Every selected algebraic element has a finite presentation. This existence
proof does not claim that Classical choice implements an effective basis oracle. -/
theorem finiteFieldPresentation_exists {x : L} (hx : IsAlgebraic F x) :
    Nonempty (FiniteFieldPresentation (F := F) x) := by
  let S : IntermediateField F L := IntermediateField.adjoin F {x}
  letI : FiniteDimensional F S := IntermediateField.adjoin.finiteDimensional hx.isIntegral
  exact ⟨⟨S, Module.finrank F S, Module.finBasis F S,
    IntermediateField.subset_adjoin F {x} (by simp)⟩⟩

namespace FiniteFieldPresentation

variable {x : L} (P : FiniteFieldPresentation (F := F) x)

/-- The concrete finite multiplication matrix of x in the supplied basis. -/
def multiplicationMatrix : Matrix (Fin P.dimension) (Fin P.dimension) F :=
  Algebra.leftMulMatrix P.basis (⟨x, P.contains⟩ : P.field)

/-- This is det(XI-M), a finite polynomial expression in the multiplication table. -/
def annihilator : F[X] := P.multiplicationMatrix.charpoly

theorem annihilator_monic : P.annihilator.Monic := Matrix.charpoly_monic _

theorem annihilator_ne_zero : P.annihilator ≠ 0 := P.annihilator_monic.ne_zero

theorem annihilator_degree : P.annihilator.natDegree = P.dimension := by
  simpa only [annihilator, Fintype.card_fin] using
    Matrix.charpoly_natDegree_eq_dim P.multiplicationMatrix

theorem annihilator_aeval : Polynomial.aeval x P.annihilator = 0 := by
  letI : Module.Finite F P.field := Module.Finite.of_basis P.basis
  have h : Polynomial.aeval (⟨x, P.contains⟩ : P.field) P.annihilator = 0 := by
    change Polynomial.aeval (⟨x, P.contains⟩ : P.field)
      (LinearMap.toMatrix P.basis P.basis
        (Algebra.lmul F P.field (⟨x, P.contains⟩ : P.field))).charpoly = 0
    rw [LinearMap.charpoly_toMatrix]
    exact Algebra.aeval_self_charpoly_lmul _
  have hmap := congrArg P.field.val h
  simp only [← Polynomial.aeval_algHom_apply, map_zero] at hmap
  exact hmap

end FiniteFieldPresentation

#print axioms FiniteFieldPresentation.annihilator_aeval
#print axioms finiteFieldPresentation_exists
end W3.Infinitesimal
