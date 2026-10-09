import W3.InfinitesimalPresentedExpression
import W3.InfinitesimalTensorPresentation
import W3.InfinitesimalInversePresentation

/-! A recursive compiler from the certified selected-root/arithmetic syntax
into an explicit finite commutative quotient algebra with a power-product
basis and a branch evaluation homomorphism. No arbitrary finite-dimensional
basis is chosen from an `IsAlgebraic` proof. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace W3.Infinitesimal
open Polynomial
universe u v
variable {F : Type u} {L : Type v} [Field F] [Field L] [Algebra F L]

/-- Compiler output: a concrete finite quotient presentation and an element
whose evaluation is the specified selected expression. -/
structure ExpressionPresentation (x : L) where
  presentation : FiniteRootPresentation F L
  value : presentation.Carrier
  evaluate_value : presentation.evaluate value = x

namespace FiniteRootPresentation

lemma eval₂_map_base (P : FiniteRootPresentation F L) (p : F[X]) (x : L) :
    (p.map (algebraMap F P.Carrier)).eval₂ P.evaluate.toRingHom x = aeval x p := by
  rw [eval₂_map]
  have hc : P.evaluate.toRingHom.comp (algebraMap F P.Carrier) = algebraMap F L := by
    ext a
    exact P.evaluate.commutes a
  rw [hc]
  rfl

end FiniteRootPresentation

namespace ExpressionPresentation

def constant (a : F) : ExpressionPresentation (F := F) (algebraMap F L a) where
  presentation := FiniteRootPresentation.base
  value := a
  evaluate_value := rfl

def add {x y : L} (A : ExpressionPresentation (F := F) x) (B : ExpressionPresentation (F := F) y) :
    ExpressionPresentation (F := F) (x+y) where
  presentation := A.presentation.tensor B.presentation
  value := A.presentation.tensorLeft B.presentation A.value + A.presentation.tensorRight B.presentation B.value
  evaluate_value := by
    rw [map_add,FiniteRootPresentation.tensor_evaluate_left,FiniteRootPresentation.tensor_evaluate_right,
      A.evaluate_value,B.evaluate_value]

def mul {x y : L} (A : ExpressionPresentation (F := F) x) (B : ExpressionPresentation (F := F) y) :
    ExpressionPresentation (F := F) (x*y) where
  presentation := A.presentation.tensor B.presentation
  value := A.presentation.tensorLeft B.presentation A.value * A.presentation.tensorRight B.presentation B.value
  evaluate_value := by
    rw [map_mul,FiniteRootPresentation.tensor_evaluate_left,FiniteRootPresentation.tensor_evaluate_right,
      A.evaluate_value,B.evaluate_value]

def neg {x : L} (A : ExpressionPresentation (F := F) x) : ExpressionPresentation (F := F) (-x) where
  presentation := A.presentation
  value := -A.value
  evaluate_value := by rw [map_neg,A.evaluate_value]

/-- Monicize a supplied base-field polynomial by explicit leading-coefficient
inversion, then adjoin the already selected root using its equation. -/
def selectedRoot (p : F[X]) (hp : p ≠ 0) (x : L) (hroot : aeval x p = 0) :
    ExpressionPresentation (F := F) x := by
  let q := p*C p.leadingCoeff⁻¹
  have hq : q.Monic := monic_mul_leadingCoeff_inv hp
  have hr : q.eval₂ (FiniteRootPresentation.base (F := F) (L := L)).evaluate.toRingHom x = 0 := by
    change aeval x q=0
    simp only [q,map_mul,hroot,zero_mul]
  exact ⟨(FiniteRootPresentation.base (F := F) (L := L)).adjoin q hq x hr,
    AdjoinRoot.root q,FiniteRootPresentation.adjoin_evaluate_root _ _ _ _ _⟩

/-- A semantic inverse is represented by one additional monic root adjunction.
No claim that all branches of the quotient invert the denominator is needed. -/
def inverse [DecidableEq F] {x : L} (A : ExpressionPresentation (F := F) x) (hx : x ≠ 0) :
    ExpressionPresentation (F := F) x⁻¹ := by
  let p := A.presentation.annihilator A.value
  have hp : p ≠ 0 := (A.presentation.annihilator_monic A.value).ne_zero
  have hr : aeval x p = 0 := by
    rw [← A.evaluate_value]
    exact A.presentation.annihilator_eval A.value
  let q := (inverseAnnihilator p).map (algebraMap F A.presentation.Carrier)
  have hq : q.Monic := (inverseAnnihilator_monic p hp).map _
  have hroot : q.eval₂ A.presentation.evaluate.toRingHom x⁻¹ = 0 := by
    rw [FiniteRootPresentation.eval₂_map_base]
    exact inverseAnnihilator_aeval p hp x hx hr
  exact ⟨A.presentation.adjoin q hq x⁻¹ hroot,AdjoinRoot.root q,
    FiniteRootPresentation.adjoin_evaluate_root _ _ _ _ _⟩

/-- Roots depending on prior expression values are monic square roots. -/
def squareRoot {r : L} (A : ExpressionPresentation (F := F) r) (x : L) (hx : x^2=r) :
    ExpressionPresentation (F := F) x := by
  let q : A.presentation.Carrier[X] := X^2-C A.value
  have hq : q.Monic := monic_X_pow_sub_C A.value (by decide : (2 : ℕ) ≠ 0)
  have hr : q.eval₂ A.presentation.evaluate.toRingHom x = 0 := by
    simp only [q,eval₂_sub,eval₂_pow,eval₂_X,eval₂_C]
    change x^2-A.presentation.evaluate A.value=0
    rw [hx,A.evaluate_value,sub_self]
  exact ⟨A.presentation.adjoin q hq x hr,AdjoinRoot.root q,
    FiniteRootPresentation.adjoin_evaluate_root _ _ _ _ _⟩

/-- The final finite determinant polynomial in the constructed multiplication table. -/
def annihilator {x : L} (A : ExpressionPresentation (F := F) x) : F[X] :=
  A.presentation.annihilator A.value

theorem annihilator_monic {x : L} (A : ExpressionPresentation (F := F) x) : A.annihilator.Monic :=
  A.presentation.annihilator_monic A.value

theorem annihilator_aeval {x : L} (A : ExpressionPresentation (F := F) x) : aeval x A.annihilator=0 := by
  unfold annihilator
  simpa only [A.evaluate_value] using A.presentation.annihilator_eval A.value

end ExpressionPresentation

/-- Structural recursion compiles the entire finite syntax tree, including all
selected roots and inverses, into an explicit power-product presentation. -/
def RootExpression.compile [DecidableEq F] {x : L} (e : RootExpression F L x) :
    ExpressionPresentation (F := F) x := by
  induction e with
  | constant a => exact ExpressionPresentation.constant a
  | add ex ey ihx ihy => exact ihx.add ihy
  | mul ex ey ihx ihy => exact ihx.mul ihy
  | neg ex ihx => exact ihx.neg
  | inverse ex hx ihx => exact ihx.inverse hx
  | selectedRoot p hp x hx => exact ExpressionPresentation.selectedRoot p hp x hx
  | squareRoot er x hx ihr => exact ihr.squareRoot x hx

/-- The determinant annihilator is produced from the expression itself, not an
unstructured algebraicity theorem. -/
def RootExpression.annihilator [DecidableEq F] {x : L} (e : RootExpression F L x) : F[X] :=
  e.compile.annihilator

theorem RootExpression.annihilator_spec [DecidableEq F] {x : L} (e : RootExpression F L x) :
    e.annihilator.Monic ∧ aeval x e.annihilator=0 :=
  ⟨e.compile.annihilator_monic,e.compile.annihilator_aeval⟩

/-- The emitted polynomial degree is the literal finite basis-cardinality of
its constructed presentation. -/
theorem RootExpression.annihilator_degree [DecidableEq F] {x : L} (e : RootExpression F L x) :
    e.annihilator.natDegree = Fintype.card e.compile.presentation.Index :=
  e.compile.presentation.annihilator_degree e.compile.value

theorem RootExpression.annihilator_ne_zero [DecidableEq F] {x : L} (e : RootExpression F L x) :
    e.annihilator ≠ 0 := (e.annihilator_spec).1.ne_zero

/-- A certified finite expression supplies the data needed by coefficient
normalization and residue extraction, without a basis-construction premise. -/
theorem Presented.compiled_annihilator [DecidableEq F] {x : L} (h : Presented F x) :
    ∃ e : RootExpression F L x, e.annihilator.Monic ∧
      aeval x e.annihilator=0 ∧ e.annihilator.natDegree=Fintype.card e.compile.presentation.Index := by
  obtain ⟨e⟩ := h
  exact ⟨e,e.annihilator_spec.1,e.annihilator_spec.2,e.annihilator_degree⟩

#print axioms RootExpression.compile
#print axioms RootExpression.annihilator_spec
end W3.Infinitesimal
