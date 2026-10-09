import W3.InfinitesimalExpressionCompiler
import W3.InfinitesimalFiniteResidue

/-! # Finite-input selected-root syntax
The only leaves are rational numbers, fifteen supplied input coordinates, and
the finitely many epsilon generators. A root node contains a finite polynomial
coefficient program and an index into a primitive real-root list. Structural
interpretation returns actual compiler input data; it never chooses a witness
of `Presented` and never receives an arbitrary selected ambient scalar.
This module supplies the primitive implementation interface, not by itself
the complete W3 candidate or residue program. -/
noncomputable section
namespace W3.FiniteInput
open Polynomial W3.Infinitesimal

inductive CoefficientCode (n : Nat) where
  | rational : ℚ → CoefficientCode n
  | input : Fin 15 → CoefficientCode n
  | epsilon : Fin n → CoefficientCode n
  | add : CoefficientCode n → CoefficientCode n → CoefficientCode n
  | mul : CoefficientCode n → CoefficientCode n → CoefficientCode n
  | neg : CoefficientCode n → CoefficientCode n
  | inv : CoefficientCode n → CoefficientCode n

def CoefficientCode.eval {F : Type*} [Field F] [CharZero F] {n : Nat}
    (input : Fin 15 → F) (epsilon : Fin n → F) : CoefficientCode n → F
  | .rational q => q
  | .input i => input i
  | .epsilon i => epsilon i
  | .add a b => a.eval input epsilon + b.eval input epsilon
  | .mul a b => a.eval input epsilon * b.eval input epsilon
  | .neg a => -a.eval input epsilon
  | .inv a => (a.eval input epsilon)⁻¹

namespace CoefficientCode

/-- Rename only the finite epsilon generator interface. In particular,
`Fin.succ` embeds a preceding-stage code into the next rational stage. -/
def renameEpsilon {n m : Nat} (f : Fin n → Fin m) : CoefficientCode n → CoefficientCode m
  | .rational q => .rational q
  | .input i => .input i
  | .epsilon i => .epsilon (f i)
  | .add a b => .add (a.renameEpsilon f) (b.renameEpsilon f)
  | .mul a b => .mul (a.renameEpsilon f) (b.renameEpsilon f)
  | .neg a => .neg (a.renameEpsilon f)
  | .inv a => .inv (a.renameEpsilon f)

@[simp] theorem eval_renameEpsilon {F : Type*} [Field F] [CharZero F] {n m : Nat}
    (f : Fin n → Fin m) (input : Fin 15 → F) (epsilon : Fin m → F)
    (c : CoefficientCode n) :
    (c.renameEpsilon f).eval input epsilon = c.eval input (epsilon ∘ f) := by
  induction c <;> simp_all [renameEpsilon,eval]

/-- Coefficient programs are natural under field embeddings, including their
rational constants and totalized inverses. -/
theorem eval_map {F G : Type*} [Field F] [CharZero F] [Field G] [CharZero G]
    {n : Nat} (f : F →+* G) (input : Fin 15 → F) (epsilon : Fin n → F)
    (c : CoefficientCode n) :
    c.eval (f ∘ input) (f ∘ epsilon) = f (c.eval input epsilon) := by
  induction c <;> simp_all [eval,map_ratCast]

end CoefficientCode

def polynomialOfList {F : Type*} [Semiring F] : List F → F[X]
  | [] => 0
  | a :: as => C a + X * polynomialOfList as

inductive Code (n : Nat) where
  | coefficient : CoefficientCode n → Code n
  | add : Code n → Code n → Code n
  | mul : Code n → Code n → Code n
  | neg : Code n → Code n
  | inv : Code n → Code n
  | root : List (CoefficientCode n) → Nat → Code n
  | squareRoot : Code n → Nat → Code n

variable {F K : Type*} [Field F] [CharZero F] [DecidableEq F] [Field K] [Algebra F K]
    [LinearOrder K] [IsStrictOrderedRing K]

structure Evaluated where
  value : K
  expression : RootExpression F K value

namespace Evaluated

def zero : Evaluated (F := F) (K := K) :=
  ⟨0, by simpa only [map_zero] using (RootExpression.constant (F := F) (L := K) 0)⟩

def add (a b : Evaluated (F := F) (K := K)) : Evaluated (F := F) (K := K) :=
  ⟨a.value + b.value, .add a.expression b.expression⟩

def mul (a b : Evaluated (F := F) (K := K)) : Evaluated (F := F) (K := K) :=
  ⟨a.value * b.value, .mul a.expression b.expression⟩

def neg (a : Evaluated (F := F) (K := K)) : Evaluated (F := F) (K := K) :=
  ⟨-a.value, .neg a.expression⟩

def inv (a : Evaluated (F := F) (K := K)) : Evaluated (F := F) (K := K) := by
  by_cases h : a.value = 0
  · exact zero
  · exact ⟨a.value⁻¹, .inverse a.expression h⟩

def root (O : RealRootEnumeration K) (p : F[X]) (i : Nat) : Evaluated (F := F) (K := K) := by
  by_cases hp : p = 0
  · exact zero
  · let rs := O.roots (p.map (algebraMap F K))
    match h : rs[i]? with
    | none => exact zero
    | some x =>
      have hx : x ∈ rs := List.mem_of_getElem? h
      have hpm : p.map (algebraMap F K) ≠ 0 :=
        (Polynomial.map_ne_zero_iff (RingHom.injective _)).mpr hp
      have hr := (O.correct _ hpm x).mp hx
      refine ⟨x, .selectedRoot p hp x ?_⟩
      simpa only [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def] using hr

def squareRoot (O : RealRootEnumeration K) (a : Evaluated (F := F) (K := K)) (i : Nat) :
    Evaluated (F := F) (K := K) := by
  let p : K[X] := X^2-C a.value
  have hp : p ≠ 0 := (monic_X_pow_sub_C a.value (by decide : (2 : Nat) ≠ 0)).ne_zero
  let rs := O.roots p
  match h : rs[i]? with
  | none => exact zero
  | some x =>
    have hx : x ∈ rs := List.mem_of_getElem? h
    have hr := (O.correct p hp x).mp hx
    have hs : x^2 = a.value := by
      simpa only [Polynomial.IsRoot,p,Polynomial.eval_sub,Polynomial.eval_pow,
        Polynomial.eval_X,Polynomial.eval_C,sub_eq_zero] using hr
    exact ⟨x, .squareRoot a.expression x hs⟩
end Evaluated

def Code.run {n : Nat} (input : Fin 15 → F) (epsilon : Fin n → F) (O : RealRootEnumeration K) :
    Code n → Evaluated (F := F) (K := K)
  | .coefficient a => ⟨algebraMap F K (a.eval input epsilon), .constant (a.eval input epsilon)⟩
  | .add a b => (a.run input epsilon O).add (b.run input epsilon O)
  | .mul a b => (a.run input epsilon O).mul (b.run input epsilon O)
  | .neg a => (a.run input epsilon O).neg
  | .inv a => (a.run input epsilon O).inv
  | .root as i => Evaluated.root O (polynomialOfList (as.map (·.eval input epsilon))) i
  | .squareRoot a i => Evaluated.squareRoot O (a.run input epsilon O) i

namespace Code
variable {n : Nat} (input : Fin 15 → F) (epsilon : Fin n → F) (O : RealRootEnumeration K)
@[simp] theorem run_coefficient_value (a : CoefficientCode n) :
    ((coefficient a).run input epsilon O).value = algebraMap F K (a.eval input epsilon) := rfl
@[simp] theorem run_add_value (a b : Code n) :
    ((add a b).run input epsilon O).value =
      (a.run input epsilon O).value + (b.run input epsilon O).value := rfl
@[simp] theorem run_mul_value (a b : Code n) :
    ((mul a b).run input epsilon O).value =
      (a.run input epsilon O).value * (b.run input epsilon O).value := rfl
@[simp] theorem run_neg_value (a : Code n) :
    ((neg a).run input epsilon O).value = -(a.run input epsilon O).value := rfl
@[simp] theorem run_inv_value (a : Code n) :
    ((inv a).run input epsilon O).value = (a.run input epsilon O).value⁻¹ := by
  by_cases h : (a.run input epsilon O).value = 0
  · simp [Code.run,Evaluated.inv,h,Evaluated.zero]
  · simp [Code.run,Evaluated.inv,h]
end Code

theorem run_annihilator {n : Nat} (input : Fin 15 → F) (epsilon : Fin n → F)
    (O : RealRootEnumeration K) (c : Code n) :
    (c.run input epsilon O).expression.annihilator.Monic ∧
      Polynomial.aeval (c.run input epsilon O).value (c.run input epsilon O).expression.annihilator = 0 :=
  (c.run input epsilon O).expression.annihilator_spec


namespace Evaluated

theorem root_value_of_get (O : RealRootEnumeration K) (p : F[X]) (hp : p ≠ 0)
    (i : Nat) (x : K)
    (h : (O.roots (p.map (algebraMap F K)))[i]? = some x) :
    (root O p i).value = x := by
  simp only [root, dif_neg hp]
  split <;> simp_all

theorem squareRoot_value_of_get (O : RealRootEnumeration K)
    (a : Evaluated (F := F) (K := K)) (i : Nat) (x : K)
    (h : (O.roots (X^2-C a.value))[i]? = some x) :
    (squareRoot O a i).value = x := by
  simp only [squareRoot]
  split <;> simp_all

end Evaluated

/-- This polynomial's complete coefficient data are finite input expressions. -/
def coefficientPolynomial {n : Nat} (input : Fin 15 → F) (epsilon : Fin n → F)
    (cs : List (CoefficientCode n)) : F[X] :=
  polynomialOfList (cs.map (·.eval input epsilon))

/-- Uniform synthesis of every selected-root code from one primitive finite
root enumeration. No semantic root or ordinal is an additional input. -/
def rootFamily {n : Nat} (input : Fin 15 → F) (epsilon : Fin n → F)
    (O : RealRootEnumeration K) (cs : List (CoefficientCode n)) : List (Code n) :=
  let p := coefficientPolynomial input epsilon cs
  List.ofFn (fun i : Fin (O.roots (p.map (algebraMap F K))).length => .root cs i.val)

/-- Interpreting the synthesized codes recovers exactly the supplied root list,
including repeated roots and its original order. -/
theorem rootFamily_correct {n : Nat} (input : Fin 15 → F) (epsilon : Fin n → F)
    (O : RealRootEnumeration K) (cs : List (CoefficientCode n))
    (hp : coefficientPolynomial input epsilon cs ≠ 0) :
    (rootFamily input epsilon O cs).map (fun c => (c.run input epsilon O).value) =
      O.roots ((coefficientPolynomial input epsilon cs).map (algebraMap F K)) := by
  unfold rootFamily
  rw [List.map_ofFn]
  conv_rhs => rw [← List.ofFn_getElem (xs := O.roots ((coefficientPolynomial input epsilon cs).map (algebraMap F K)))]
  apply List.ofFn_inj.mpr
  funext i
  exact Evaluated.root_value_of_get O _ hp i.val _ (List.getElem?_eq_getElem i.isLt)

/-- The analogous uniform family for a quadratic over a previous selected
expression. This supplies all square-root signs without an extra branch oracle. -/
def squareRootFamily {n : Nat} (input : Fin 15 → F) (epsilon : Fin n → F)
    (O : RealRootEnumeration K) (a : Code n) : List (Code n) :=
  let p : K[X] := X^2-C (a.run input epsilon O).value
  List.ofFn (fun i : Fin (O.roots p).length => .squareRoot a i.val)

theorem squareRootFamily_correct {n : Nat} (input : Fin 15 → F) (epsilon : Fin n → F)
    (O : RealRootEnumeration K) (a : Code n) :
    (squareRootFamily input epsilon O a).map (fun c => (c.run input epsilon O).value) =
      O.roots (X^2-C (a.run input epsilon O).value) := by
  unfold squareRootFamily
  rw [List.map_ofFn]
  conv_rhs => rw [← List.ofFn_getElem (xs := O.roots (X^2-C (a.run input epsilon O).value))]
  apply List.ofFn_inj.mpr
  funext i
  exact Evaluated.squareRoot_value_of_get O _ i.val _ (List.getElem?_eq_getElem i.isLt)

#print axioms rootFamily_correct
#print axioms squareRootFamily_correct
#print axioms Code.run
#print axioms run_annihilator
end W3.FiniteInput
