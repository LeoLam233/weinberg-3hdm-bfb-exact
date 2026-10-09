import W3.InfinitesimalRealClosed
import W3.InfinitesimalTower
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Order.Filter.Finite

/-!
# Genuine finite-polynomial minimum transfer through the actual tower

The only premise is the universal theorem in the preceding field. Coefficients,
minimizers and comparison points are represented coordinatewise; finite domain
constraints are intersected in the ultrafilter. This proves transfer, rather than
postulating a minimum or an unformalized real-closed transfer principle.
-/
noncomputable section
namespace W3.Infinitesimal
open Filter

/-- Fixed integer-polynomial syntax, evaluated in any commutative ring. -/
def intPolynomialEval {σ A : Type*} [CommRing A] (p : MvPolynomial σ ℤ) (v : σ → A) : A :=
  MvPolynomial.eval₂Hom (Int.castRingHom A) v p

theorem intPolynomialEval_natural {σ A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (p : MvPolynomial σ ℤ) (v : σ → A) :
    f (intPolynomialEval p v) = intPolynomialEval p (fun j => f (v j)) := by
  have hc : f.comp (Int.castRingHom A) = Int.castRingHom B := RingHom.ext_int _ _
  simpa only [intPolynomialEval, hc] using
    MvPolynomial.map_eval₂Hom (Int.castRingHom A) v f p

variable (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Assemble coordinate functions into a vector in the actual extension. -/
def germsOfVector {σ : Type*} (v : K → σ → K) : σ → Extension K :=
  fun j => germRingHom K (fun i => v i j)

/-- A simultaneous representative for every entry of an extension-valued vector. -/
def vectorRepresentatives {σ : Type*} (v : σ → Extension K) : K → σ → K :=
  fun i j => coefficientRep K (v j) i

@[simp] theorem germs_vectorRepresentatives {σ : Type*} (v : σ → Extension K) :
    germsOfVector K (vectorRepresentatives K v) = v := by
  funext j
  exact germ_coefficientRep K (v j)

theorem intPolynomialEval_germs {σ : Type*} (p : MvPolynomial σ ℤ) (v : K → σ → K) :
    intPolynomialEval p (germsOfVector K v) =
      germRingHom K (fun i => intPolynomialEval p (v i)) := by
  have hfun : intPolynomialEval p (fun j i => v i j) =
      (fun i => intPolynomialEval p (v i)) := by
    funext i
    exact intPolynomialEval_natural (Pi.evalRingHom (fun _ : K => K) i) p (fun j i => v i j)
  rw [← hfun]
  exact (intPolynomialEval_natural (germRingHom K) p (fun j i => v i j)).symm

/-- Parameter values are arbitrary extension values; only coordinates of the
chosen variables need to be supplied by the caller. -/
theorem intPolynomialEval_parameters_germs {σ τ : Type*}
    (p : MvPolynomial (σ ⊕ τ) ℤ) (κ : σ → Extension K) (x : K → τ → K) :
    intPolynomialEval p (Sum.elim κ (germsOfVector K x)) =
      germRingHom K (fun i => intPolynomialEval p
        (Sum.elim (vectorRepresentatives K κ i) (x i))) := by
  have hv : Sum.elim κ (germsOfVector K x) =
      germsOfVector K (fun i => Sum.elim (vectorRepresentatives K κ i) (x i)) := by
    funext j
    cases j with
    | inl j => exact (germ_coefficientRep K (κ j)).symm
    | inr j => rfl
  rw [hv, intPolynomialEval_germs]

/-- Full universal minimization property in fixed integer-polynomial syntax.
D comprises finitely many domain equalities. E comprises optional finite
polynomial equations satisfied by the selected minimizer. -/
def PolynomialMinimumProperty {p n d e : ℕ}
    (P : MvPolynomial (Fin p ⊕ Fin n) ℤ)
    (D : Fin d → MvPolynomial (Fin n) ℤ)
    (E : Fin e → MvPolynomial (Fin p ⊕ Fin n) ℤ)
    (A : Type*) [CommRing A] [LE A] : Prop :=
  ∀ κ : Fin p → A, ∃ x : Fin n → A,
    (∀ j, intPolynomialEval (D j) x = 0) ∧
    (∀ j, intPolynomialEval (E j) (Sum.elim κ x) = 0) ∧
    ∀ y : Fin n → A, (∀ j, intPolynomialEval (D j) y = 0) →
      intPolynomialEval P (Sum.elim κ x) ≤ intPolynomialEval P (Sum.elim κ y)

/-- Actual one-step minimum transfer, including finite stationary equations. -/
theorem polynomialMinimumProperty_extension {p n d e : ℕ}
    (P : MvPolynomial (Fin p ⊕ Fin n) ℤ)
    (D : Fin d → MvPolynomial (Fin n) ℤ)
    (E : Fin e → MvPolynomial (Fin p ⊕ Fin n) ℤ)
    (hbase : PolynomialMinimumProperty P D E K) :
    PolynomialMinimumProperty P D E (Extension K) := by
  intro κ
  let x : K → Fin n → K := fun i => Classical.choose (hbase (vectorRepresentatives K κ i))
  have hx (i : K) := Classical.choose_spec (hbase (vectorRepresentatives K κ i))
  refine ⟨germsOfVector K x, ?_, ?_, ?_⟩
  · intro j
    rw [intPolynomialEval_germs]
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall (fun i => (hx i).1 j)
  · intro j
    rw [intPolynomialEval_parameters_germs]
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall (fun i => (hx i).2.1 j)
  · intro y hy
    have hDy : ∀ᶠ i in (extensionUltrafilter K : Filter K),
        ∀ j, intPolynomialEval (D j) (vectorRepresentatives K y i) = 0 := by
      apply Filter.eventually_all.mpr
      intro j
      have hj := hy j
      rw [← germs_vectorRepresentatives K y, intPolynomialEval_germs] at hj
      exact Germ.coe_eq.mp hj
    rw [← germs_vectorRepresentatives K y,
      intPolynomialEval_parameters_germs, intPolynomialEval_parameters_germs]
    apply Germ.coe_le.mpr
    exact hDy.mono (fun i hi => (hx i).2.2 (vectorRepresentatives K y i) hi)

/-- Induction lifts a proved universal base-field extremum theorem through every
actual level of the tower, with no new minimum-attainment premise. -/
theorem polynomialMinimumProperty_tower {p n d e : ℕ}
    (P : MvPolynomial (Fin p ⊕ Fin n) ℤ)
    (D : Fin d → MvPolynomial (Fin n) ℤ)
    (E : Fin e → MvPolynomial (Fin p ⊕ Fin n) ℤ)
    (M : OrderedFieldModel) (hbase : PolynomialMinimumProperty P D E M.Carrier) :
    ∀ k : ℕ, PolynomialMinimumProperty P D E (Tower M k) := by
  intro k
  induction k with
  | zero => exact hbase
  | succ k ih => exact polynomialMinimumProperty_extension (Tower M k) P D E ih

#print axioms polynomialMinimumProperty_extension
#print axioms polynomialMinimumProperty_tower
end W3.Infinitesimal
