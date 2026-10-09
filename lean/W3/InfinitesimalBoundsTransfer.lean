import W3.InfinitesimalMinimumTransfer

/-! # Transfer of fixed lower bounds against all extension-valued points
This preserves an already proved real minimum value, rather than merely proving
that some new minimum exists in the enlarged domain.
-/
noncomputable section
namespace W3.Infinitesimal
open Filter

variable (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]

lemma intPolynomialEval_embeddedParameters_germs {σ τ : Type*}
    (P : MvPolynomial (σ ⊕ τ) ℤ) (κ : σ → K) (x : K → τ → K) :
    intPolynomialEval P (Sum.elim (fun j => embed K (κ j)) (germsOfVector K x)) =
      germRingHom K (fun i => intPolynomialEval P (Sum.elim κ (x i))) := by
  have hv : Sum.elim (fun j => embed K (κ j)) (germsOfVector K x) =
      germsOfVector K (fun i => Sum.elim κ (x i)) := by
    funext j
    cases j <;> rfl
  rw [hv, intPolynomialEval_germs]

/-- An exact constant lower bound over a polynomial equality domain. -/
def PolynomialLowerBound {p n d : ℕ}
    (P : MvPolynomial (Fin p ⊕ Fin n) ℤ) (D : Fin d → MvPolynomial (Fin n) ℤ)
    {A : Type*} [CommRing A] [LE A] (κ : Fin p → A) (c : A) : Prop :=
  ∀ y : Fin n → A, (∀ j, intPolynomialEval (D j) y = 0) →
    c ≤ intPolynomialEval P (Sum.elim κ y)

/-- One-step transfer preserves a fixed lower bound over the entire enlarged domain. -/
theorem polynomialLowerBound_extension {p n d : ℕ}
    (P : MvPolynomial (Fin p ⊕ Fin n) ℤ) (D : Fin d → MvPolynomial (Fin n) ℤ)
    (κ : Fin p → K) (c : K) (hbase : PolynomialLowerBound P D κ c) :
    PolynomialLowerBound P D (fun j => embed K (κ j)) (embed K c) := by
  intro y hy
  have hDy : ∀ᶠ i in (extensionUltrafilter K : Filter K),
      ∀ j, intPolynomialEval (D j) (vectorRepresentatives K y i) = 0 := by
    apply Filter.eventually_all.mpr
    intro j
    have hj := hy j
    rw [← germs_vectorRepresentatives K y, intPolynomialEval_germs] at hj
    exact Germ.coe_eq.mp hj
  rw [← germs_vectorRepresentatives K y, intPolynomialEval_embeddedParameters_germs]
  apply Germ.coe_le.mpr
  exact hDy.mono (fun i hi => hbase (vectorRepresentatives K y i) hi)

/-- A proved lower bound from the base field stays valid against arbitrary points
of every actual tower level. -/
theorem polynomialLowerBound_tower {p n d : ℕ}
    (P : MvPolynomial (Fin p ⊕ Fin n) ℤ) (D : Fin d → MvPolynomial (Fin n) ℤ)
    (M : OrderedFieldModel) (κ : Fin p → M.Carrier) (c : M.Carrier)
    (hbase : PolynomialLowerBound P D κ c) (k : ℕ) :
    PolynomialLowerBound P D (fun j => baseEmbed M k (κ j)) (baseEmbed M k c) := by
  induction k with
  | zero => exact hbase
  | succ k ih => exact polynomialLowerBound_extension (Tower M k) P D _ _ ih

/-- Embedded witnesses retain their polynomial equalities exactly. -/
theorem intPolynomialEval_baseEmbed (M : OrderedFieldModel) (k : ℕ) {σ : Type*}
    (P : MvPolynomial σ ℤ) (x : σ → M.Carrier) :
    intPolynomialEval P (fun j => baseEmbed M k (x j)) =
      baseEmbed M k (intPolynomialEval P x) :=
  (intPolynomialEval_natural (baseEmbed M k).toRingHom P x).symm

#print axioms polynomialLowerBound_tower
end W3.Infinitesimal
