import W3.InfinitesimalMinimumTransfer

/-!
# Full finite ordered-polynomial formula transfer

A small explicit first-order syntax: integer-polynomial equalities and
inequalities, conjunction, negation, and quantification over one field variable.
Its coordinatewise ultrapower semantics is proved by induction, including
existential witness selection. The base embedding is consequently elementary
for every formula in this syntax. No unproved transfer interface is used.
-/
noncomputable section
namespace W3.Infinitesimal
open Filter

/-- Finite first-order formulas in the ordered-ring polynomial language.
The n free variables are indexed by Fin n; a quantified variable is prepended. -/
inductive OrderedPolynomialFormula : ℕ → Type
  | eqZero {n : ℕ} (p : MvPolynomial (Fin n) ℤ) : OrderedPolynomialFormula n
  | nonneg {n : ℕ} (p : MvPolynomial (Fin n) ℤ) : OrderedPolynomialFormula n
  | conj {n : ℕ} (p q : OrderedPolynomialFormula n) : OrderedPolynomialFormula n
  | neg {n : ℕ} (p : OrderedPolynomialFormula n) : OrderedPolynomialFormula n
  | ex {n : ℕ} (p : OrderedPolynomialFormula (n + 1)) : OrderedPolynomialFormula n

namespace OrderedPolynomialFormula

def Realize {A : Type*} [CommRing A] [LE A] :
    {n : ℕ} → OrderedPolynomialFormula n → (Fin n → A) → Prop
  | _, .eqZero p, v => intPolynomialEval p v = 0
  | _, .nonneg p, v => 0 ≤ intPolynomialEval p v
  | _, .conj p q, v => p.Realize v ∧ q.Realize v
  | _, .neg p, v => ¬p.Realize v
  | _, .ex p, v => ∃ x, p.Realize (Fin.cons x v)

/-- Universal quantification is derived from negation and existence. -/
def all {n : ℕ} (p : OrderedPolynomialFormula (n + 1)) : OrderedPolynomialFormula n :=
  .neg (.ex (.neg p))

def disj {n : ℕ} (p q : OrderedPolynomialFormula n) : OrderedPolynomialFormula n :=
  .neg (.conj (.neg p) (.neg q))

def implies {n : ℕ} (p q : OrderedPolynomialFormula n) : OrderedPolynomialFormula n :=
  .neg (.conj p (.neg q))

@[simp] theorem realize_all {A : Type*} [CommRing A] [LE A] {n : ℕ}
    (p : OrderedPolynomialFormula (n + 1)) (v : Fin n → A) :
    p.all.Realize v ↔ ∀ x : A, p.Realize (Fin.cons x v) := by
  simp only [all, Realize, not_exists, not_not]

@[simp] theorem realize_disj {A : Type*} [CommRing A] [LE A] {n : ℕ}
    (p q : OrderedPolynomialFormula n) (v : Fin n → A) :
    (p.disj q).Realize v ↔ p.Realize v ∨ q.Realize v := by
  simp only [disj, Realize]
  tauto

@[simp] theorem realize_implies {A : Type*} [CommRing A] [LE A] {n : ℕ}
    (p q : OrderedPolynomialFormula n) (v : Fin n → A) :
    (p.implies q).Realize v ↔ (p.Realize v → q.Realize v) := by
  simp only [implies, Realize, not_and, not_not]

end OrderedPolynomialFormula

variable (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem germsOfVector_cons {n : ℕ} (w : K → K) (v : K → Fin n → K) :
    germsOfVector K (fun i => Fin.cons (w i) (v i)) =
      Fin.cons (germRingHom K w) (germsOfVector K v) := by
  funext j
  cases j using Fin.cases <;> rfl

/-- Łoś's equivalence for the explicit polynomial syntax, proved directly. -/
theorem orderedPolynomialFormula_germs {n : ℕ} (p : OrderedPolynomialFormula n) :
    ∀ v : K → Fin n → K,
      p.Realize (germsOfVector K v) ↔
        ∀ᶠ i in (extensionUltrafilter K : Filter K), p.Realize (v i) := by
  classical
  induction p with
  | eqZero p =>
    intro v
    simp only [OrderedPolynomialFormula.Realize, intPolynomialEval_germs]
    exact Germ.coe_eq
  | nonneg p =>
    intro v
    simp only [OrderedPolynomialFormula.Realize, intPolynomialEval_germs]
    exact Germ.coe_le
  | conj p q ihp ihq =>
    intro v
    simp only [OrderedPolynomialFormula.Realize, ihp, ihq, Filter.eventually_and]
  | neg p ih =>
    intro v
    simp only [OrderedPolynomialFormula.Realize, ih]
    exact Ultrafilter.eventually_not.symm
  | @ex n p ih =>
    intro v
    constructor
    · rintro ⟨x, hx⟩
      have hx' : p.Realize (germsOfVector K
          (fun i => Fin.cons (coefficientRep K x i) (v i))) := by
        rw [germsOfVector_cons, germ_coefficientRep]
        exact hx
      exact ((ih _).mp hx').mono (fun i hi => ⟨coefficientRep K x i, hi⟩)
    · intro h
      let w : K → K := fun i => if hi : ∃ x : K, p.Realize (Fin.cons x (v i)) then
        Classical.choose hi else 0
      have hw : ∀ᶠ i in (extensionUltrafilter K : Filter K),
          p.Realize (Fin.cons (w i) (v i)) := by
        apply h.mono
        intro i hi
        change (∃ x : K, p.Realize (Fin.cons x (v i))) at hi
        dsimp only [w]
        rw [dite_eq_left hi]
        exact Classical.choose_spec hi
      refine ⟨germRingHom K w, ?_⟩
      have hh := (ih (fun i => Fin.cons (w i) (v i))).mpr hw
      rwa [germsOfVector_cons] at hh

/-- The actual base embedding preserves and reflects every first-order formula
in finite integer-polynomial ordered-ring syntax, including quantifier alternation. -/
theorem orderedPolynomialFormula_embed {n : ℕ} (p : OrderedPolynomialFormula n)
    (v : Fin n → K) :
    p.Realize (fun j => embed K (v j)) ↔ p.Realize v := by
  have h := orderedPolynomialFormula_germs K p (fun _ => v)
  exact h.trans Filter.eventually_const

/-- Full finite-tower elementarity, established by iterating proved one-step transfer. -/
theorem orderedPolynomialFormula_tower (M : OrderedFieldModel) (k : ℕ) {n : ℕ}
    (p : OrderedPolynomialFormula n) (v : Fin n → M.Carrier) :
    p.Realize (fun j => baseEmbed M k (v j)) ↔ p.Realize v := by
  induction k with
  | zero => exact Iff.rfl
  | succ k ih =>
    exact (orderedPolynomialFormula_embed (Tower M k) p
      (fun j => baseEmbed M k (v j))).trans ih

/-- Universal statements with arbitrary extension-valued parameters transfer too;
parameters are represented coordinatewise, not required to lie in the base image. -/
theorem orderedPolynomialFormula_universal_extension {n : ℕ}
    (p : OrderedPolynomialFormula n) (h : ∀ v : Fin n → K, p.Realize v) :
    ∀ v : Fin n → Extension K, p.Realize v := by
  intro v
  rw [← germs_vectorRepresentatives K v]
  apply (orderedPolynomialFormula_germs K p _).mpr
  exact Eventually.of_forall (fun i => h (vectorRepresentatives K v i))

/-- Every proved universal ordered-polynomial formula, including any nested
quantifiers and disjunctions in its body, holds for arbitrary points of every stage. -/
theorem orderedPolynomialFormula_universal_tower (M : OrderedFieldModel) (k : ℕ)
    {n : ℕ} (p : OrderedPolynomialFormula n)
    (h : ∀ v : Fin n → M.Carrier, p.Realize v) :
    ∀ v : Fin n → Tower M k, p.Realize v := by
  induction k with
  | zero => exact h
  | succ k ih => exact orderedPolynomialFormula_universal_extension (Tower M k) p ih

#print axioms orderedPolynomialFormula_germs
#print axioms orderedPolynomialFormula_tower
#print axioms orderedPolynomialFormula_universal_tower
end W3.Infinitesimal
