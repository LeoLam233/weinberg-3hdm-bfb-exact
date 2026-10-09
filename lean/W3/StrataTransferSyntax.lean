import W3.InfinitesimalFormulaTransfer

noncomputable section
namespace W3.StrataTransfer
open W3.Infinitesimal
abbrev Formula := OrderedPolynomialFormula

/-- Prefix k witnesses to an n-variable valuation. -/
def extendVec {A : Type*} {n : ℕ} (v : Fin n → A) :
    {k : ℕ} → (Fin k → A) → (Fin (n+k) → A)
  | 0, _ => v
  | k+1, w => Fin.cons (w 0) (extendVec v (fun i : Fin k => w i.succ))

def frontIndex (n k : ℕ) (i : Fin k) : Fin (n+k) := ⟨i.val, by omega⟩
def backIndex (n k : ℕ) (i : Fin n) : Fin (n+k) := ⟨k+i.val, by omega⟩

@[simp] theorem extendVec_front {A : Type*} {n k : ℕ} (v : Fin n → A) (w : Fin k → A) (i : Fin k) :
    extendVec v w (frontIndex n k i) = w i := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      change extendVec v (fun j => w j.succ) (frontIndex n k i) = w i.succ
      exact ih _ i

@[simp] theorem extendVec_back {A : Type*} {n k : ℕ} (v : Fin n → A) (w : Fin k → A) (i : Fin n) :
    extendVec v w (backIndex n k i) = v i := by
  induction k with
  | zero => simp [extendVec, backIndex]
  | succ k ih =>
    have hi : backIndex n (k+1) i = (backIndex n k i).succ := by
      apply Fin.ext
      simp [backIndex]
      omega
    rw [hi]
    change extendVec v (fun j => w j.succ) (backIndex n k i) = v i
    exact ih _

/-- Quantify all k prefix coordinates; this is an actual iteration of the unary syntax. -/
def exVec {n : ℕ} : (k : ℕ) → Formula (n+k) → Formula n
  | 0, p => p
  | k+1, p => exVec k (.ex p)

def allVec {n : ℕ} (k : ℕ) (p : Formula (n+k)) : Formula n := .neg (exVec k (.neg p))

theorem realize_exVec {A : Type*} [CommRing A] [LE A] {n : ℕ}
    (k : ℕ) (p : Formula (n+k)) (v : Fin n → A) :
    (exVec k p).Realize v ↔ ∃ w : Fin k → A, p.Realize (extendVec v w) := by
  induction k with
  | zero => simp only [exVec, extendVec]; exact ⟨fun h => ⟨Fin.elim0,h⟩,fun ⟨_,h⟩ => h⟩
  | succ k ih =>
    rw [exVec, ih]
    constructor
    · rintro ⟨w,x,hx⟩
      exact ⟨Fin.cons x w, by simpa [extendVec] using hx⟩
    · rintro ⟨w,hw⟩
      exact ⟨(fun i : Fin k => w i.succ), w 0, hw⟩

@[simp] theorem realize_allVec {A : Type*} [CommRing A] [LE A] {n : ℕ}
    (k : ℕ) (p : Formula (n+k)) (v : Fin n → A) :
    (allVec k p).Realize v ↔ ∀ w : Fin k → A, p.Realize (extendVec v w) := by
  simp only [allVec, OrderedPolynomialFormula.Realize, realize_exVec, not_exists, not_not]

/-- Finite conjunction, compiled into the actual binary syntax. -/
def allFin {n : ℕ} : (k : ℕ) → (Fin k → Formula n) → Formula n
  | 0, _ => .eqZero 0
  | k+1, p => .conj (p 0) (allFin k (fun i => p i.succ))

@[simp] theorem realize_allFin {A : Type*} [CommRing A] [LE A] {n : ℕ}
    (k : ℕ) (p : Fin k → Formula n) (v : Fin n → A) :
    (allFin k p).Realize v ↔ ∀ i, (p i).Realize v := by
  induction k with
  | zero => simp [allFin, OrderedPolynomialFormula.Realize, intPolynomialEval]
  | succ k ih =>
    simp only [allFin, OrderedPolynomialFormula.Realize, ih, Fin.forall_fin_succ]

end W3.StrataTransfer
