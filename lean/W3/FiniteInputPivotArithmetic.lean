import W3.FiniteInputPivotRootSelection

/-! Literal complex-coordinate arithmetic for Eq. (41), with finite matrix
zero testing and no semantic constants introduced into the output program. -/
noncomputable section
namespace W3.FiniteInput
open Polynomial W3.Infinitesimal W3.Weighted ComplexConjugate

abbrev PivotMatrixCode (n : Nat) := Fin 3 → Fin 3 → ComplexPair (Code n)
abbrev PivotRowCode (n : Nat) := Fin 3 → ComplexPair (Code n)

variable {F : Type*} [Field F] [CharZero F] [DecidableEq F] [Algebra F ℝ]
variable {n : Nat} (input : Fin 15 → F) (epsilon : Fin n → F)
    (O : RealRootEnumeration ℝ)

/-- Interpret the two retained real coordinate programs as one complex number. -/
def pivotComplexValue (z : ComplexPair (Code n)) : ℂ :=
  ⟨(z.re.run input epsilon O).value,(z.im.run input epsilon O).value⟩
def pivotRowValue (a : PivotRowCode n) : Fin 3 → ℂ :=
  fun j => pivotComplexValue input epsilon O (a j)
def pivotMatrixValue (A : PivotMatrixCode n) : PivotedGram.HermitianMatrix :=
  fun i j => pivotComplexValue input epsilon O (A i j)

def zeroPivotRow : PivotRowCode n := fun _ => ⟨0,0⟩
def complexSubCode (a b : ComplexPair (Code n)) : ComplexPair (Code n) :=
  ⟨a.re-b.re,a.im-b.im⟩
def complexRealDivCode (a : ComplexPair (Code n)) (d : Code n) : ComplexPair (Code n) :=
  ⟨a.re/d,a.im/d⟩

@[simp] theorem pivotComplexValue_sub (a b : ComplexPair (Code n)) :
    pivotComplexValue input epsilon O (complexSubCode a b) =
      pivotComplexValue input epsilon O a - pivotComplexValue input epsilon O b := by
  apply Complex.ext <;> simp [pivotComplexValue,complexSubCode]

@[simp] theorem pivotComplexValue_mul (a b : ComplexPair (Code n)) :
    pivotComplexValue input epsilon O (complexMul a b) =
      pivotComplexValue input epsilon O a * pivotComplexValue input epsilon O b := by
  apply Complex.ext <;> simp [pivotComplexValue,complexMul,Complex.mul_re,Complex.mul_im]

@[simp] theorem pivotComplexValue_conj (a : ComplexPair (Code n)) :
    pivotComplexValue input epsilon O (complexConj a) =
      conj (pivotComplexValue input epsilon O a) := by
  apply Complex.ext <;> simp [pivotComplexValue,complexConj]

@[simp] theorem pivotComplexValue_realDiv (a : ComplexPair (Code n)) (d : Code n) :
    pivotComplexValue input epsilon O (complexRealDivCode a d) =
      pivotComplexValue input epsilon O a / ((d.run input epsilon O).value : ℂ) := by
  apply Complex.ext <;> simp [pivotComplexValue,complexRealDivCode]

@[simp] theorem pivotRowValue_zero :
    pivotRowValue input epsilon O (zeroPivotRow : PivotRowCode n) = 0 := by
  funext j
  apply Complex.ext <;> simp [pivotRowValue,zeroPivotRow,pivotComplexValue]

/-- At most nine pairs of exact scalar zero tests. -/
def pivotMatrixZeroTest (A : PivotMatrixCode n) : Bool :=
  (List.finRange 3).all fun i => (List.finRange 3).all fun j =>
    decide (((A i j).re.run input epsilon O).value = 0) &&
    decide (((A i j).im.run input epsilon O).value = 0)

theorem pivotMatrixZeroTest_correct (A : PivotMatrixCode n) :
    pivotMatrixZeroTest input epsilon O A = true ↔ pivotMatrixValue input epsilon O A = 0 := by
  simp only [pivotMatrixZeroTest,List.all_eq_true,List.mem_finRange,forall_const,
    Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · intro h
    funext i j
    apply Complex.ext
    · exact (h i j).1
    · exact (h i j).2
  · intro h i j
    have he := congrFun (congrFun h i) j
    exact ⟨congrArg Complex.re he,congrArg Complex.im he⟩

/-- a_j = K_ij / selected_nonnegative_root(K_ii). -/
def pivotRowCode (A : PivotMatrixCode n) (i : Fin 3) : PivotRowCode n :=
  fun j => complexRealDivCode (A i j)
    (nonnegativeSquareRootCode input epsilon O (A i i).re)

/-- H_jl = K_jl - conjugate(a_j) a_l, all in finite input syntax. -/
def schurRemainderCode (A : PivotMatrixCode n) (i : Fin 3) : PivotMatrixCode n :=
  let a := pivotRowCode input epsilon O A i
  fun j l => complexSubCode (A j l) (complexMul (complexConj (a j)) (a l))

theorem pivotRowCode_correct (A : PivotMatrixCode n) (i : Fin 3)
    (hi : 0 ≤ (pivotMatrixValue input epsilon O A i i).re) :
    pivotRowValue input epsilon O (pivotRowCode input epsilon O A i) =
      PivotedGram.pivotRow (pivotMatrixValue input epsilon O A) i := by
  funext j
  simp only [pivotRowValue,pivotRowCode,pivotComplexValue_realDiv]
  rw [nonnegativeSquareRootCode_correct input epsilon O (A i i).re hi]
  rfl

theorem schurRemainderCode_correct (A : PivotMatrixCode n) (i : Fin 3)
    (hi : 0 ≤ (pivotMatrixValue input epsilon O A i i).re) :
    pivotMatrixValue input epsilon O (schurRemainderCode input epsilon O A i) =
      PivotedGram.schurRemainder (pivotMatrixValue input epsilon O A) i := by
  have hr := pivotRowCode_correct input epsilon O A i hi
  funext j l
  change pivotComplexValue input epsilon O
    (complexSubCode (A j l) (complexMul
      (complexConj (pivotRowCode input epsilon O A i j))
      (pivotRowCode input epsilon O A i l))) = _
  rw [pivotComplexValue_sub,pivotComplexValue_mul,pivotComplexValue_conj]
  change pivotMatrixValue input epsilon O A j l -
    conj (pivotRowValue input epsilon O (pivotRowCode input epsilon O A i) j) *
      pivotRowValue input epsilon O (pivotRowCode input epsilon O A i) l = _
  rw [hr]
  rfl

#print axioms pivotMatrixZeroTest_correct
#print axioms schurRemainderCode_correct
end W3.FiniteInput
