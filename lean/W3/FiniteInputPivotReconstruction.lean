import W3.FiniteInputPivotArithmetic

/-! The complete finite-input Eq. (41) reconstruction. Its result retains the
finite scalar programs, selected root ordinals, first/second pivot indices, and
Schur zero-test result. Correctness identifies the interpreted result with the
previous literal semantic Eq. (41) algorithm on the entire physical domain. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace W3.FiniteInput
open W3.Infinitesimal W3.Weighted

/-- An inspectable execution trace containing only finite indices and code. -/
structure CodedPivotResult (n : Nat) where
  firstPivot : Fin 3
  firstRoot : Code n
  firstRow : PivotRowCode n
  remainder : PivotMatrixCode n
  remainderIsZero : Bool
  secondPivot : Option (Fin 3)
  secondRoot : Option (Code n)
  secondRow : PivotRowCode n

variable {F : Type*} [Field F] [CharZero F] [DecidableEq F] [Algebra F ℝ]
variable {n : Nat} (input : Fin 15 → F) (epsilon : Fin n → F)
    (O : RealRootEnumeration ℝ)

def CodedPivotResult.fields (r : CodedPivotResult n) : W3.Fields :=
  PivotedGram.rowFields (pivotRowValue input epsilon O r.firstRow)
    (pivotRowValue input epsilon O r.secondRow)

/-- The physical proof guarantees that every executed pivot search succeeds;
it supplies no scalar coefficients, roots, or root ordinals to the program. -/
def codedPivotAlgorithm (A : PivotMatrixCode n)
    (hA : W3.PhysicalGram (pivotMatrixValue input epsilon O A)) : CodedPivotResult n := by
  classical
  let K := pivotMatrixValue input epsilon O A
  let i := PivotedGram.positivePivot K (PivotedGram.physical_positive_pivot K hA)
  have hi : 0 < (K i i).re := PivotedGram.positivePivot_spec K _
  let a := pivotRowCode input epsilon O A i
  let H := schurRemainderCode input epsilon O A i
  have hH : pivotMatrixValue input epsilon O H = PivotedGram.schurRemainder K i :=
    schurRemainderCode_correct input epsilon O A i hi.le
  exact if hz : pivotMatrixZeroTest input epsilon O H = true then
    ⟨i,nonnegativeSquareRootCode input epsilon O (A i i).re,a,H,true,none,none,zeroPivotRow⟩
  else
    have hn : PivotedGram.schurRemainder K i ≠ 0 := by
      intro he
      apply hz
      apply (pivotMatrixZeroTest_correct input epsilon O H).mpr
      exact hH.trans he
    have hp : ∃ k, 0 < (pivotMatrixValue input epsilon O H k k).re := by
      rw [hH]
      exact PivotedGram.schur_positive_pivot K hA i hi hn
    let k := PivotedGram.positivePivot (pivotMatrixValue input epsilon O H) hp
    ⟨i,nonnegativeSquareRootCode input epsilon O (A i i).re,a,H,false,some k,
      some (nonnegativeSquareRootCode input epsilon O (H k k).re),
      pivotRowCode input epsilon O H k⟩

def codedPivotedFields (A : PivotMatrixCode n)
    (hA : W3.PhysicalGram (pivotMatrixValue input epsilon O A)) : W3.Fields :=
  (codedPivotAlgorithm input epsilon O A hA).fields input epsilon O

/-- Congruence keeps proof arguments out of the data path. -/
theorem pivotRow_positivePivot_congr {K L : PivotedGram.HermitianMatrix}
    (h : K = L) (hK : ∃ i, 0 < (K i i).re) (hL : ∃ i, 0 < (L i i).re) :
    PivotedGram.pivotRow K (PivotedGram.positivePivot K hK) =
      PivotedGram.pivotRow L (PivotedGram.positivePivot L hL) := by
  subst L
  rfl

/-- Exact agreement of reconstructed doublets, not merely existence of a Gram
factor. In particular both algorithms execute the same finite pivot order. -/
theorem codedPivotedFields_eq (A : PivotMatrixCode n)
    (hA : W3.PhysicalGram (pivotMatrixValue input epsilon O A)) :
    codedPivotedFields input epsilon O A hA =
      PivotedGram.pivotedFields (pivotMatrixValue input epsilon O A) hA := by
  classical
  let K := pivotMatrixValue input epsilon O A
  let i := PivotedGram.positivePivot K (PivotedGram.physical_positive_pivot K hA)
  have hi : 0 < (K i i).re := PivotedGram.positivePivot_spec K _
  have hr := pivotRowCode_correct input epsilon O A i hi.le
  have hH := schurRemainderCode_correct input epsilon O A i hi.le
  unfold codedPivotedFields codedPivotAlgorithm CodedPivotResult.fields
  dsimp only
  split_ifs with hz
  · have hs : PivotedGram.schurRemainder K i = 0 := by
      rw [← hH]
      exact (pivotMatrixZeroTest_correct input epsilon O _).mp hz
    simp only [pivotRowValue_zero]
    change PivotedGram.rowFields
      (pivotRowValue input epsilon O (pivotRowCode input epsilon O A i)) 0 = _
    rw [hr]
    simp only [PivotedGram.pivotedFields]
    rw [dif_pos hs]
  · have hs : PivotedGram.schurRemainder K i ≠ 0 := by
      intro he
      apply hz
      apply (pivotMatrixZeroTest_correct input epsilon O _).mpr
      exact hH.trans he
    have hk := PivotedGram.positivePivot_spec
      (pivotMatrixValue input epsilon O (schurRemainderCode input epsilon O A i))
      (by rw [hH]; exact PivotedGram.schur_positive_pivot K hA i hi hs)
    rw [pivotRowCode_correct input epsilon O A i hi.le]
    rw [pivotRowCode_correct input epsilon O _ _ hk.le]
    simp only [PivotedGram.pivotedFields]
    rw [dif_neg hs]
    congr 1
    exact pivotRow_positivePivot_congr hH _ _

/-- Full normalized physical-domain correctness, including rank-one matrices
and zero original leading diagonals. -/
theorem codedPivotedFields_gram (A : PivotMatrixCode n)
    (hA : W3.PhysicalGram (pivotMatrixValue input epsilon O A)) :
    W3.gram (codedPivotedFields input epsilon O A hA) = pivotMatrixValue input epsilon O A := by
  rw [codedPivotedFields_eq]
  exact PivotedGram.pivotedFields_gram _ hA

theorem codedPivotedFields_normalized (A : PivotMatrixCode n)
    (hA : W3.PhysicalGram (pivotMatrixValue input epsilon O A)) :
    ‖codedPivotedFields input epsilon O A hA‖ = 1 := by
  rw [codedPivotedFields_eq]
  exact PivotedGram.pivotedFields_normalized _ hA

theorem codedPivotedFields_value (k : W3.Couplings) (A : PivotMatrixCode n)
    (hA : W3.PhysicalGram (pivotMatrixValue input epsilon O A)) :
    W3.quartic k (codedPivotedFields input epsilon O A hA) =
      W3.gramQuartic k (pivotMatrixValue input epsilon O A) := by
  rw [codedPivotedFields_eq]
  exact PivotedGram.pivotedFields_value _ _ hA

#print axioms codedPivotAlgorithm
#print axioms codedPivotedFields_eq
#print axioms codedPivotedFields_gram
#print axioms codedPivotedFields_normalized
#print axioms codedPivotedFields_value
end W3.FiniteInput
