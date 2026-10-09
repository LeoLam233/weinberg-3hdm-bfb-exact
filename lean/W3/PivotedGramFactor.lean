import W3.GramSemantics

/-! The literal finite pivot-and-square-root Gram-factor algorithm from equation (41).
The algorithm contains only finite pivot selection, square roots, arithmetic,
and a zero test. Spectral factorization is used solely to prove its correctness. -/
set_option maxHeartbeats 1000000
noncomputable section
namespace W3.PivotedGram
open Matrix ComplexConjugate
open scoped BigOperators ComplexOrder

abbrev HermitianMatrix := Matrix (Fin 3) (Fin 3) ℂ

def rowGram (a : Fin 3 → ℂ) : HermitianMatrix := fun j l=>conj (a j)*a l

def twoRowGram (u v : Fin 3 → ℂ) : HermitianMatrix := rowGram u+rowGram v

def rowFields (a b : Fin 3 → ℂ) : W3.Fields :=
  WithLp.toLp 2 (fun p=>if p.1=0 then a p.2 else b p.2)

@[simp] theorem gram_rowFields (a b : Fin 3 → ℂ) :
    W3.gram (rowFields a b)=twoRowGram a b := by
  ext i j
  simp [W3.gram,rowFields,twoRowGram,rowGram,Fin.sum_univ_two]

@[simp] theorem rowGram_diag (a : Fin 3 → ℂ) (i : Fin 3) :
    (rowGram a i i).re=Complex.normSq (a i) := by
  simp [rowGram,Complex.normSq]

/-- A finite sign-tested pivot, chosen from the explicit three-entry list. -/
def positivePivot (K : HermitianMatrix) (h : ∃ i,0<(K i i).re) : Fin 3 := by
  classical
  exact (Finset.univ.filter (fun i=>0<(K i i).re)).min' (by
    obtain ⟨i,hi⟩ := h
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩)

theorem positivePivot_spec (K : HermitianMatrix) (h : ∃ i,0<(K i i).re) :
    0<(K (positivePivot K h) (positivePivot K h)).re := by
  classical
  unfold positivePivot
  exact (Finset.mem_filter.mp (Finset.min'_mem (Finset.univ.filter (fun i : Fin 3=>0<(K i i).re)) _)).2

/-- The displayed first-row formula a_j = K_ij / sqrt(K_ii). -/
def pivotRow (K : HermitianMatrix) (i : Fin 3) : Fin 3 → ℂ :=
  fun j=>K i j/(Real.sqrt (K i i).re : ℂ)

def schurRemainder (K : HermitianMatrix) (i : Fin 3) : HermitianMatrix :=
  K-rowGram (pivotRow K i)

lemma two_row_lagrange (a b u v w z : ℂ) :
    conj (conj a*u+conj b*v)*(conj a*w+conj b*z)+
      conj (-b*u+a*v)*(-b*w+a*z)=
    ((Complex.normSq a+Complex.normSq b : ℝ) : ℂ)*(conj u*w+conj v*z) := by
  apply Complex.ext <;> simp [Complex.normSq] <;> ring

lemma divided_two_row_lagrange (a b u v w z : ℂ) (d : ℝ) (hd : d≠0)
    (hsq : d^2=Complex.normSq a+Complex.normSq b) :
    conj ((conj a*u+conj b*v)/(d:ℂ))*((conj a*w+conj b*z)/(d:ℂ))+
      conj ((-b*u+a*v)/(d:ℂ))*((-b*w+a*z)/(d:ℂ))=conj u*w+conj v*z := by
  have hdC : (d:ℂ)≠0 := by exact_mod_cast hd
  have hsqC : (d:ℂ)^2=((Complex.normSq a+Complex.normSq b : ℝ):ℂ) := by exact_mod_cast hsq
  simp only [map_div₀,Complex.conj_ofReal]
  calc
    _ = (conj (conj a*u+conj b*v)*(conj a*w+conj b*z)+
      conj (-b*u+a*v)*(-b*w+a*z))/(d:ℂ)^2 := by field_simp
    _ = ((d:ℂ)^2*(conj u*w+conj v*z))/(d:ℂ)^2 := by rw [two_row_lagrange,hsqC]
    _ = _ := by field_simp

/-- The explicit two-row rotation is used only as a correctness certificate for the remainder. -/
def rotatedSecond (K : HermitianMatrix) (u v : Fin 3 → ℂ) (i : Fin 3) : Fin 3 → ℂ :=
  fun j=>(-v i*u j+u i*v j)/(Real.sqrt (K i i).re : ℂ)

theorem schurRemainder_single_row (K : HermitianMatrix) (u v : Fin 3 → ℂ)
    (hK : K=twoRowGram u v) (i : Fin 3) (hi : 0<(K i i).re) :
    schurRemainder K i=rowGram (rotatedSecond K u v i) := by
  have hd : Real.sqrt (K i i).re≠0 := (Real.sqrt_pos.mpr hi).ne'
  have hr : (K i i).re=Complex.normSq (u i)+Complex.normSq (v i) := by
    rw [hK]
    simp [twoRowGram,rowGram,Complex.normSq]
  have hsq : (Real.sqrt (K i i).re)^2=Complex.normSq (u i)+Complex.normSq (v i) :=
    (Real.sq_sqrt hi.le).trans hr
  ext j l
  have he := divided_two_row_lagrange (u i) (v i) (u j) (v j) (u l) (v l)
    (Real.sqrt (K i i).re) hd hsq
  change K j l-conj (K i j/(Real.sqrt (K i i).re:ℂ))*(K i l/(Real.sqrt (K i i).re:ℂ))=
    conj ((-v i*u j+u i*v j)/(Real.sqrt (K i i).re:ℂ))*
      ((-v i*u l+u i*v l)/(Real.sqrt (K i i).re:ℂ))
  have heq (a b : Fin 3) : K a b=conj (u a)*u b+conj (v a)*v b := congrFun (congrFun hK a) b
  rw [heq j l,heq i j,heq i l]
  linear_combination -he

/-- A nonzero one-row Gram matrix always has a positive diagonal pivot. -/
theorem rowGram_positive_pivot (b : Fin 3 → ℂ) (h : rowGram b≠0) :
    ∃ k,0<(rowGram b k k).re := by
  by_contra hn
  push Not at hn
  apply h
  have hb : ∀ i,b i=0 := by
    intro i
    have hi := hn i
    rw [rowGram_diag] at hi
    exact Complex.normSq_eq_zero.mp (le_antisymm hi (Complex.normSq_nonneg _))
  ext i j
  simp [rowGram,hb]

/-- The displayed second pivot recovers any one-row Gram matrix exactly. -/
theorem pivotRow_rowGram (b : Fin 3 → ℂ) (k : Fin 3) (hk : 0<(rowGram b k k).re) :
    rowGram (pivotRow (rowGram b) k)=rowGram b := by
  have hd : Real.sqrt (rowGram b k k).re≠0 := (Real.sqrt_pos.mpr hk).ne'
  have hsq : (Real.sqrt (rowGram b k k).re)^2=Complex.normSq (b k)+Complex.normSq (0:ℂ) := by
    rw [Real.sq_sqrt hk.le,rowGram_diag]
    simp
  ext j l
  have he := divided_two_row_lagrange (b k) 0 (b j) 0 (b l) 0
    (Real.sqrt (rowGram b k k).re) hd hsq
  simpa [rowGram,pivotRow] using he

lemma physical_positive_pivot (K : HermitianMatrix) (hK : W3.PhysicalGram K) :
    ∃ i,0<(K i i).re := by
  by_contra h
  push Not at h
  have ht := congrArg Complex.re hK.2.2.1
  simp [Matrix.trace,Fin.sum_univ_three] at ht
  linarith [h 0,h 1,h 2]

/-- The first remainder of a physical rank-at-most-two matrix is either zero or has a positive pivot. -/
theorem schur_positive_pivot (K : HermitianMatrix) (hK : W3.PhysicalGram K)
    (i : Fin 3) (hi : 0<(K i i).re) (hH : schurRemainder K i≠0) :
    ∃ k,0<(schurRemainder K i k k).re := by
  obtain ⟨phi,_,hphi⟩ := (W3.physicalGram_iff_fields K).mp hK
  have he : K=twoRowGram (fun j=>phi (0,j)) (fun j=>phi (1,j)) := by
    rw [← hphi]
    ext j l
    simp [W3.gram,twoRowGram,rowGram,Fin.sum_univ_two]
  rw [schurRemainder_single_row K _ _ he i hi] at hH ⊢
  exact rowGram_positive_pivot _ hH

/-- Correctness of the second-row branch, proved from the original physical-domain hypotheses. -/
theorem schur_pivot_reconstructs (K : HermitianMatrix) (hK : W3.PhysicalGram K)
    (i : Fin 3) (hi : 0<(K i i).re) (k : Fin 3) (hk : 0<(schurRemainder K i k k).re) :
    rowGram (pivotRow (schurRemainder K i) k)=schurRemainder K i := by
  obtain ⟨phi,_,hphi⟩ := (W3.physicalGram_iff_fields K).mp hK
  have he : K=twoRowGram (fun j=>phi (0,j)) (fun j=>phi (1,j)) := by
    rw [← hphi]
    ext j l
    simp [W3.gram,twoRowGram,rowGram,Fin.sum_univ_two]
  rw [schurRemainder_single_row K _ _ he i hi] at hk ⊢
  exact pivotRow_rowGram _ k hk

/-- Literal equation (41), with at most two finite pivot searches and two square roots. -/
def pivotedFields (K : HermitianMatrix) (hK : W3.PhysicalGram K) : W3.Fields := by
  classical
  let i := positivePivot K (physical_positive_pivot K hK)
  let a := pivotRow K i
  let H := schurRemainder K i
  exact if hH : H=0 then rowFields a 0 else
    let k := positivePivot H (schur_positive_pivot K hK i (positivePivot_spec K _) hH)
    rowFields a (pivotRow H k)

theorem pivotedFields_gram (K : HermitianMatrix) (hK : W3.PhysicalGram K) :
    W3.gram (pivotedFields K hK)=K := by
  classical
  unfold pivotedFields
  dsimp only
  split_ifs with hH
  · rw [gram_rowFields]
    have he : rowGram (pivotRow K (positivePivot K (physical_positive_pivot K hK)))=K := by
      exact (sub_eq_zero.mp hH).symm
    rw [twoRowGram,he]
    have hz : rowGram (0 : Fin 3 → ℂ)=0 := by ext i j; simp [rowGram]
    rw [hz,add_zero]
  · rw [gram_rowFields,twoRowGram,schur_pivot_reconstructs K hK _ (positivePivot_spec K _) _ (positivePivot_spec _ _)]
    unfold schurRemainder
    abel

theorem pivotedFields_normalized (K : HermitianMatrix) (hK : W3.PhysicalGram K) :
    ‖pivotedFields K hK‖=1 := by
  have ht := W3.gram_trace (pivotedFields K hK)
  rw [pivotedFields_gram, hK.2.2.1] at ht
  have hn : ‖pivotedFields K hK‖^2=1 := by exact_mod_cast ht.symm
  nlinarith [norm_nonneg (pivotedFields K hK)]

/-- The literal pivot algorithm preserves the original quartic value. -/
theorem pivotedFields_value (k : W3.Couplings) (K : HermitianMatrix) (hK : W3.PhysicalGram K) :
    W3.quartic k (pivotedFields K hK)=W3.gramQuartic k K := by
  rw [← W3.gramQuartic_gram,pivotedFields_gram]

/-- Applying the finite pivot algorithm to a minimizing residue recovers its minimizing doublets. -/
theorem pivotedFields_minimizing (k : W3.RealModel.Parameters ℝ)
    (K : HermitianMatrix) (hK : W3.PhysicalGram K)
    (hmin : W3.gramQuartic (W3.RealModel.couplings k) K=W3.Infinitesimal.realMinimum k) :
    ‖pivotedFields K hK‖=1 ∧
      W3.quartic (W3.RealModel.couplings k) (pivotedFields K hK)=W3.Infinitesimal.realMinimum k :=
  ⟨pivotedFields_normalized K hK,(pivotedFields_value _ K hK).trans hmin⟩

#print axioms pivotedFields_minimizing
#print axioms pivotedFields_gram
#print axioms pivotedFields_normalized
end W3.PivotedGram
