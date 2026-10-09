import W3.TransferOperatorEnergy
import W3.ActualWitness
import W3.InfinitesimalSuccessiveResidue

/-! Bounded physical matrices, their entrywise residues, and exact minimizing witnesses. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace W3.TransferOperator
open W3.StrataTransfer W3.RealModel W3.Infinitesimal ArchimedeanClass

section OrderedBounds
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def MatrixBounded (y : HermitianCoordinates K) : Prop := ∀ i,-1≤y i ∧ y i≤1

lemma offRe_bounds_one (x : RealFields K) (hx : mass x=1) (i : Fin 3) :
    -1≤offRe x i ∧ offRe x i≤1 := by
  have h := off_norm_le_quarter x hx i
  constructor <;> nlinarith [sq_nonneg (offIm x i),sq_nonneg (offRe x i-1),sq_nonneg (offRe x i+1)]

lemma offIm_bounds_one (x : RealFields K) (hx : mass x=1) (i : Fin 3) :
    -1≤offIm x i ∧ offIm x i≤1 := by
  have h := off_norm_le_quarter x hx i
  constructor <;> nlinarith [sq_nonneg (offRe x i),sq_nonneg (offIm x i-1),sq_nonneg (offIm x i+1)]

theorem gramCoordinates_bounded (x : RealFields K) (hx : mass x=1) :
    MatrixBounded (gramCoordinates x) := by
  intro i
  fin_cases i
  · exact ⟨(by change -1≤radii x 0; linarith [radii_nonneg x 0]),radii_le_one x hx 0⟩
  · exact ⟨(by change -1≤radii x 1; linarith [radii_nonneg x 1]),radii_le_one x hx 1⟩
  · exact ⟨(by change -1≤radii x 2; linarith [radii_nonneg x 2]),radii_le_one x hx 2⟩
  · exact offRe_bounds_one x hx 0
  · exact offIm_bounds_one x hx 0
  · exact offRe_bounds_one x hx 1
  · exact offIm_bounds_one x hx 1
  · exact offRe_bounds_one x hx 2
  · exact offIm_bounds_one x hx 2

theorem gramMatches_bounded {x : RealFields K} {y : HermitianCoordinates K}
    (hx : mass x=1) (hgram : GramMatches x y) : MatrixBounded y := by
  rw [← (gramMatches_iff x y).mp hgram]
  exact gramCoordinates_bounded x hx

end OrderedBounds

@[simp] theorem map_gramCoordinates {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (x : RealFields K) (i : Fin 9) :
    f (gramCoordinates x i)=gramCoordinates (fun j=>f (x j)) i := by
  fin_cases i <;> simp [gramCoordinates,radii,offRe,offIm]

/-- Every physically retained normalized matrix is bounded by real constants. -/
theorem sixteen_physical_matrix_bounded (y : HermitianCoordinates SixteenLevelField)
    (z : RealVector SixteenLevelField) (hn : NormalizedKernel y z) (hp : hermitianPurity y≤1) :
    MatrixBounded y := by
  obtain ⟨x,hx,hgram⟩ := (sixteen_physical_equivalence y z hn).mp hp
  exact gramMatches_bounded hx hgram

/-- The actual finite-element representation of each of the nine matrix coordinates. -/
def finiteMatrix9 (y : HermitianCoordinates SixteenLevelField) (hy : MatrixBounded y) :
    HermitianCoordinates Finite16 := fun i=>
  boundedElement realEmbedding16 (y i) (a := (-1 : ℝ)) (b := (1 : ℝ))
    (by rw [map_neg,map_one]; exact (hy i).1)
    (by rw [map_one]; exact (hy i).2)

@[simp] theorem finiteMatrix9_value (y : HermitianCoordinates SixteenLevelField) (hy : MatrixBounded y) (i : Fin 9) :
    finiteValue (finiteMatrix9 y hy i)=y i := rfl

def residueMatrix9 (y : HermitianCoordinates SixteenLevelField) (hy : MatrixBounded y) :
    HermitianCoordinates ℝ := fun i=>realResidue (finiteMatrix9 y hy i)

@[simp] theorem residueMatrix9_eq_stdPart (y : HermitianCoordinates SixteenLevelField) (hy : MatrixBounded y) (i : Fin 9) :
    residueMatrix9 y hy i=ArchimedeanClass.stdPart (y i) := by
  exact realResidue_eq_stdPart (finiteMatrix9 y hy i)

/-- The finite matrix equals the Gram polynomial evaluated on the finite field coordinates. -/
theorem finiteMatrix9_eq_gram (y : HermitianCoordinates SixteenLevelField) (hy : MatrixBounded y)
    (x : RealFields SixteenLevelField) (hx : mass x=1) (hgram : GramMatches x y) :
    finiteMatrix9 y hy=gramCoordinates (finitePoint x hx) := by
  funext i
  apply FiniteElement.ext
  change finiteValue (finiteMatrix9 y hy i)=finiteValue (gramCoordinates (finitePoint x hx) i)
  rw [finiteMatrix9_value,map_gramCoordinates]
  simp only [finitePoint_value]
  exact congrFun ((gramMatches_iff x y).mp hgram).symm i

/-- Entrywise matrix residue is independent of the chosen Gram factor. -/
theorem residueMatrix9_eq_gram (y : HermitianCoordinates SixteenLevelField) (hy : MatrixBounded y)
    (x : RealFields SixteenLevelField) (hx : mass x=1) (hgram : GramMatches x y) :
    residueMatrix9 y hy=gramCoordinates (residuePoint x hx) := by
  funext i
  change realResidue (finiteMatrix9 y hy i)=gramCoordinates (residuePoint x hx) i
  rw [finiteMatrix9_eq_gram y hy x hx hgram]
  exact map_gramCoordinates (realResidue (L := SixteenLevelField)).toRingHom (finitePoint x hx) i

/-- Every normalized Gram matrix minimizing the deformed quartic has the exact physical real residue. -/
theorem minimizing_matrix_residue (k : Parameters ℝ)
    (y : HermitianCoordinates SixteenLevelField) (hy : MatrixBounded y)
    (hphysical : ∃ x : RealFields SixteenLevelField,mass x=1 ∧ GramMatches x y)
    (hv : hermitianEnergy (actualParameters k) y/2=deformedMinimum k) :
    hermitianTrace (residueMatrix9 y hy)=1 ∧
      hermitianEnergy k (residueMatrix9 y hy)/2=realMinimum k ∧
      ∃ phi : W3.Fields, ‖phi‖=1 ∧
        complexMatrix (hermitianRe (residueMatrix9 y hy)) (hermitianIm (residueMatrix9 y hy))=W3.gram phi ∧
        W3.quartic (couplings k) phi=realMinimum k := by
  obtain ⟨x,hx,hgram⟩ := hphysical
  have hxv : quarticReal (actualParameters k) x=deformedMinimum k := by
    rw [quarticReal,gramMatches_energy (actualParameters k) hgram]
    exact hv
  obtain ⟨hresmass,hresvalue⟩ := residuePoint_minimizing k x hx hxv
  have hres := residueMatrix9_eq_gram y hy x hx hgram
  have henergy : hermitianEnergy k (residueMatrix9 y hy)/2=realMinimum k := by
    rw [hres,hermitianEnergy_gramCoordinates]
    exact hresvalue
  refine ⟨?_,henergy,fields (residuePoint x hx),?_,?_,?_⟩
  · rw [hres,hermitianTrace_gramCoordinates]
    exact hresmass
  · rw [mass_fields] at hresmass
    nlinarith [norm_nonneg (fields (residuePoint x hx))]
  · rw [hres,hermitianRe_gramCoordinates,hermitianIm_gramCoordinates,complex_gram]
  · rw [quarticReal_fields] at hresvalue
    exact hresvalue

/-- The charged physical filter supplies the Gram premise and all bounds above. -/
theorem physical_minimizing_matrix_residue (k : Parameters ℝ)
    (y : HermitianCoordinates SixteenLevelField) (z : RealVector SixteenLevelField)
    (hn : NormalizedKernel y z) (hp : hermitianPurity y≤1)
    (hv : hermitianEnergy (actualParameters k) y/2=deformedMinimum k) :
    let hy := sixteen_physical_matrix_bounded y z hn hp
    hermitianTrace (residueMatrix9 y hy)=1 ∧
      hermitianEnergy k (residueMatrix9 y hy)/2=realMinimum k ∧
      ∃ phi : W3.Fields, ‖phi‖=1 ∧
        complexMatrix (hermitianRe (residueMatrix9 y hy)) (hermitianIm (residueMatrix9 y hy))=W3.gram phi ∧
        W3.quartic (couplings k) phi=realMinimum k := by
  exact minimizing_matrix_residue k y (sixteen_physical_matrix_bounded y z hn hp)
    ((sixteen_physical_equivalence y z hn).mp hp) hv

/-- If a successive extraction is given, its endpoint is the same canonical matrix residue. -/
theorem successive_matrix_residue_eq (y : HermitianCoordinates SixteenLevelField) (hy : MatrixBounded y)
    (r : HermitianCoordinates ℝ) (hr : ∀ i,SuccessiveResidue 16 (y i) (r i)) :
    residueMatrix9 y hy=r := by
  funext i
  rw [residueMatrix9_eq_stdPart]
  exact successiveResidue_eq_stdPart 16 (hr i)

/-- The selected algebraic nine coordinates have an actual sixteen-step residue chain. -/
theorem matrix_successiveResidue (y : HermitianCoordinates SixteenLevelField) (hy : MatrixBounded y)
    (halg : letI := rationalTowerAlgebra 16; ∀ i,IsAlgebraic (RationalTower 16) (y i)) :
    ∀ i,SuccessiveResidue 16 (y i) (residueMatrix9 y hy i) := by
  intro i
  obtain ⟨r,_,_,hr⟩ := successiveResidue_exists 16
    (a := (-1 : ℝ)) (b := (1 : ℝ))
    (by change realEmbedding16 (-1)≤y i; simpa using (hy i).1)
    (by change y i≤realEmbedding16 1; simpa using (hy i).2) (halg i)
  have he : residueMatrix9 y hy i=r := by
    rw [residueMatrix9_eq_stdPart]
    exact successiveResidue_eq_stdPart 16 hr
  rwa [he]

/-- Final matrix witness interface: finite successive extraction and physical original minimum. -/
theorem minimizing_matrix_successive_residue (k : Parameters ℝ)
    (y : HermitianCoordinates SixteenLevelField)
    (hphysical : ∃ x : RealFields SixteenLevelField,mass x=1 ∧ GramMatches x y)
    (hv : hermitianEnergy (actualParameters k) y/2=deformedMinimum k)
    (halg : letI := rationalTowerAlgebra 16; ∀ i,IsAlgebraic (RationalTower 16) (y i)) :
    ∃ r : HermitianCoordinates ℝ,
      (∀ i,SuccessiveResidue 16 (y i) (r i)) ∧ hermitianTrace r=1 ∧
      hermitianEnergy k r/2=realMinimum k ∧
      ∃ phi : W3.Fields, ‖phi‖=1 ∧ complexMatrix (hermitianRe r) (hermitianIm r)=W3.gram phi ∧
        W3.quartic (couplings k) phi=realMinimum k := by
  obtain ⟨x,hx,hgram⟩ := hphysical
  let hy := gramMatches_bounded hx hgram
  refine ⟨residueMatrix9 y hy,matrix_successiveResidue y hy halg,?_⟩
  exact minimizing_matrix_residue k y hy ⟨x,hx,hgram⟩ hv

#print axioms minimizing_matrix_successive_residue
#print axioms gramCoordinates_bounded
#print axioms residueMatrix9_eq_gram
#print axioms physical_minimizing_matrix_residue
#print axioms matrix_successiveResidue
end W3.TransferOperator
