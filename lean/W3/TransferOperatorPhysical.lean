import W3.StrataTransfer
import W3.GramFactor
import W3.OperatorPhysical

noncomputable section
namespace W3.TransferOperator
open W3.StrataTransfer W3.RealModel W3.Infinitesimal W3.Operator Matrix
open OrderedPolynomialFormula
open scoped BigOperators ComplexOrder

abbrev HermitianCoordinates (K : Type*) := Fin 9 → K

section PhysicalModel
variable {K : Type*} [CommRing K]

def hermitianRe (y : HermitianCoordinates K) : RealMatrix K :=
  !![y 0,y 3,y 5; y 3,y 1,y 7; y 5,y 7,y 2]
def hermitianIm (y : HermitianCoordinates K) : RealMatrix K :=
  !![0,y 4,y 6; -y 4,0,y 8; -y 6,-y 8,0]
def hermitianTrace (y : HermitianCoordinates K) : K := y 0+y 1+y 2
def hermitianPurity (y : HermitianCoordinates K) : K :=
  (y 0)^2+(y 1)^2+(y 2)^2+2*((y 3)^2+(y 4)^2+(y 5)^2+(y 6)^2+(y 7)^2+(y 8)^2)

def GramMatches (x : RealFields K) (y : HermitianCoordinates K) : Prop :=
  ∀ i j,gramRe x i j=hermitianRe y i j ∧ gramIm x i j=hermitianIm y i j

def NormalizedKernel (y : HermitianCoordinates K) (z : RealVector K) : Prop :=
  hermitianTrace y=1 ∧ zMass z=1 ∧
    ∀ i,actionRe (hermitianRe y) (hermitianIm y) z i=0 ∧
      actionIm (hermitianRe y) (hermitianIm y) z i=0

end PhysicalModel

section Natural
variable {K L : Type*} [CommRing K] [CommRing L]
@[simp] theorem map_hermitianRe (f : K →+* L) (y : HermitianCoordinates K) (i j : Fin 3) :
    f (hermitianRe y i j)=hermitianRe (fun a=>f (y a)) i j := by
  fin_cases i <;> fin_cases j <;> rfl
@[simp] theorem map_hermitianIm (f : K →+* L) (y : HermitianCoordinates K) (i j : Fin 3) :
    f (hermitianIm y i j)=hermitianIm (fun a=>f (y a)) i j := by
  fin_cases i <;> fin_cases j <;> simp [hermitianIm]
@[simp] theorem map_hermitianTrace (f : K →+* L) (y : HermitianCoordinates K) :
    f (hermitianTrace y)=hermitianTrace (fun a=>f (y a)) := by simp [hermitianTrace]
@[simp] theorem map_hermitianPurity (f : K →+* L) (y : HermitianCoordinates K) :
    f (hermitianPurity y)=hermitianPurity (fun a=>f (y a)) := by simp [hermitianPurity,map_ofNat]
end Natural

def complexCoordinates (y : HermitianCoordinates ℝ) : Coordinates :=
  (![y 0,y 1,y 2],![⟨y 3,y 4⟩,⟨y 5,y 6⟩,⟨y 7,y 8⟩])

theorem complexMatrix_hermitianCoordinates (y : HermitianCoordinates ℝ) :
    complexMatrix (hermitianRe y) (hermitianIm y)=coordinateMatrix (complexCoordinates y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [complexMatrix,hermitianRe,hermitianIm,coordinateMatrix,complexCoordinates]

theorem hermitianTrace_complex (y : HermitianCoordinates ℝ) :
    (complexMatrix (hermitianRe y) (hermitianIm y)).trace=((hermitianTrace y : ℝ) : ℂ) := by
  simp [Matrix.trace,complexMatrix,hermitianRe,hermitianIm,hermitianTrace,Fin.sum_univ_three]
  apply Complex.ext <;> simp

theorem hermitianPurity_complex (y : HermitianCoordinates ℝ) :
    ((complexMatrix (hermitianRe y) (hermitianIm y)) *
      (complexMatrix (hermitianRe y) (hermitianIm y))).trace.re=hermitianPurity y := by
  rw [complexMatrix_hermitianCoordinates,← coordinatePair_eq_trace]
  simp [coordinatePair,complexCoordinates,hermitianPurity,Fin.sum_univ_three]
  ring

/-- Real spectral/Gram-factor theorem expressed entirely in polynomial real coordinates. -/
theorem real_physical_equivalence (y : HermitianCoordinates ℝ) (z : RealVector ℝ)
    (hn : NormalizedKernel y z) :
    hermitianPurity y≤1 ↔ ∃ x : RealFields ℝ,mass x=1 ∧ GramMatches x y := by
  obtain ⟨ht,hz,hker⟩ := hn
  have hH : (complexMatrix (hermitianRe y) (hermitianIm y)).IsHermitian := by
    rw [complexMatrix_hermitianCoordinates]
    exact coordinateMatrix_hermitian _
  have htr : (complexMatrix (hermitianRe y) (hermitianIm y)).trace=1 := by
    rw [hermitianTrace_complex,ht]
    norm_num
  have hZ : complexVector z ≠ 0 := by
    intro hzero
    rw [← complex_norm,hzero] at hz
    simp at hz
  have hK : complexMatrix (hermitianRe y) (hermitianIm y) *ᵥ complexVector z=0 := by
    funext i
    rw [complex_action]
    apply Complex.ext <;> simp [(hker i).1,(hker i).2]
  have hf := physical_filter_of_kernel _ hH htr _ hZ hK
  rw [hermitianPurity_complex] at hf
  constructor
  · intro hp
    have hpos := hf.mpr hp
    have hdet : (complexMatrix (hermitianRe y) (hermitianIm y)).det=0 := by
      by_contra hdet
      apply hZ
      exact (Matrix.mulVec_injective_of_det_ne_zero hdet) (by simpa using hK)
    obtain ⟨phi,hgram,hnorm⟩ := W3.exists_normalized_gram_factor _ hpos hdet htr
    refine ⟨coordinates phi,by simp [mass_coordinates,hnorm],?_⟩
    have hm : complexMatrix (gramRe (coordinates phi)) (gramIm (coordinates phi))=
        complexMatrix (hermitianRe y) (hermitianIm y) := by
      rw [complex_gram,fields_coordinates]
      exact hgram
    intro i j
    exact ⟨congrArg (fun M=>(M i j).re) hm,congrArg (fun M=>(M i j).im) hm⟩
  · rintro ⟨x,_,hx⟩
    apply hf.mp
    have hm : complexMatrix (hermitianRe y) (hermitianIm y)=W3.gram (fields x) := by
      rw [← complex_gram]
      ext i j
      apply Complex.ext
      · exact (hx i j).1.symm
      · exact (hx i j).2.symm
    rw [hm]
    exact W3.gram_posSemidef _

/-- Encoded equivalence, built from the actual syntax's implications. -/
def iffFormula {n : ℕ} (p q : Formula n) : Formula n :=
  .conj (p.implies q) (q.implies p)

@[simp] theorem realize_iffFormula {K : Type*} [CommRing K] [LE K] {n : ℕ}
    (p q : Formula n) (v : Fin n → K) :
    (iffFormula p q).Realize v ↔ (p.Realize v ↔ q.Realize v) := by
  simp [iffFormula,Realize,realize_implies,iff_def]

def coordinates15 {K : Type*} (v : Fin 15 → K) : HermitianCoordinates K := fun i=>v (Fin.castAdd 6 i)
def vector15 {K : Type*} (v : Fin 15 → K) : RealVector K := fun i=>v (Fin.natAdd 9 i)

def kernelFormula {n : ℕ} (y : HermitianCoordinates (Poly n)) (z : RealVector (Poly n)) : Formula n :=
  .conj (.eqZero (hermitianTrace y-1))
    (.conj (.eqZero (zMass z-1))
      (allFin 3 (fun i=>.conj (.eqZero (actionRe (hermitianRe y) (hermitianIm y) z i))
        (.eqZero (actionIm (hermitianRe y) (hermitianIm y) z i)))))

def gramWitnessFormula {n : ℕ} (x : RealFields (Poly n)) (y : HermitianCoordinates (Poly n)) : Formula n :=
  .conj (.eqZero (mass x-1)) (allFin 3 (fun i=>allFin 3 (fun j=>
    .conj (.eqZero (gramRe x i j-hermitianRe y i j)) (.eqZero (gramIm x i j-hermitianIm y i j)))))

def gramWitnessBody : Formula (15+12) :=
  let v : Fin 15 → Poly (15+12) := fun i=>MvPolynomial.X (backIndex 15 12 i)
  let x : RealFields (Poly (15+12)) := fun i=>MvPolynomial.X (frontIndex 15 12 i)
  gramWitnessFormula x (coordinates15 v)

def physicalFormula : Formula 15 :=
  (kernelFormula (coordinates15 MvPolynomial.X) (vector15 MvPolynomial.X)).implies
    (iffFormula (.nonneg (1-hermitianPurity (coordinates15 MvPolynomial.X))) (exVec 12 gramWitnessBody))

section FormulaSemantics
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem kernelFormula_realize {n : ℕ} (y : HermitianCoordinates (Poly n)) (z : RealVector (Poly n)) (v : Fin n → K) :
    (kernelFormula y z).Realize v ↔
      NormalizedKernel (fun i=>intPolynomialEval (y i) v) (fun i=>intPolynomialEval (z i) v) := by
  simp only [kernelFormula,Realize,realize_allFin,NormalizedKernel,intPolynomialEval,
    map_sub,map_one,map_zMass,map_hermitianTrace,map_actionRe,map_actionIm,
    map_hermitianRe,map_hermitianIm,sub_eq_zero]

theorem gramWitnessFormula_realize {n : ℕ} (x : RealFields (Poly n)) (y : HermitianCoordinates (Poly n)) (v : Fin n → K) :
    (gramWitnessFormula x y).Realize v ↔
      mass (fun i=>intPolynomialEval (x i) v)=1 ∧
        GramMatches (fun i=>intPolynomialEval (x i) v) (fun i=>intPolynomialEval (y i) v) := by
  simp only [gramWitnessFormula,Realize,realize_allFin,GramMatches,intPolynomialEval,
    map_sub,map_one,map_mass,map_gramRe,map_gramIm,map_hermitianRe,map_hermitianIm,sub_eq_zero]

@[simp] theorem gramWitnessBody_realize (v : Fin 15 → K) (x : RealFields K) :
    gramWitnessBody.Realize (extendVec v x) ↔ mass x=1 ∧ GramMatches x (coordinates15 v) := by
  rw [gramWitnessBody,gramWitnessFormula_realize]
  simp [intPolynomialEval,coordinates15]
  intro _
  rfl

theorem physicalFormula_realize (v : Fin 15 → K) :
    physicalFormula.Realize v ↔
      (NormalizedKernel (coordinates15 v) (vector15 v) →
        (hermitianPurity (coordinates15 v)≤1 ↔ ∃ x : RealFields K,mass x=1 ∧ GramMatches x (coordinates15 v))) := by
  simp [physicalFormula,realize_implies,realize_iffFormula,kernelFormula_realize,
    realize_exVec,Realize,intPolynomialEval,map_sub,map_one,coordinates15,vector15,sub_nonneg] <;> rfl

end FormulaSemantics

theorem real_physicalFormula (v : Fin 15 → ℝ) : physicalFormula.Realize v := by
  apply (physicalFormula_realize v).mpr
  exact real_physical_equivalence _ _

/-- Exact nonarchimedean purity filter and two-row Gram witness, genuinely transferred. -/
theorem tower_physical_equivalence (n : ℕ) (y : HermitianCoordinates (Tower realModel n))
    (z : RealVector (Tower realModel n)) (hn : NormalizedKernel y z) :
    hermitianPurity y≤1 ↔ ∃ x : RealFields (Tower realModel n),mass x=1 ∧ GramMatches x y := by
  have h := (physicalFormula_realize (Fin.append y z)).mp
    (orderedPolynomialFormula_universal_tower realModel n physicalFormula real_physicalFormula (Fin.append y z))
  have hy : coordinates15 (Fin.append y z)=y := by funext i; simp [coordinates15]
  have hz : vector15 (Fin.append y z)=z := by funext i; simp [vector15]
  rw [hy,hz] at h
  exact h hn

theorem sixteen_physical_equivalence (y : HermitianCoordinates SixteenLevelField)
    (z : RealVector SixteenLevelField) (hn : NormalizedKernel y z) :
    hermitianPurity y≤1 ↔ ∃ x : RealFields SixteenLevelField,mass x=1 ∧ GramMatches x y :=
  tower_physical_equivalence 16 y z hn

#print axioms real_physical_equivalence
#print axioms physicalFormula_realize
#print axioms sixteen_physical_equivalence
end W3.TransferOperator
