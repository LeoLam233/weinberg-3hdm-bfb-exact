import W3.StrataTransferModel

noncomputable section
namespace W3.StrataTransfer
open W3.RealModel W3.Infinitesimal
open OrderedPolynomialFormula

abbrev Poly (n : ℕ) := MvPolynomial (Fin n) ℤ

def neutralFormula {n : ℕ} (k : Parameters (Poly n)) (x : RealFields (Poly n))
    (z : RealVector (Poly n)) : Formula n :=
  OrderedPolynomialFormula.conj
    (allFin 3 (fun i => allFin 3 (fun j =>
      OrderedPolynomialFormula.conj (OrderedPolynomialFormula.eqZero (gramRe x i j-projectorRe z i j)) (OrderedPolynomialFormula.eqZero (gramIm x i j-projectorIm z i j)))))
    (allFin 3 (fun i =>
      OrderedPolynomialFormula.conj (OrderedPolynomialFormula.eqZero (actionRe (operatorRe k x) (operatorIm k x) z i-twiceQuartic k x*zRe z i))
        (OrderedPolynomialFormula.eqZero (actionIm (operatorRe k x) (operatorIm k x) z i-twiceQuartic k x*zIm z i))))

def chargedFormula {n : ℕ} (k : Parameters (Poly n)) (x : RealFields (Poly n))
    (z : RealVector (Poly n)) (mu : Poly n) : Formula n :=
  OrderedPolynomialFormula.conj
    (allFin 3 (fun i =>
      OrderedPolynomialFormula.conj (OrderedPolynomialFormula.eqZero (actionRe (gramRe x) (gramIm x) z i)) (OrderedPolynomialFormula.eqZero (actionIm (gramRe x) (gramIm x) z i))))
    (allFin 3 (fun i => allFin 3 (fun j =>
      OrderedPolynomialFormula.conj (OrderedPolynomialFormula.eqZero (operatorRe k x i j-(if i=j then twiceQuartic k x else 0)-mu*projectorRe z i j))
        (OrderedPolynomialFormula.eqZero (operatorIm k x i j-mu*projectorIm z i j)))))

def witnessFormula {n : ℕ} (k : Parameters (Poly n)) (x : RealFields (Poly n))
    (z : RealVector (Poly n)) (mu : Poly n) : Formula n :=
  OrderedPolynomialFormula.conj (OrderedPolynomialFormula.eqZero (zMass z-1)) ((neutralFormula k x z).disj (chargedFormula k x z mu))

def parameters27 {K : Type*} (v : Fin 27 → K) : Parameters K := fun i => v (Fin.castAdd 12 i)
def fields27 {K : Type*} (v : Fin 27 → K) : RealFields K := fun i => v (Fin.natAdd 15 i)
def witnessZ {K : Type*} (w : Fin 7 → K) : RealVector K := fun i => w (Fin.castAdd 1 i)
def witnessMu {K : Type*} (w : Fin 7 → K) : K := w 6

def witnessVector {K : Type*} (z : RealVector K) (mu : K) : Fin 7 → K :=
  Fin.append z (fun _ : Fin 1 => mu)

@[simp] theorem witnessZ_vector {K : Type*} (z : RealVector K) (mu : K) :
    witnessZ (witnessVector z mu)=z := by funext i; simp [witnessZ,witnessVector]
@[simp] theorem witnessMu_vector {K : Type*} (z : RealVector K) (mu : K) :
    witnessMu (witnessVector z mu)=mu := rfl

/-- Actual twelve-variable universal comparison in the formula syntax. -/
def comparisonBody : Formula (27+12) :=
  let v : Fin 27 → Poly (27+12) := fun i => MvPolynomial.X (backIndex 27 12 i)
  let y : RealFields (Poly (27+12)) := fun i => MvPolynomial.X (frontIndex 27 12 i)
  (OrderedPolynomialFormula.eqZero (mass y-1)).implies
    (OrderedPolynomialFormula.nonneg (twiceQuartic (parameters27 v) y-twiceQuartic (parameters27 v) (fields27 v)))

/-- Actual seven-variable existential witness in the formula syntax. -/
def witnessBody : Formula (27+7) :=
  let v : Fin 27 → Poly (27+7) := fun i => MvPolynomial.X (backIndex 27 7 i)
  let w : Fin 7 → Poly (27+7) := fun i => MvPolynomial.X (frontIndex 27 7 i)
  witnessFormula (parameters27 v) (fields27 v) (witnessZ w) (witnessMu w)

/-- The concrete source-to-tower formula, with all quantifiers and all polynomials specified. -/
def stationaryStrataFormula : Formula 27 :=
  (OrderedPolynomialFormula.conj (OrderedPolynomialFormula.eqZero (mass (fields27 MvPolynomial.X)-1)) (allVec 12 comparisonBody)).implies
    (exVec 7 witnessBody)

section Semantics
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem conditional_sub_eq (p : Prop) [Decidable p] (a b c : K) :
    (if p then a-b else a-0)=c ↔ a=(if p then b else 0)+c := by
  by_cases hp : p <;> simp [hp,sub_eq_iff_eq_add,add_comm]

theorem witnessFormula_realize {n : ℕ} (k : Parameters (Poly n)) (x : RealFields (Poly n))
    (z : RealVector (Poly n)) (mu : Poly n) (v : Fin n → K) :
    (witnessFormula k x z mu).Realize v ↔
      StrataWitness (fun i => intPolynomialEval (k i) v) (fun i => intPolynomialEval (x i) v)
        (fun i => intPolynomialEval (z i) v) (intPolynomialEval mu v) := by
  simp only [witnessFormula,neutralFormula,chargedFormula,realize_disj,realize_allFin,
    Realize,StrataWitness,intPolynomialEval,map_sub,map_mul,map_one,map_zero,map_zMass,
    map_gramRe,map_gramIm,map_projectorRe,map_projectorIm,map_operatorRe,map_operatorIm,
    map_actionRe,map_actionIm,map_twiceQuartic,map_zRe,map_zIm,apply_ite,sub_sub,sub_eq_zero,conditional_sub_eq]

@[simp] theorem comparisonBody_realize (v : Fin 27 → K) (y : RealFields K) :
    comparisonBody.Realize (extendVec v y) ↔
      (mass y=1 → twiceQuartic (parameters27 v) (fields27 v)≤twiceQuartic (parameters27 v) y) := by
  simp [comparisonBody,realize_implies,Realize,intPolynomialEval,parameters27,fields27,sub_nonneg,map_sub,map_one,sub_eq_zero] <;> rfl

@[simp] theorem witnessBody_realize (v : Fin 27 → K) (w : Fin 7 → K) :
    witnessBody.Realize (extendVec v w) ↔
      StrataWitness (parameters27 v) (fields27 v) (witnessZ w) (witnessMu w) := by
  rw [witnessBody,witnessFormula_realize]
  simp [intPolynomialEval,parameters27,fields27,witnessZ,witnessMu] <;> rfl

@[simp] theorem quantified_witness_realize (v : Fin 27 → K) :
    (exVec 7 witnessBody).Realize v ↔ StrataConclusion (parameters27 v) (fields27 v) := by
  rw [realize_exVec]
  simp only [witnessBody_realize]
  constructor
  · rintro ⟨w,hw⟩
    exact ⟨witnessZ w,witnessMu w,hw⟩
  · rintro ⟨z,mu,hz⟩
    exact ⟨witnessVector z mu,by simpa using hz⟩

/-- Exact semantic equivalence; no correctness-of-encoding premise is assumed. -/
theorem stationaryStrataFormula_realize (v : Fin 27 → K) :
    stationaryStrataFormula.Realize v ↔
    ((mass (fields27 v)=1 ∧ ∀ y : RealFields K,mass y=1→
      twiceQuartic (parameters27 v) (fields27 v)≤twiceQuartic (parameters27 v) y) →
      StrataConclusion (parameters27 v) (fields27 v)) := by
  simp [stationaryStrataFormula,realize_implies,Realize,intPolynomialEval,fields27,map_sub,map_one,sub_eq_zero] <;> rfl

end Semantics
end W3.StrataTransfer
