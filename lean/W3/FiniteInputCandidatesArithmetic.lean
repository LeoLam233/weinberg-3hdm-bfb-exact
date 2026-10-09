import W3.FiniteInputSyntax
import W3.WeightedSpectrum
import W3.EliminationPolynomial

/-! Explicit arithmetic coordinate programs for the three support types. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace W3.FiniteInput
open Polynomial W3.Elimination W3.Weighted W3.Infinitesimal

namespace Code
variable {n : Nat}
instance : Add (Code n) := ⟨Code.add⟩
instance : Mul (Code n) := ⟨Code.mul⟩
instance : Neg (Code n) := ⟨Code.neg⟩
instance : Inv (Code n) := ⟨Code.inv⟩
instance : Sub (Code n) := ⟨fun a b => a + -b⟩
instance : Div (Code n) := ⟨fun a b => a * b⁻¹⟩
instance (k : Nat) : OfNat (Code n) k := ⟨.coefficient (.rational k)⟩
def sq (a : Code n) : Code n := a * a
end Code

variable {n : Nat}
def evalWeighted {F : Type*} [Field F] [CharZero F]
    (input : Fin 15 → F) (epsilon : Fin n → F)
    (w : WeightedData (CoefficientCode n)) : WeightedData F :=
  ⟨w.alpha1.eval input epsilon, w.alpha2.eval input epsilon, w.alpha3.eval input epsilon,
   w.e12.eval input epsilon, w.e13.eval input epsilon, w.e23.eval input epsilon,
   w.d12r.eval input epsilon, w.d12i.eval input epsilon,
   w.d13r.eval input epsilon, w.d13i.eval input epsilon,
   w.d23r.eval input epsilon, w.d23i.eval input epsilon,
   w.g1.eval input epsilon, w.g2.eval input epsilon, w.g3.eval input epsilon⟩

def liftWeighted (w : WeightedData (CoefficientCode n)) : WeightedData (Code n) :=
  ⟨.coefficient w.alpha1, .coefficient w.alpha2, .coefficient w.alpha3,
   .coefficient w.e12, .coefficient w.e13, .coefficient w.e23,
   .coefficient w.d12r, .coefficient w.d12i, .coefficient w.d13r, .coefficient w.d13i,
   .coefficient w.d23r, .coefficient w.d23i,
   .coefficient w.g1, .coefficient w.g2, .coefficient w.g3⟩

def complexMul (a b : ComplexPair (Code n)) : ComplexPair (Code n) :=
  ⟨a.re*b.re-a.im*b.im, a.re*b.im+a.im*b.re⟩
def complexConj (a : ComplexPair (Code n)) : ComplexPair (Code n) := ⟨a.re,-a.im⟩
def onePhaseCode : ComplexPair (Code n) := ⟨1,0⟩
def circleCode (t : Code n) : ComplexPair (Code n) :=
  ⟨(1-Code.sq t)/(1+Code.sq t), (2*t)/(1+Code.sq t)⟩

def singletonCode (i : Fin 3) : SpectrumPoint (Code n) :=
  ![⟨1,0,0,onePhaseCode,onePhaseCode⟩, ⟨0,1,0,onePhaseCode,onePhaseCode⟩,
    ⟨0,0,1,onePhaseCode,onePhaseCode⟩] i

def pairInputCode (w : WeightedData (Code n)) (i : Fin 3) : PairInput (Code n) :=
  ![⟨w.alpha1,w.alpha2,w.e12,⟨w.d12r,w.d12i⟩,w.g1,w.g2⟩,
    ⟨w.alpha1,w.alpha3,w.e13,⟨w.d13r,w.d13i⟩,w.g1,w.g3⟩,
    ⟨w.alpha2,w.alpha3,w.e23,⟨w.d23r,w.d23i⟩,w.g2,w.g3⟩] i

def branchSignCode (s : Bool) : Code n := if s then 1 else -1

def pairPointCode (w : WeightedData (Code n)) (rho : Code n) (i : Fin 3)
    (s : Bool) : SpectrumPoint (Code n) :=
  let p := pairInputCode w i
  let h := (p.e + branchSignCode s * rho)/2
  let nl := (p.b/2)*p.g₁-h*p.g₂
  let nr := (p.a/2)*p.g₂-h*p.g₁
  let l := nl/(nl+nr)
  let r := nr/(nl+nr)
  let q : ComplexPair (Code n) :=
    ⟨branchSignCode s * p.d.re / rho, -(branchSignCode s * p.d.im)/rho⟩
  ![⟨l,r,0,q,onePhaseCode⟩,⟨l,0,r,onePhaseCode,q⟩,⟨0,l,r,onePhaseCode,q⟩] i

def fullPointCode (w : WeightedData (Code n)) (t u : Code n) : SpectrumPoint (Code n) :=
  let q := circleCode t
  let v := circleCode u
  let j12 := (complexMul ⟨w.d12r,w.d12i⟩ q).im
  let j13 := (complexMul ⟨w.d13r,w.d13i⟩ v).im
  let j23 := (complexMul ⟨w.d23r,w.d23i⟩ (complexMul v (complexConj q))).im
  let d := j23-j13+j12
  ⟨j23/d,-j13/d,j12/d,q,v⟩

def valueCode (w : WeightedData (Code n)) (x : SpectrumPoint (Code n)) : Code n :=
  let h12 := w.e12 + (complexMul ⟨w.d12r,w.d12i⟩ x.q).re
  let h13 := w.e13 + (complexMul ⟨w.d13r,w.d13i⟩ x.v).re
  let h23 := w.e23 + (complexMul ⟨w.d23r,w.d23i⟩ (complexMul x.v (complexConj x.q))).re
  let b1 := w.alpha1*x.r₁+h12*x.r₂+h13*x.r₃
  let b2 := h12*x.r₁+w.alpha2*x.r₂+h23*x.r₃
  let b3 := h13*x.r₁+h23*x.r₂+w.alpha3*x.r₃
  let g := w.g1*x.r₁+w.g2*x.r₂+w.g3*x.r₃
  (x.r₁*b1+x.r₂*b2+x.r₃*b3)/(2*Code.sq g)

section Evaluate
variable {F K : Type*} [Field F] [CharZero F] [DecidableEq F]
    [Field K] [Algebra F K] [LinearOrder K] [IsStrictOrderedRing K]
variable (input : Fin 15 → F) (epsilon : Fin n → F) (O : RealRootEnumeration K)

def runWeighted (w : WeightedData (CoefficientCode n)) : WeightedData K :=
  mapWeighted (algebraMap F K) (evalWeighted input epsilon w)

def runComplex (z : ComplexPair (Code n)) : ComplexPair K :=
  ⟨(z.re.run input epsilon O).value,(z.im.run input epsilon O).value⟩
def runPoint (x : SpectrumPoint (Code n)) : SpectrumPoint K :=
  ⟨(x.r₁.run input epsilon O).value,(x.r₂.run input epsilon O).value,
   (x.r₃.run input epsilon O).value,runComplex input epsilon O x.q,runComplex input epsilon O x.v⟩

@[simp] theorem run_nat (k : Nat) :
    ((OfNat.ofNat k : Code n).run input epsilon O).value = (k : K) := by
  simp [OfNat.ofNat,Code.run,CoefficientCode.eval]

@[simp] theorem run_zero : ((0 : Code n).run input epsilon O).value = 0 := by
  simp [Code.run,CoefficientCode.eval]
@[simp] theorem run_one : ((1 : Code n).run input epsilon O).value = 1 := by
  simp [Code.run,CoefficientCode.eval]
@[simp] theorem run_two : ((2 : Code n).run input epsilon O).value = 2 := by
  norm_num [Code.run,CoefficientCode.eval,map_ofNat]
@[simp] theorem run_add (a b : Code n) :
    ((a+b).run input epsilon O).value =
      (a.run input epsilon O).value + (b.run input epsilon O).value := rfl
@[simp] theorem run_mul (a b : Code n) :
    ((a*b).run input epsilon O).value =
      (a.run input epsilon O).value * (b.run input epsilon O).value := rfl
@[simp] theorem run_neg (a : Code n) :
    ((-a).run input epsilon O).value = -(a.run input epsilon O).value := rfl

@[simp] theorem run_sub (a b : Code n) :
    ((a-b).run input epsilon O).value =
      (a.run input epsilon O).value - (b.run input epsilon O).value := by
  change ((Code.add a (Code.neg b)).run input epsilon O).value = _
  simp [sub_eq_add_neg]

@[simp] theorem run_div (a b : Code n) :
    ((a/b).run input epsilon O).value =
      (a.run input epsilon O).value / (b.run input epsilon O).value := by
  change ((Code.mul a (Code.inv b)).run input epsilon O).value = _
  simp [div_eq_mul_inv]

@[simp] theorem run_sq (a : Code n) :
    ((Code.sq a).run input epsilon O).value = (a.run input epsilon O).value^2 := by
  simp [Code.sq,pow_two]

@[simp] theorem run_complexMul (a b : ComplexPair (Code n)) :
    runComplex input epsilon O (complexMul a b) =
      ComplexPair.mul (runComplex input epsilon O a) (runComplex input epsilon O b) := by
  simp [runComplex,complexMul,ComplexPair.mul]

@[simp] theorem run_complexConj (a : ComplexPair (Code n)) :
    runComplex input epsilon O (complexConj a) = ComplexPair.conj (runComplex input epsilon O a) := by
  simp [runComplex,complexConj,ComplexPair.conj]

@[simp] theorem run_onePhase : runComplex input epsilon O (onePhaseCode : ComplexPair (Code n)) = onePhase := by
  simp [runComplex,onePhaseCode,onePhase]

@[simp] theorem run_circle (a : Code n) :
    runComplex input epsilon O (circleCode a) = circlePoint 1 (a.run input epsilon O).value := by
  simp [runComplex,circleCode,circlePoint]

@[simp] theorem run_singleton (i : Fin 3) :
    runPoint input epsilon O (singletonCode i) = singletonPoint i := by
  fin_cases i <;> simp [singletonCode,singletonPoint,runPoint]

@[simp] theorem run_branchSign (s : Bool) :
    ((branchSignCode s : Code n).run input epsilon O).value = branchSign s := by
  cases s <;> simp [branchSignCode,branchSign]

@[simp] theorem run_pairPoint (w : WeightedData (CoefficientCode n))
    (rho : Code n) (i : Fin 3) (s : Bool) :
    runPoint input epsilon O (pairPointCode (liftWeighted w) rho i s) =
      pairPoint (runWeighted input epsilon w)
        (fun _ => (rho.run input epsilon O).value) i s := by
  fin_cases i <;>
    simp [runPoint,runComplex,pairPointCode,pairPoint,pairInputCode,pairInput,
      pairLeft,pairRight,pairSum,pairN₁,pairN₂,pairH,pairPhase,
      liftWeighted,runWeighted,evalWeighted,mapWeighted,onePhaseCode,onePhase]

@[simp] theorem run_fullPoint (w : WeightedData (CoefficientCode n)) (t u : Code n) :
    runPoint input epsilon O (fullPointCode (liftWeighted w) t u) =
      fullPoint (runWeighted input epsilon w) (t.run input epsilon O).value
        (u.run input epsilon O).value := by
  simp [runPoint,runComplex,fullPointCode,fullPoint,complexMul,complexConj,
    circleCode,circlePoint,Code.sq,currentDen,edge₁₂,edge₁₃,edge₂₃,
    ComplexPair.mul,ComplexPair.conj,liftWeighted,runWeighted,evalWeighted,mapWeighted,toSpectrum,pow_two]

@[simp] theorem run_value (w : WeightedData (CoefficientCode n)) (x : SpectrumPoint (Code n)) :
    ((valueCode (liftWeighted w) x).run input epsilon O).value =
      spectrumValue (runWeighted input epsilon w) (runPoint input epsilon O x) := by
  simp [valueCode,spectrumValue,weightedQuotient,twiceB₁,twiceB₂,twiceB₃,
    runPoint,runComplex,complexMul,complexConj,Code.sq,edge₁₂,edge₁₃,edge₂₃,
    ComplexPair.mul,ComplexPair.conj,liftWeighted,runWeighted,evalWeighted,mapWeighted,toSpectrum,pow_two]

end Evaluate
end W3.FiniteInput
