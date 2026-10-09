import W3.StrataTransferSyntax
import W3.RealModel
import W3.OperatorStrata

noncomputable section
namespace W3.StrataTransfer
open W3.RealModel W3.Operator Matrix
open scoped BigOperators

abbrev RealVector (K : Type*) := Fin 6 → K
abbrev RealMatrix (K : Type*) := Fin 3 → Fin 3 → K

section RingModel
variable {K : Type*} [CommRing K]

def zRe (z : RealVector K) : Fin 3 → K := ![z 0,z 2,z 4]
def zIm (z : RealVector K) : Fin 3 → K := ![z 1,z 3,z 5]
def zMass (z : RealVector K) : K := ∑ i, ((zRe z i)^2+(zIm z i)^2)

def gramRe (x : RealFields K) : RealMatrix K :=
  !![radii x 0,offRe x 0,offRe x 1;
    offRe x 0,radii x 1,offRe x 2;
    offRe x 1,offRe x 2,radii x 2]

def gramIm (x : RealFields K) : RealMatrix K :=
  !![0,offIm x 0,offIm x 1; -offIm x 0,0,offIm x 2; -offIm x 1,-offIm x 2,0]

def operatorDiag (k : Parameters K) (x : RealFields K) : Fin 3 → K :=
  ![k 0*radii x 0+k 3*radii x 1+k 4*radii x 2,
    k 3*radii x 0+k 1*radii x 1+k 5*radii x 2,
    k 4*radii x 0+k 5*radii x 1+k 2*radii x 2]

def operatorOffRe (k : Parameters K) (x : RealFields K) : Fin 3 → K :=
  ![(k 6+k 9)*offRe x 0-k 10*offIm x 0,
    (k 7+k 11)*offRe x 1-k 12*offIm x 1,
    (k 8+k 13)*offRe x 2-k 14*offIm x 2]

def operatorOffIm (k : Parameters K) (x : RealFields K) : Fin 3 → K :=
  ![(k 6-k 9)*offIm x 0-k 10*offRe x 0,
    (k 7-k 11)*offIm x 1-k 12*offRe x 1,
    (k 8-k 13)*offIm x 2-k 14*offRe x 2]

def operatorRe (k : Parameters K) (x : RealFields K) : RealMatrix K :=
  !![operatorDiag k x 0,operatorOffRe k x 0,operatorOffRe k x 1;
    operatorOffRe k x 0,operatorDiag k x 1,operatorOffRe k x 2;
    operatorOffRe k x 1,operatorOffRe k x 2,operatorDiag k x 2]

def operatorIm (k : Parameters K) (x : RealFields K) : RealMatrix K :=
  !![0,operatorOffIm k x 0,operatorOffIm k x 1;
    -operatorOffIm k x 0,0,operatorOffIm k x 2;
    -operatorOffIm k x 1,-operatorOffIm k x 2,0]

def projectorRe (z : RealVector K) (i j : Fin 3) : K := zRe z i*zRe z j+zIm z i*zIm z j
def projectorIm (z : RealVector K) (i j : Fin 3) : K := zIm z i*zRe z j-zRe z i*zIm z j

def actionRe (ar ai : RealMatrix K) (z : RealVector K) (i : Fin 3) : K :=
  ∑ j, (ar i j*zRe z j-ai i j*zIm z j)
def actionIm (ar ai : RealMatrix K) (z : RealVector K) (i : Fin 3) : K :=
  ∑ j, (ar i j*zIm z j+ai i j*zRe z j)

/-- No rank or complex spectral notions occur in this target-field statement. -/
def StrataWitness (k : Parameters K) (x : RealFields K) (z : RealVector K) (mu : K) : Prop :=
  zMass z = 1 ∧
    (((∀ i j, gramRe x i j=projectorRe z i j ∧ gramIm x i j=projectorIm z i j) ∧
      (∀ i, actionRe (operatorRe k x) (operatorIm k x) z i=twiceQuartic k x*zRe z i ∧
        actionIm (operatorRe k x) (operatorIm k x) z i=twiceQuartic k x*zIm z i)) ∨
     ((∀ i, actionRe (gramRe x) (gramIm x) z i=0 ∧ actionIm (gramRe x) (gramIm x) z i=0) ∧
      (∀ i j, operatorRe k x i j=(if i=j then twiceQuartic k x else 0)+mu*projectorRe z i j ∧
        operatorIm k x i j=mu*projectorIm z i j)))


def StrataConclusion (k : Parameters K) (x : RealFields K) : Prop :=
  ∃ z : RealVector K, ∃ mu : K, StrataWitness k x z mu

end RingModel

section Naturality
variable {K L : Type*} [CommRing K] [CommRing L]

@[simp] theorem map_mass (f : K →+* L) (x : RealFields K) : f (mass x)=mass (fun i=>f (x i)) := by
  simp [mass]

@[simp] theorem map_twiceQuartic (f : K →+* L) (k : Parameters K) (x : RealFields K) :
    f (twiceQuartic k x)=twiceQuartic (fun i=>f (k i)) (fun i=>f (x i)) := by
  simp [twiceQuartic,radii,offRe,offIm,map_ofNat]

@[simp] theorem map_zRe (f : K →+* L) (z : RealVector K) (i : Fin 3) :
    f (zRe z i)=zRe (fun j=>f (z j)) i := by fin_cases i <;> rfl
@[simp] theorem map_zIm (f : K →+* L) (z : RealVector K) (i : Fin 3) :
    f (zIm z i)=zIm (fun j=>f (z j)) i := by fin_cases i <;> rfl
@[simp] theorem map_zMass (f : K →+* L) (z : RealVector K) :
    f (zMass z)=zMass (fun i=>f (z i)) := by simp [zMass]

@[simp] theorem map_gramRe (f : K →+* L) (x : RealFields K) (i j : Fin 3) :
    f (gramRe x i j)=gramRe (fun l=>f (x l)) i j := by
  fin_cases i <;> fin_cases j <;> simp [gramRe,radii,offRe]
@[simp] theorem map_gramIm (f : K →+* L) (x : RealFields K) (i j : Fin 3) :
    f (gramIm x i j)=gramIm (fun l=>f (x l)) i j := by
  fin_cases i <;> fin_cases j <;> simp [gramIm,offIm]
@[simp] theorem map_operatorRe (f : K →+* L) (k : Parameters K) (x : RealFields K) (i j : Fin 3) :
    f (operatorRe k x i j)=operatorRe (fun l=>f (k l)) (fun l=>f (x l)) i j := by
  fin_cases i <;> fin_cases j <;> simp [operatorRe,operatorDiag,operatorOffRe,radii,offRe,offIm]
@[simp] theorem map_operatorIm (f : K →+* L) (k : Parameters K) (x : RealFields K) (i j : Fin 3) :
    f (operatorIm k x i j)=operatorIm (fun l=>f (k l)) (fun l=>f (x l)) i j := by
  fin_cases i <;> fin_cases j <;> simp [operatorIm,operatorOffIm,offRe,offIm]
@[simp] theorem map_projectorRe (f : K →+* L) (z : RealVector K) (i j : Fin 3) :
    f (projectorRe z i j)=projectorRe (fun l=>f (z l)) i j := by simp [projectorRe]
@[simp] theorem map_projectorIm (f : K →+* L) (z : RealVector K) (i j : Fin 3) :
    f (projectorIm z i j)=projectorIm (fun l=>f (z l)) i j := by simp [projectorIm]
@[simp] theorem map_actionRe (f : K →+* L) (ar ai : RealMatrix K) (z : RealVector K) (i : Fin 3) :
    f (actionRe ar ai z i)=actionRe (fun i j=>f (ar i j)) (fun i j=>f (ai i j)) (fun l=>f (z l)) i := by
  simp [actionRe]
@[simp] theorem map_actionIm (f : K →+* L) (ar ai : RealMatrix K) (z : RealVector K) (i : Fin 3) :
    f (actionIm ar ai z i)=actionIm (fun i j=>f (ar i j)) (fun i j=>f (ai i j)) (fun l=>f (z l)) i := by
  simp [actionIm]

end Naturality
end W3.StrataTransfer
