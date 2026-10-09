import W3.FiniteInputCandidatesLists
import W3.OperatorFieldCandidates

/-! Explicit finite square-root branches realizing phases and radii. Every sign
is enumerated. The proof covers arbitrary representatives of the same square. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace W3.FiniteInput
open Polynomial W3.Elimination W3.Weighted W3.Infinitesimal W3.OperatorField W3.RealModel
open ComplexPair

section Algebra
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem phaseRadius_minus (r : K) (q : ComplexPair K) (hq : normSq q = 1)
    (hm : q.re = -1) (b : K) (hb : b^2 = r) :
    normSq (⟨0,-b⟩ : ComplexPair K) = r ∧
      conj (mul (⟨0,-b⟩ : ComplexPair K) ⟨0,-b⟩) = scale r q := by
  have hi : q.im = 0 := by
    change q.re^2+q.im^2=1 at hq
    rw [hm] at hq
    nlinarith [sq_nonneg q.im]
  constructor
  · simp [normSq,hb]
  · apply complexPair_ext <;> simp [mul,conj,scale,hm,hi,← hb] <;> ring

theorem phaseRadius_root_nonzero (r : K) (q : ComplexPair K) (hr : 0 ≤ r)
    (hq : normSq q = 1) (hr0 : r ≠ 0) (hm : q.re ≠ -1)
    (a : K) (ha : a^2 = r*(1+q.re)/2) : a ≠ 0 := by
  have hn : q.re^2+q.im^2=1 := hq
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  have hre : 0 < 1+q.re := by
    have hb : -1 ≤ q.re := by nlinarith [sq_nonneg q.im,sq_nonneg (q.re+1)]
    have hz : 1+q.re ≠ 0 := by intro he; apply hm; linear_combination he
    exact lt_of_le_of_ne (by linarith) (Ne.symm hz)
  have hp : 0 < r*(1+q.re)/2 := div_pos (mul_pos hrp hre) (by norm_num)
  intro hz
  rw [hz] at ha
  nlinarith

theorem phaseRadius_other (r : K) (q : ComplexPair K) (hr : 0 ≤ r)
    (hq : normSq q = 1) (hr0 : r ≠ 0) (hm : q.re ≠ -1)
    (a : K) (ha : a^2 = r*(1+q.re)/2) :
    normSq (⟨a,-(r*q.im/(2*a))⟩ : ComplexPair K) = r ∧
      conj (mul (⟨a,-(r*q.im/(2*a))⟩ : ComplexPair K) ⟨a,-(r*q.im/(2*a))⟩) = scale r q := by
  have hn : q.re^2+q.im^2=1 := hq
  have ha0 := phaseRadius_root_nonzero r q hr hq hr0 hm a ha
  let b := r*q.im/(2*a)
  have hb : b^2 = r*(1-q.re)/2 := by
    dsimp [b]
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 2 (mul_ne_zero (by norm_num) ha0))).mpr
    linear_combination r^2*hn-2*r*(1-q.re)*ha
  have hab : 2*a*b=r*q.im := by dsimp [b]; field_simp [ha0]
  constructor
  · change a^2+(-b)^2=r
    rw [neg_sq,ha,hb]
    ring
  · apply complexPair_ext
    · change a*a-(-b)*(-b)=r*q.re
      nlinarith [ha,hb]
    · change -(a*(-b)+(-b)*a)=r*q.im
      linear_combination hab

end Algebra

variable {n : Nat}
def phaseRadiusOtherCode (r : Code n) (q : ComplexPair (Code n)) (a : Code n) : ComplexPair (Code n) :=
  ⟨a,-(r*q.im/(2*a))⟩

section Program
variable {F K : Type*} [Field F] [CharZero F] [DecidableEq F]
    [Field K] [Algebra F K] [LinearOrder K] [IsStrictOrderedRing K]
variable (input : Fin 15 → F) (epsilon : Fin n → F) (O : RealRootEnumeration K)

def phaseRadiusProgram (r : Code n) (q : ComplexPair (Code n)) : List (ComplexPair (Code n)) := by
  classical
  exact if (r.run input epsilon O).value = 0 then [⟨0,0⟩]
    else if (q.re.run input epsilon O).value = -1 then
      (squareRootFamily input epsilon O r).map (fun b => ⟨0,-b⟩)
    else (squareRootFamily input epsilon O (r*(1+q.re)/2)).map (phaseRadiusOtherCode r q)

@[simp] theorem run_phaseRadiusOther (r a : Code n) (q : ComplexPair (Code n)) :
    runComplex input epsilon O (phaseRadiusOtherCode r q a) =
      ⟨(a.run input epsilon O).value,
        -((r.run input epsilon O).value*(q.im.run input epsilon O).value/(2*(a.run input epsilon O).value))⟩ := by
  simp [runComplex,phaseRadiusOtherCode]

/-- Exact finite enumeration of both real-coordinate square-root signs. -/
theorem phaseRadiusProgram_correct (r : Code n) (q : ComplexPair (Code n))
    (hr : 0 ≤ (r.run input epsilon O).value)
    (hq : normSq (runComplex input epsilon O q)=1) (z : ComplexPair K) :
    z ∈ (phaseRadiusProgram input epsilon O r q).map (runComplex input epsilon O) ↔
      normSq z = (r.run input epsilon O).value ∧
        conj (mul z z) = scale (r.run input epsilon O).value (runComplex input epsilon O q) := by
  classical
  let R := (r.run input epsilon O).value
  let Q := runComplex input epsilon O q
  by_cases hr0 : R=0
  · rw [phaseRadiusProgram,if_pos (show (r.run input epsilon O).value = 0 from hr0)]
    simp only [List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false]
    constructor
    · intro hz
      subst z
      simp [runComplex,normSq,mul,conj,scale,hr0,R]
    · rintro ⟨hn,_⟩
      have hzre : z.re=0 := by change z.re^2+z.im^2=R at hn; rw [hr0] at hn; nlinarith [sq_nonneg z.im]
      have hzim : z.im=0 := by change z.re^2+z.im^2=R at hn; rw [hr0] at hn; nlinarith [sq_nonneg z.re]
      apply complexPair_ext <;> simp [runComplex,hzre,hzim]
  · by_cases hm : Q.re = -1
    · rw [phaseRadiusProgram,if_neg (show (r.run input epsilon O).value ≠ 0 from hr0),
        if_pos (show (q.re.run input epsilon O).value = -1 from hm)]
      simp only [List.map_map,List.mem_map,Function.comp_def]
      constructor
      · rintro ⟨b,hb,rfl⟩
        have hb' := (squareRootProgram_mem input epsilon O r (b.run input epsilon O).value).mp ⟨b,hb,rfl⟩
        simpa [runComplex,R,Q] using phaseRadius_minus R Q hq hm _ hb'
      · rintro ⟨hn,hs⟩
        have hsre := congrArg ComplexPair.re hs
        have hsim := congrArg ComplexPair.im hs
        change z.re^2+z.im^2=R at hn
        change z.re*z.re-z.im*z.im=R*Q.re at hsre
        rw [hm] at hsre
        have hzre : z.re=0 := by nlinarith [sq_nonneg z.re]
        have hb : (-z.im)^2=R := by nlinarith
        obtain ⟨b,hb,hbv⟩ := (squareRootProgram_mem input epsilon O r (-z.im)).mpr hb
        refine ⟨b,hb,?_⟩
        apply complexPair_ext <;> simp [runComplex,hzre,hbv]
    · rw [phaseRadiusProgram,if_neg (show (r.run input epsilon O).value ≠ 0 from hr0),
        if_neg (show (q.re.run input epsilon O).value ≠ -1 from hm)]
      simp only [List.map_map,List.mem_map,Function.comp_def]
      constructor
      · rintro ⟨a,ha,rfl⟩
        have ha' := (squareRootProgram_mem input epsilon O (r*(1+q.re)/2)
          (a.run input epsilon O).value).mp ⟨a,ha,rfl⟩
        simp only [run_div,run_mul,run_add,run_one,run_two] at ha'
        rw [run_phaseRadiusOther]
        exact phaseRadius_other R Q hr hq hr0 hm _ ha'
      · rintro ⟨hn,hs⟩
        have hsre := congrArg ComplexPair.re hs
        have hsim := congrArg ComplexPair.im hs
        change z.re^2+z.im^2=R at hn
        change z.re*z.re-z.im*z.im=R*Q.re at hsre
        change -(z.re*z.im+z.im*z.re)=R*Q.im at hsim
        have ha : z.re^2=R*(1+Q.re)/2 := by nlinarith
        have ha0 := phaseRadius_root_nonzero R Q hr hq hr0 hm z.re ha
        have har : z.re^2=((r*(1+q.re)/2).run input epsilon O).value := by
          simpa [R,Q,runComplex] using ha
        obtain ⟨a,ham,hav⟩ := (squareRootProgram_mem input epsilon O (r*(1+q.re)/2) z.re).mpr har
        refine ⟨a,ham,?_⟩
        rw [run_phaseRadiusOther,hav]
        apply complexPair_ext
        · rfl
        · change -(R*Q.im/(2*z.re))=z.im
          apply (neg_eq_iff_eq_neg).mpr
          apply (div_eq_iff (mul_ne_zero (by norm_num) ha0)).mpr
          linear_combination hsim.symm

end Program
end W3.FiniteInput
