import Foundation.YMPositiveKernel
import Mathlib.Probability.ProbabilityMassFunction.Constructions
/-!
A finite Z2 shared-plaquette Wilson-noise quotient with an explicit positive
ground state, stationary PMFs and a sharp failure of an unchanged kinetic gap
after one elementary plaquette multiplier. This is not an SU2 or 4D theorem.
-/
noncomputable section
open MeasureTheory
open scoped Matrix
namespace OperatorDerivativeRewrite.Foundation.WilsonPlaquetteGapCounterexample
abbrev State := Fin 4

def kinetic : Matrix State State ℝ :=
  !![13/36,2/9,2/9,7/36;2/9,13/36,7/36,2/9;
     2/9,7/36,13/36,2/9;7/36,2/9,2/9,13/36]
def amplitude : State → ℝ := ![2,2,1,1]
def ground : State → ℝ := ![5,5,2,2]
def transfer (i j : State) : ℝ := amplitude i*kinetic i j*amplitude j
def groundValue : ℝ := 8/3
def step (i j : State) : ℝ := transfer i j*ground j/(groundValue*ground i)
def stationary : State → ℝ := ![25/58,25/58,2/29,2/29]
def probe : State → ℝ := ![1,-1,0,0]
def mean (f : State → ℝ) : ℝ := ∑ i, stationary i*f i
def secondMoment (f : State → ℝ) : ℝ := ∑ i, stationary i*f i^2
def lagPairing (f : State → ℝ) : ℝ := ∑ i, stationary i*f i*(∑ j, step i j*f j)

theorem ground_positive (i : State) : 0 < ground i := by fin_cases i <;> norm_num [ground]
theorem kinetic_positive (i j : State) : 0 < kinetic i j := by
 fin_cases i <;> fin_cases j <;> norm_num [kinetic]
theorem kinetic_rows (i : State) : (∑ j, kinetic i j)=1 := by
 fin_cases i <;> norm_num [kinetic,Fin.sum_univ_succ]
theorem transfer_symmetric (i j : State) : transfer i j=transfer j i := by
 fin_cases i <;> fin_cases j <;> norm_num [transfer,amplitude,kinetic]
theorem ground_eigen (i : State) : (∑ j, transfer i j*ground j)=groundValue*ground i := by
 fin_cases i <;> norm_num [transfer,amplitude,kinetic,ground,groundValue,Fin.sum_univ_succ]
theorem step_positive (i j : State) : 0 < step i j := by
 fin_cases i <;> fin_cases j <;> norm_num [step,transfer,amplitude,kinetic,ground,groundValue]
theorem step_rows (i : State) : (∑ j, step i j)=1 := by
 fin_cases i <;> norm_num [step,transfer,amplitude,kinetic,ground,groundValue,Fin.sum_univ_succ]
theorem stationary_positive (i : State) : 0 < stationary i := by fin_cases i <;> norm_num [stationary]
theorem stationary_total : (∑ i, stationary i)=1 := by norm_num [stationary,Fin.sum_univ_succ]
theorem stationary_ground (i : State) : stationary i=ground i^2/(∑ j,ground j^2) := by
 fin_cases i <;> norm_num [stationary,ground,Fin.sum_univ_succ]
theorem detailed_balance (i j : State) : stationary i*step i j=stationary j*step j i := by
 fin_cases i <;> fin_cases j <;> norm_num [stationary,step,transfer,amplitude,kinetic,ground,groundValue]
theorem stationary_step (j : State) : (∑ i,stationary i*step i j)=stationary j := by
 fin_cases j <;> norm_num [stationary,step,transfer,amplitude,kinetic,ground,groundValue,Fin.sum_univ_succ]

def rowPMF (i : State) : PMF State := PMF.ofFintype (fun j => ENNReal.ofReal (step i j)) (by
 rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => (step_positive i j).le),step_rows]
 norm_num)
def stationaryPMF : PMF State := PMF.ofFintype (fun i => ENNReal.ofReal (stationary i)) (by
 rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (stationary_positive i).le),stationary_total]
 norm_num)

theorem kinetic_centered_bound (f : State → ℝ) (hf : (∑ i,f i)=0) :
    (∑ i,f i*(∑ j,kinetic i j*f j)) ≤ (1/6:ℝ)*(∑ i,f i^2) := by
 have hid : (1/6:ℝ)*(∑ i,f i^2)-(∑ i,f i*(∑ j,kinetic i j*f j)) =
   -(5/24:ℝ)*(∑ i,f i)^2+(1/72:ℝ)*(f 0-f 1-f 2+f 3)^2 := by
   simp only [Fin.sum_univ_succ]
   norm_num [kinetic]
   ring
 rw [hf] at hid
 nlinarith [sq_nonneg (f 0-f 1-f 2+f 3)]

theorem kinetic_bound_sharp :
    (∑ i, (![1,-1,1,-1] : State → ℝ) i)=0 ∧
    ∀ i : State, (∑ j,kinetic i j*(![1,-1,1,-1] : State → ℝ) j)=
      (1/6:ℝ)*(![1,-1,1,-1] : State → ℝ) i := by
 constructor
 · norm_num [Fin.sum_univ_succ]
 · intro i; fin_cases i <;> norm_num [kinetic,Fin.sum_univ_succ]

theorem probe_values : mean probe=0 ∧ secondMoment probe=25/29 ∧ lagPairing probe=125/696 := by
 norm_num [mean,secondMoment,lagPairing,probe,stationary,step,transfer,amplitude,kinetic,ground,groundValue,Fin.sum_univ_succ]

theorem normalized_pairing_exceeds_kinetic : (1/6:ℝ)*secondMoment probe < lagPairing probe := by
 rw [probe_values.2.1,probe_values.2.2]
 norm_num

theorem unchanged_gap_fails :
    ¬∀ f : State → ℝ, mean f=0 →
      (5/6:ℝ)*secondMoment f ≤ secondMoment f-lagPairing f := by
 intro h
 have hh := h probe probe_values.1
 rw [probe_values.2.1,probe_values.2.2] at hh
 norm_num at hh

/-- The multiplier is a scalar multiple of the literal one-plaquette half weight. -/
theorem amplitude_wilson_form (i : State) :
    amplitude i=Real.sqrt 2*Real.exp ((Real.log 2/2)*(![1,1,-1,-1] : State → ℝ) i) := by
 have hs : Real.exp (Real.log 2/2)=Real.sqrt 2 := by rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]; congr 1; ring
 have hspos := Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)
 have hsquare := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
 fin_cases i <;> norm_num [amplitude] <;>
   first | (rw [hs]; nlinarith) | (rw [Real.exp_neg,hs]; exact (mul_inv_cancel₀ hspos.ne').symm)
end OperatorDerivativeRewrite.Foundation.WilsonPlaquetteGapCounterexample

namespace OperatorDerivativeRewrite.Foundation.WilsonPlaquetteGapCounterexample

theorem stationary_bind : stationaryPMF.bind rowPMF=stationaryPMF := by
  ext j
  rw [PMF.bind_apply,tsum_fintype]
  simp only [rowPMF,stationaryPMF,PMF.ofFintype_apply]
  simp_rw [← ENNReal.ofReal_mul (stationary_positive _).le]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (stationary_positive i).le (step_positive i j).le),stationary_step]

def leftFlip (y : Fin 128) : Bool :=
  Bool.xor (Bool.xor (Bool.xor (y.val.testBit 0) (y.val.testBit 2)) (y.val.testBit 4)) (y.val.testBit 5)
def rightFlip (y : Fin 128) : Bool :=
  Bool.xor (Bool.xor (Bool.xor (y.val.testBit 1) (y.val.testBit 3)) (y.val.testBit 5)) (y.val.testBit 6)
def noiseLabel (y : Fin 128) : ℕ := (if leftFlip y then 2 else 0)+(if rightFlip y then 1 else 0)
def noiseWeight (y : Fin 128) : ℕ :=
  (if y.val.testBit 0 then 1 else 5)*(if y.val.testBit 1 then 1 else 5)*
  (if y.val.testBit 2 then 1 else 5)*(if y.val.testBit 3 then 1 else 5)*
  (if y.val.testBit 4 then 1 else 7)*(if y.val.testBit 5 then 1 else 3)*
  (if y.val.testBit 6 then 1 else 7)
def noiseIndex (b : Fin 8) (r : Fin 16) : Fin 128 := ⟨16*b.val+r.val,by omega⟩

theorem noiseIndex_bijective : Function.Bijective (fun p : Fin 8 × Fin 16 => noiseIndex p.1 p.2) := by
  constructor
  · intro p q he
    have hv := congrArg Fin.val he
    change 16*p.1.val+p.2.val=16*q.1.val+q.2.val at hv
    have hb : p.1=q.1 := Fin.ext (by omega)
    have hr : p.2=q.2 := Fin.ext (by omega)
    exact Prod.ext hb hr
  · intro y
    refine ⟨(⟨y.val/16,by omega⟩,⟨y.val%16,by omega⟩),?_⟩
    apply Fin.ext
    change 16*(y.val/16)+y.val%16=y.val
    omega

def noiseCount (j : State) : ℕ := ∑ b : Fin 8, ∑ r : Fin 16,
  if noiseLabel (noiseIndex b r)=j.val then noiseWeight (noiseIndex b r) else 0

theorem noiseCount_zero : noiseCount 0=119808 := by decide
theorem noiseCount_one : noiseCount 1=73728 := by decide
theorem noiseCount_two : noiseCount 2=73728 := by decide
theorem noiseCount_three : noiseCount 3=64512 := by decide
theorem noise_total : (∑ b : Fin 8, ∑ r : Fin 16,noiseWeight (noiseIndex b r))=331776 := by decide

theorem noise_quotient_certificate (j : State) : (noiseCount j : ℝ)/331776=kinetic 0 j := by
 fin_cases j <;> norm_num [noiseCount_zero,noiseCount_one,noiseCount_two,noiseCount_three,kinetic]
end OperatorDerivativeRewrite.Foundation.WilsonPlaquetteGapCounterexample

namespace OperatorDerivativeRewrite.Foundation.WilsonPlaquetteGapCounterexample

def labelDifference (i j : State) : State := ⟨Nat.xor i.val j.val,by
 fin_cases i <;> fin_cases j <;> decide⟩

theorem kinetic_difference (i j : State) : kinetic i j=kinetic 0 (labelDifference i j) := by
 fin_cases i <;> fin_cases j <;> norm_num [kinetic,labelDifference]

theorem full_noise_quotient_certificate (i j : State) :
    (noiseCount (labelDifference i j) : ℝ)/331776=kinetic i j := by
 rw [noise_quotient_certificate,kinetic_difference i j]

theorem probe_rayleigh : lagPairing probe/secondMoment probe=(5/24:ℝ) := by
 rw [probe_values.2.1,probe_values.2.2]
 norm_num
end OperatorDerivativeRewrite.Foundation.WilsonPlaquetteGapCounterexample
