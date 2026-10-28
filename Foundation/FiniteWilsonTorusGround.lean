import Foundation.YMPositiveKernel
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.Order.IntermediateValue

/-! Constructive positive eigenstate for a four-orbit homogeneous torus
candidate. The block is explicit; its complete microscopic32-state Wilson
noise/gauge quotient identification is a separate obligation, not an axiom. -/
noncomputable section
open scoped Matrix
namespace OperatorDerivativeRewrite.Foundation.FiniteWilsonTorusGround
abbrev Orbit := Fin 4

def block : Matrix Orbit Orbit ℝ :=
  !![3177/2048,765/512,675/1024,225/2048;
     765/2048,257/512,255/1024,85/2048;
     675/2048,255/512,289/1024,75/2048;
     225/2048,85/512,75/1024,353/18432]

def polynomial (x : ℝ) : ℝ :=
  589824*x^4-1388800*x^3+284192*x^2-5425*x+9

theorem root_exists : ∃ x : ℝ, 2 ≤ x ∧ x ≤ 9/4 ∧ polynomial x = 0 := by
  have hc : Continuous polynomial := by unfold polynomial; fun_prop
  have he : (0:ℝ) ∈ Set.Icc (polynomial 2) (polynomial (9/4)) := by
    norm_num [polynomial, Set.mem_Icc]
  obtain ⟨x,hx,hzero⟩ := intermediate_value_Icc (by norm_num : (2:ℝ) ≤ 9/4) hc.continuousOn he
  exact ⟨x,hx.1,hx.2,hzero⟩

def value : ℝ := Classical.choose root_exists

theorem value_bounds : 2 ≤ value ∧ value ≤ 9/4 :=
  ⟨(Classical.choose_spec root_exists).1,(Classical.choose_spec root_exists).2.1⟩

theorem value_polynomial : polynomial value = 0 := (Classical.choose_spec root_exists).2.2

theorem value_pos : 0 < value := lt_of_lt_of_le (by norm_num) value_bounds.1

/-- A scaled adjugate column. Positivity will be proved on the whole root interval. -/
def vectorAt (x : ℝ) : Orbit → ℝ :=
  ![4718592*x^3-3790592*x^2+108928*x-353,
    1762560*x^2-122400*x+765,
    1555200*x^2+86400*x-675,
    518400*x^2-2025]

theorem vectorAt_positive (x : ℝ) (hx : 2 ≤ x) (i : Orbit) : 0 < vectorAt x i := by
  have h2 : 4 ≤ x^2 := by nlinarith [sq_nonneg (x-2)]
  have h3 : 2*x^2 ≤ x^3 := by nlinarith [mul_nonneg (by linarith : 0 ≤ x-2) (sq_nonneg x)]
  have hlin : 2*x ≤ x^2 := by nlinarith [mul_nonneg (by linarith : 0 ≤ x) (by linarith : 0 ≤ x-2)]
  fin_cases i <;> norm_num [vectorAt] <;> nlinarith

def ground : Orbit → ℝ := vectorAt value

theorem ground_positive (i : Orbit) : 0 < ground i := vectorAt_positive value value_bounds.1 i

/-- All four polynomial eigen-equations, before choosing a root. -/
theorem adjugate_identity (x : ℝ) (i : Orbit) :
    (∑ j, block i j*vectorAt x j)-x*vectorAt x i = if i=0 then -8*polynomial x else 0 := by
  fin_cases i <;> norm_num [block,vectorAt,polynomial,Fin.sum_univ_succ] <;> ring

theorem ground_eigen (i : Orbit) : (∑ j, block i j*ground j)=value*ground i := by
  have h := adjugate_identity value i
  rw [value_polynomial] at h
  simp only [mul_zero,ite_self] at h
  change (∑ j, block i j*ground j)-value*ground i=0 at h
  linarith

def multiplicity : Orbit → ℝ := ![1,4,2,1]

theorem multiplicity_positive (i : Orbit) : 0 < multiplicity i := by
  fin_cases i <;> norm_num [multiplicity]

theorem block_positive (i j : Orbit) : 0 < block i j := by
  fin_cases i <;> fin_cases j <;> norm_num [block]

theorem weighted_symmetry (i j : Orbit) : multiplicity i*block i j=multiplicity j*block j i := by
  fin_cases i <;> fin_cases j <;> norm_num [block,multiplicity]

def normalizer : ℝ := ∑ i, multiplicity i*ground i^2

theorem normalizer_pos : 0 < normalizer := by
  apply Finset.sum_pos
  · intro i hi
    exact mul_pos (multiplicity_positive i) (sq_pos_of_pos (ground_positive i))
  · exact Finset.univ_nonempty

def stationary (i : Orbit) : ℝ := multiplicity i*ground i^2/normalizer

def step (i j : Orbit) : ℝ := block i j*ground j/(value*ground i)

theorem step_positive (i j : Orbit) : 0 < step i j :=
  div_pos (mul_pos (block_positive i j) (ground_positive j)) (mul_pos value_pos (ground_positive i))

theorem step_rows (i : Orbit) : (∑ j, step i j)=1 := by
  unfold step
  rw [← Finset.sum_div,ground_eigen,div_self (mul_pos value_pos (ground_positive i)).ne']

theorem stationary_positive (i : Orbit) : 0 < stationary i :=
  div_pos (mul_pos (multiplicity_positive i) (sq_pos_of_pos (ground_positive i))) normalizer_pos

theorem stationary_total : (∑ i, stationary i)=1 := by
  unfold stationary
  rw [← Finset.sum_div]
  exact div_self normalizer_pos.ne'

theorem detailed_balance (i j : Orbit) : stationary i*step i j=stationary j*step j i := by
  unfold stationary step
  have hw := weighted_symmetry i j
  field_simp [normalizer_pos.ne',value_pos.ne',(ground_positive i).ne',(ground_positive j).ne']
  nlinarith [hw]

theorem stationary_step (j : Orbit) : (∑ i,stationary i*step i j)=stationary j := by
  simp_rw [detailed_balance]
  rw [← Finset.mul_sum,step_rows,mul_one]

def rowPMF (i : Orbit) : PMF Orbit := PMF.ofFintype (fun j => ENNReal.ofReal (step i j)) (by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => (step_positive i j).le),step_rows]
  norm_num)

def stationaryPMF : PMF Orbit := PMF.ofFintype (fun i => ENNReal.ofReal (stationary i)) (by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (stationary_positive i).le),stationary_total]
  norm_num)

/-- The flat winding trial's candidate ratio lies strictly above1/4. Its
microscopic numerator/centering identification is deliberately not asserted here. -/
theorem flat_trial_scalar_margin : (1/4:ℝ) < (225/256)/value := by
  apply (lt_div_iff₀ value_pos).mpr
  nlinarith [value_bounds.2]

end OperatorDerivativeRewrite.Foundation.FiniteWilsonTorusGround
