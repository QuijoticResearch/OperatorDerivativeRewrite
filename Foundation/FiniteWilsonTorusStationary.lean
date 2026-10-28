import Foundation.FiniteWilsonTorusNoise

/-! Actual finite32-state stationary ground transform of the explicit torus
transfer. The ground is constructed, never postulated as an existence axiom. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FiniteWilsonTorusStationary
open FiniteWilsonTorusKernel

def normalizer : ℝ := ∑ i : State,ground i^2

theorem normalizer_pos : 0 < normalizer := by
  apply Finset.sum_pos
  · intro i hi
    exact sq_pos_of_pos (ground_positive i)
  · exact Finset.univ_nonempty

def stationary (i : State) : ℝ := ground i^2/normalizer

def step (i j : State) : ℝ := transfer i j*ground j/(FiniteWilsonTorusGround.value*ground i)

theorem step_positive (i j : State) : 0 < step i j :=
  div_pos (mul_pos (transfer_positive i j) (ground_positive j))
    (mul_pos FiniteWilsonTorusGround.value_pos (ground_positive i))

theorem step_rows (i : State) : (∑ j,step i j)=1 := by
  unfold step
  rw [← Finset.sum_div,ground_eigen,
    div_self (mul_pos FiniteWilsonTorusGround.value_pos (ground_positive i)).ne']

theorem stationary_positive (i : State) : 0 < stationary i :=
  div_pos (sq_pos_of_pos (ground_positive i)) normalizer_pos

theorem stationary_total : (∑ i,stationary i)=1 := by
  unfold stationary
  rw [← Finset.sum_div]
  exact div_self normalizer_pos.ne'

theorem detailed_balance (i j : State) : stationary i*step i j=stationary j*step j i := by
  unfold stationary step
  rw [transfer_symmetric i j]
  field_simp [normalizer_pos.ne',FiniteWilsonTorusGround.value_pos.ne',
    (ground_positive i).ne',(ground_positive j).ne']
  <;> ring

theorem stationary_step (j : State) : (∑ i,stationary i*step i j)=stationary j := by
  simp_rw [detailed_balance]
  rw [← Finset.mul_sum,step_rows,mul_one]

def rowPMF (i : State) : PMF State := PMF.ofFintype (fun j => ENNReal.ofReal (step i j)) (by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => (step_positive i j).le),step_rows]
  norm_num)

def stationaryPMF : PMF State := PMF.ofFintype (fun i => ENNReal.ofReal (stationary i)) (by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (stationary_positive i).le),stationary_total]
  norm_num)

theorem stationary_bind : stationaryPMF.bind rowPMF=stationaryPMF := by
  ext j
  rw [PMF.bind_apply,tsum_fintype]
  simp only [rowPMF,stationaryPMF,PMF.ofFintype_apply]
  simp_rw [← ENNReal.ofReal_mul (stationary_positive _).le]
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun i _ => mul_nonneg (stationary_positive i).le (step_positive i j).le),stationary_step]

theorem bare_stationary_step (j : State) : (∑ i : State,(1/32:ℝ)*kinetic i j)=1/32 := by
  calc
    _ = (1/32:ℝ)*(∑ i : State,kinetic j i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [kinetic_symmetric i j]
    _ = 1/32 := by rw [kinetic_rows,mul_one]

def bareRowPMF (i : State) : PMF State := PMF.ofFintype (fun j => ENNReal.ofReal (kinetic i j)) (by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => (kinetic_positive i j).le),kinetic_rows]
  norm_num)

def bareStationaryPMF : PMF State := PMF.ofFintype (fun _ => ENNReal.ofReal (1/32:ℝ)) (by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun (_i : State) _ => (by norm_num : (0:ℝ) ≤ 1/32))]
  norm_num)

theorem bare_stationary_bind : bareStationaryPMF.bind bareRowPMF=bareStationaryPMF := by
  ext j
  rw [PMF.bind_apply,tsum_fintype]
  simp only [bareRowPMF,bareStationaryPMF,PMF.ofFintype_apply]
  simp_rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/32)]
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun i _ => mul_nonneg (by norm_num : (0:ℝ) ≤ 1/32) (kinetic_positive i j).le),bare_stationary_step]

end OperatorDerivativeRewrite.Foundation.FiniteWilsonTorusStationary
