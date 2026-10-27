import Foundation.PhysicalHeatFiniteTimeCovariance
import Foundation.AnisotropicStableEndpoint

/-!
# Positive finite-time covariance need not increase in Loewner order

For the ordinary quadratic heat symbol on one coordinate of the three-torus,
two character frequencies and weights `1, -2` give a negative quadratic form
for the difference of finite-time Gamma matrices between times `log 2` and
`2 log 2`. Each individual matrix is positive semidefinite by the previous
Schoenberg theorem. The exact witness is rational after evaluating the heat
exponentials. Thus covariance positivity alone supplies no time-monotonicity
or Bakry curvature conclusion.
-/

open OperatorDerivativeRewrite.Foundation
open FiniteFourierDifferentialTrace FourierCovarianceCriterion
open FiniteStableGamma.Core PhysicalHeatChain AnchoredCovariance
open scoped NNReal

noncomputable section

namespace OperatorDerivativeRewrite.Foundation.PhysicalHeatCovarianceNonmonotonicity

def quadRate (k : Wave) : ℝ≥0 := ((k 0).natAbs : ℝ≥0) ^ 2

private theorem quadRate_coe (k : Wave) : (quadRate k : ℝ) = (k 0 : ℝ)^2 := by
  simp [quadRate, sq_abs]

theorem quadRate_covariance : CovarianceSymbol (fun k => (quadRate k : ℝ)) := by
  convert AnisotropicStableEndpoint.axis_covariance_two 0 using 1
  funext k
  simp [quadRate_coe, AnisotropicStableGamma.axisSymbol, sq_abs]

def ka : Wave := Pi.single 0 (1 : ℤ)
def kb : Wave := Pi.single 0 (-2 : ℤ)

private theorem rates : quadRate ka = 1 ∧ quadRate kb = 4 ∧ quadRate (kb-ka) = 9 := by
  norm_num [quadRate, ka, kb, Pi.single_apply]

def halfTime : ℝ≥0 := ⟨Real.log 2, Real.log_nonneg (by norm_num)⟩

private theorem exp_halfTime (n : ℕ) :
    Real.exp (-((halfTime : ℝ) * (n : ℝ))) = (1/2 : ℝ)^n := by
  change Real.exp (-(Real.log 2 * (n : ℝ))) = _
  rw [show -(Real.log 2 * (n : ℝ)) = (n : ℝ) * (-Real.log 2) by ring,
    Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

private theorem exp_doubleTime (n : ℕ) :
    Real.exp (-(((halfTime + halfTime : ℝ≥0) : ℝ) * (n : ℝ))) =
      (1/2 : ℝ)^(2*n) := by
  have h : -(((halfTime + halfTime : ℝ≥0) : ℝ) * (n : ℝ)) =
      -((halfTime : ℝ) * ((2*n : ℕ) : ℝ)) := by
    change -((Real.log 2 + Real.log 2) * (n : ℝ)) =
      -(Real.log 2 * (((2*n : ℕ) : ℝ)))
    push_cast
    ring
  rw [h, exp_halfTime]

def sampleWave : Fin 2 → Wave := ![ka, kb]
def sampleWeights : Fin 2 → ℝ := ![1, -2]

theorem covariance_increment_energy_eq :
    energy (fun i j : Fin 2 =>
      kernel (heatIncrementSymbol quadRate (halfTime+halfTime))
        (sampleWave i) (sampleWave j) -
      kernel (heatIncrementSymbol quadRate halfTime)
        (sampleWave i) (sampleWave j)) sampleWeights = -(16897/131072 : ℝ) := by
  simp only [energy, Fin.sum_univ_two]
  simp [sampleWave, sampleWeights, kernel, heatIncrementSymbol,
    quadRate, ka, kb]
  have h1 : Real.exp (-(halfTime : ℝ)) = 1/2 := by
    simpa using exp_halfTime 1
  have h2 : Real.exp (-(halfTime : ℝ) + -(halfTime : ℝ)) = 1/4 := by
    rw [Real.exp_add, h1]
    norm_num
  have h4 : Real.exp (-((halfTime : ℝ) * 4)) = 1/16 := by
    convert exp_halfTime 4 using 1; norm_num
  have h9 : Real.exp (-((halfTime : ℝ) * 9)) = 1/512 := by
    convert exp_halfTime 9 using 1; norm_num
  have h8 : Real.exp (-(((halfTime+halfTime : ℝ≥0) : ℝ) * 4)) = 1/256 := by
    convert exp_doubleTime 4 using 1; norm_num
  have h18 : Real.exp (-(((halfTime+halfTime : ℝ≥0) : ℝ) * 9)) = 1/262144 := by
    convert exp_doubleTime 9 using 1; norm_num
  norm_num only [show (2 : ℝ)^2 = 4 by norm_num, show (3 : ℝ)^2 = 9 by norm_num] at *
  simp only [NNReal.coe_add] at h8 h18
  rw [h1, h2, h4, h9, h8, h18]
  norm_num

theorem negative_covariance_increment :
    energy (fun i j : Fin 2 =>
      kernel (heatIncrementSymbol quadRate (halfTime+halfTime))
        (sampleWave i) (sampleWave j) -
      kernel (heatIncrementSymbol quadRate halfTime)
        (sampleWave i) (sampleWave j)) sampleWeights < 0 := by
  rw [covariance_increment_energy_eq]
  norm_num

theorem nonmonotone_matrix :
    ¬ Matrix.PosSemidef (fun i j : Fin 2 =>
      kernel (heatIncrementSymbol quadRate (halfTime+halfTime))
        (sampleWave i) (sampleWave j) -
      kernel (heatIncrementSymbol quadRate halfTime)
        (sampleWave i) (sampleWave j)) := by
  intro h
  have hE : 0 ≤ energy (fun i j : Fin 2 =>
      kernel (heatIncrementSymbol quadRate (halfTime+halfTime))
        (sampleWave i) (sampleWave j) -
      kernel (heatIncrementSymbol quadRate halfTime)
        (sampleWave i) (sampleWave j)) sampleWeights := by
    simpa only [energy, dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
      Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
      h.dotProduct_mulVec_nonneg sampleWeights
  exact (not_le_of_gt negative_covariance_increment) hE

theorem quadRate_zero : quadRate 0 = 0 := by simp [quadRate]

theorem exists_nonmonotone_heat_covariance :
    ∃ (r : Wave → ℝ≥0), CovarianceSymbol (fun k => (r k : ℝ)) ∧ r 0 = 0 ∧
      ∃ (s t : ℝ≥0), s < t ∧
        ¬ Matrix.PosSemidef (fun i j : Fin 2 =>
          kernel (heatIncrementSymbol r t) (sampleWave i) (sampleWave j) -
          kernel (heatIncrementSymbol r s) (sampleWave i) (sampleWave j)) := by
  refine ⟨quadRate, quadRate_covariance, quadRate_zero,
    halfTime, halfTime+halfTime, ?_, nonmonotone_matrix⟩
  have h : 0 < halfTime := by
    change (0 : ℝ) < Real.log 2
    exact Real.log_pos (by norm_num)
  exact lt_add_of_pos_right _ h

end OperatorDerivativeRewrite.Foundation.PhysicalHeatCovarianceNonmonotonicity
