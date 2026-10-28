import Foundation.SU2LagEventCorrelation
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open OperatorDerivativeRewrite.Foundation.QuaternionSU2Representation
open OperatorDerivativeRewrite.Foundation.SU2LoopEquilibrium
open OperatorDerivativeRewrite.Foundation.SU2ResidualEntropy
open OperatorDerivativeRewrite.Foundation.SU2EventMixing
open OperatorDerivativeRewrite.Foundation.SU2LagEventCorrelation
namespace OperatorDerivativeRewrite.Foundation.SU2CouplingIteration

theorem residual_power_exp_bound (r : ℝ) (n : ℕ) :
    (residualCoefficient r)^n ≤ ENNReal.ofReal (Real.exp (-(n:ℝ) * reset r)) := by
  have hbase : 1 - reset r ≤ Real.exp (-reset r) := by
    linarith [Real.add_one_le_exp (-reset r)]
  have hpow := pow_le_pow_left₀ (sub_nonneg.mpr (reset_lt_one r).le) hbase n
  have hex : Real.exp (-reset r)^n = Real.exp (-(n:ℝ)*reset r) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hex] at hpow
  rw [residualCoefficient, ← ENNReal.ofReal_pow (sub_nonneg.mpr (reset_lt_one r).le)]
  exact ENNReal.ofReal_le_ofReal hpow

theorem coupling_iteration_bound (r t : ℝ) (n : ℕ) (hn : t ≤ (n:ℝ)*reset r) :
    (residualCoefficient r)^n ≤ ENNReal.ofReal (Real.exp (-t)) := by
  refine (residual_power_exp_bound r n).trans (ENNReal.ofReal_le_ofReal ?_)
  apply Real.exp_le_exp.mpr
  linarith

theorem lag_event_macro_bound (r t : ℝ) (n : ℕ) (hn : t ≤ (n:ℝ)*reset r)
    (A B : Set SU2) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    stationaryLagLaw r n (A ×ˢ B) ≤ equilibriumLaw r A * equilibriumLaw r B +
      equilibriumLaw r A * ENNReal.ofReal (Real.exp (-t)) ∧
    equilibriumLaw r A * equilibriumLaw r B ≤ stationaryLagLaw r n (A ×ˢ B) +
      equilibriumLaw r A * ENNReal.ofReal (Real.exp (-t)) := by
  have he := mul_le_mul_of_nonneg_left (coupling_iteration_bound r t n hn)
    (show 0 ≤ equilibriumLaw r A from bot_le)
  exact ⟨(lag_event_upper r n A B hA hB).trans (add_le_add le_rfl he),
    (lag_event_lower r n A B hA hB).trans (add_le_add le_rfl he)⟩

theorem sufficient_step_count (r t : ℝ) (n : ℕ)
    (hn : 2*t*Real.exp (4*|r|) ≤ (n:ℝ)) : t ≤ (n:ℝ)*reset r := by
  have he : (2*t*Real.exp (4*|r|))*reset r = t := by
    rw [reset]
    have hex : Real.exp (4*|r|) * Real.exp (-(4*|r|)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      2*t*Real.exp (4*|r|) * (Real.exp (-(4*|r|))/2) =
          t * (Real.exp (4*|r|) * Real.exp (-(4*|r|))) := by ring
      _ = t := by rw [hex, mul_one]
  rw [← he]
  exact mul_le_mul_of_nonneg_right hn (reset_pos r).le

theorem physical_distance_event_bound (r a m : ℝ) (n : ℕ)
    (hscale : m*a ≤ reset r) (A B : Set SU2)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    stationaryLagLaw r n (A ×ˢ B) ≤ equilibriumLaw r A * equilibriumLaw r B +
      equilibriumLaw r A * ENNReal.ofReal (Real.exp (-(m*((n:ℝ)*a)))) ∧
    equilibriumLaw r A * equilibriumLaw r B ≤ stationaryLagLaw r n (A ×ˢ B) +
      equilibriumLaw r A * ENNReal.ofReal (Real.exp (-(m*((n:ℝ)*a)))) := by
  apply lag_event_macro_bound r (m*((n:ℝ)*a)) n ?_ A B hA hB
  have h := mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  nlinarith

end OperatorDerivativeRewrite.Foundation.SU2CouplingIteration
