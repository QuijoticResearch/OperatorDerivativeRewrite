import Foundation.HigherHeatAnalyticCylinderDomain
import Mathlib.Analysis.SpecificLimits.Basic

/-! Common analytic cylinder domains and their precise time-topology boundary. -/
noncomputable section
open scoped BigOperators NNReal ENNReal Topology

namespace OperatorDerivativeRewrite.Foundation.HigherHeatAnalyticTimeObstruction
open HigherHeatPolynomialCylinders HigherHeatPolynomialCoordinates HigherHeatPolynomialPathDomain
open HigherHeatAnalyticCylinderDomain MultivariateFactorialDomain
open Filter
open scoped Topology ENNReal

theorem position_core_norm (n : ℕ) (i : Fin (size n)) : ‖core (positionCylinder n i)‖ = 1 := by
  rw [core_norm]
  change cylinderSeminorm (cylinderOf n (positionPolynomial n i)) = 1
  rw [cylinderSeminorm_grid, encode_apply, ← coordinates_X, AlgEquiv.symm_apply_apply]
  simp only [MvPolynomial.X, polynomial_monomial, Finsupp.degree_single,
    Nat.factorial_one, Nat.cast_one, one_mul]
  rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1)]
  norm_num

def firstIndex (n : ℕ) : Fin (size n) := ⟨0, HigherHeatDyadicLaws.gridSize_pos n⟩

def firstPosition (n : ℕ) : Cylinder := positionCylinder n (firstIndex n)

theorem first_time (n : ℕ) :
    HigherHeatContinuousCylinders.sampleTime n (firstIndex n) = (1/2 : ℝ)^n := by
  simp [HigherHeatContinuousCylinders.sampleTime, HigherHeatDyadicLaws.time,
    HigherHeatDyadicLaws.duration, HigherHeatDyadicLaws.gridSize_pow, firstIndex]

theorem first_time_tendsto :
    Tendsto (fun n => HigherHeatContinuousCylinders.sampleTime n (firstIndex n)) atTop (𝓝 0) := by
  simp only [first_time]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)

theorem first_path_tendsto (ω : Path) :
    Tendsto (fun n => HigherHeatPolynomialPathDomain.realize (firstPosition n) ω) atTop (𝓝 0) := by
  have ht := ω.val.continuous.continuousAt.tendsto.comp first_time_tendsto
  have he (n : ℕ) : HigherHeatPolynomialPathDomain.realize (firstPosition n) ω =
      ω.val (HigherHeatContinuousCylinders.sampleTime n (firstIndex n)) :=
    realize_position n (firstIndex n) ω
  simpa only [he, Function.comp_def, ω.property] using ht

theorem first_core_norm (n : ℕ) : ‖core (firstPosition n)‖ = 1 :=
  position_core_norm n (firstIndex n)

theorem first_core_not_tendsto_zero : ¬ Tendsto (fun n => core (firstPosition n)) atTop (𝓝 0) := by
  intro h
  have hn := h.norm
  simp only [first_core_norm, norm_zero] at hn
  have hz : (1:ℝ)=0 := tendsto_nhds_unique tendsto_const_nhds hn
  norm_num at hz

end OperatorDerivativeRewrite.Foundation.HigherHeatAnalyticTimeObstruction
