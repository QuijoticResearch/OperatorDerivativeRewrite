import Foundation.IBMConstructedSources
import Foundation.GaussianTimeProcess

/-! A positive-probability clock-backtracking witness on the actual constructed
Brownian clock. This is independent of any stochastic-integral convention. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMClockBacktracking
open InfiniteGaussian GaussianTimeProcess
set_option backward.isDefEq.respectTransparency false

theorem gaussian_interval_pos (a b : ℝ) (hab : a < b) :
    0 < gaussianReal 0 1 (Ioo a b) := by
  apply bot_lt_iff_ne_bot.mpr
  intro hz
  have hv := gaussianReal_absolutelyContinuous' (0 : ℝ) (by norm_num : (1 : ℝ≥0) ≠ 0) hz
  have hp : (0 : ℝ≥0∞) < volume (Ioo a b) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  exact hp.ne' hv

def witness : Set SampleSpace :=
  (process 1) ⁻¹' Ioo 1 2 ∩ (process 2 - process 1) ⁻¹' Ioo (-1) (-1/2)

theorem witness_positive : 0 < gaussianProduct witness := by
  have hi := process_hasIndepIncrements.indepFun_eval_sub
    (show (0 : ℝ≥0) ≤ 1 by norm_num) (show (1 : ℝ≥0) ≤ 2 by norm_num) process_zero_ae
  have h := hi.measure_inter_preimage_eq_mul (Ioo 1 2) (Ioo (-1) (-1/2))
    measurableSet_Ioo measurableSet_Ioo
  have hd : nndist (2 : ℝ) (1 : ℝ) = (1 : ℝ≥0) := by
    apply NNReal.eq
    norm_num [coe_nndist, Real.dist_eq]
  have hl : HasLaw (process 2 - process 1) (gaussianReal 0 1) gaussianProduct := by
    have hh := process_increment_hasLaw 1 2
    norm_num only [NNReal.coe_ofNat, NNReal.coe_one] at hh
    rwa [hd] at hh
  have hx : gaussianProduct ((process 1) ⁻¹' Ioo 1 2) = gaussianReal 0 1 (Ioo 1 2) :=
    (process_hasLaw 1).measure_eq (p := fun x => x ∈ Ioo (1 : ℝ) 2) measurableSet_Ioo
  have hy : gaussianProduct ((process 2 - process 1) ⁻¹' Ioo (-1) (-1/2)) =
      gaussianReal 0 1 (Ioo (-1) (-1/2)) :=
    hl.measure_eq (p := fun x => x ∈ Ioo (-1 : ℝ) (-1/2)) measurableSet_Ioo
  change 0 < gaussianProduct ((process 1) ⁻¹' Ioo 1 2 ∩
    (process 2 - process 1) ⁻¹' Ioo (-1) (-1/2))
  rw [h, hx, hy]
  exact ENNReal.mul_pos (ne_of_gt (gaussian_interval_pos 1 2 (by norm_num)))
    (ne_of_gt (gaussian_interval_pos (-1) (-1/2) (by norm_num)))

theorem witness_backtracks {ω : SampleSpace} (h : ω ∈ witness) :
    |process 2 ω| < |process 1 ω| := by
  change (1 < process 1 ω ∧ process 1 ω < 2) ∧
    (-1 < process 2 ω - process 1 ω ∧ process 2 ω - process 1 ω < -1/2) at h
  rw [abs_of_pos (by linarith : 0 < process 2 ω), abs_of_pos (by linarith : 0 < process 1 ω)]
  linarith

theorem backtracking_positive :
    0 < gaussianProduct {ω | |process 2 ω| < |process 1 ω|} :=
  witness_positive.trans_le (measure_mono fun _ h => witness_backtracks h)

theorem actual_clock_backtracking_positive :
    0 < gaussianProduct {ω | |IBMConstructedSources.clockPath ω 2| <
      |IBMConstructedSources.clockPath ω 1|} := by
  have he : {ω | |IBMConstructedSources.clockPath ω 2| < |IBMConstructedSources.clockPath ω 1|}
      =ᵐ[gaussianProduct] {ω | |process 2 ω| < |process 1 ω|} := by
    filter_upwards [IBMConstructedSources.clockPath_coordinate_ae 1,
      IBMConstructedSources.clockPath_coordinate_ae 2] with ω h1 h2
    simp only [h1, h2]
  rw [measure_congr he]
  exact backtracking_positive

end OperatorDerivativeRewrite.Foundation.IBMClockBacktracking
