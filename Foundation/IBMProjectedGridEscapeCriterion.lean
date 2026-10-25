import Foundation.IBMCenteredClockVariance

/-! A sufficient escape criterion for the ORIGINAL projected IBM output.
The actual source-energy growth and clock bound remain explicit obligations. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMProjectedGridEscapeCriterion
open InfiniteGaussian IBMTimeAveragedObservable IBMRawGridCompensation
open IBMRawGridSecondChaos IBMCenteredRawGrid IBMJointIntrinsicDerivative

theorem native_energy_dominates {h : ℝ≥0} {n : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hq : 0 < ‖sourceGrid h n‖^2)
    (hv : ‖centeredClock h n‖^2 ≤ C*‖sourceGrid h n‖^2) :
    ‖sourceGrid h n‖^2/(1+C) ≤ ‖jointDivergence (gridInput h n)‖^2 := by
  have hi := native_energy_lower_bound h n
  have hc : 0 < 1+C := by linarith
  apply (div_le_iff₀ hc).mpr
  apply (mul_le_mul_iff_left₀ hq).mp
  calc
    _ = (‖sourceGrid h n‖^2)^2 := by ring
    _ ≤ ‖jointDivergence (gridInput h n)‖^2*
        (‖sourceGrid h n‖^2+‖centeredClock h n‖^2) := hi
    _ ≤ _ := by
      have hb := mul_le_mul_of_nonneg_left (add_le_add_left hv (‖sourceGrid h n‖^2))
        (sq_nonneg ‖jointDivergence (gridInput h n)‖)
      nlinarith [hb]

theorem native_norm_escape (h : ℕ → ℝ≥0) (n : ℕ → ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hq : Tendsto (fun N => ‖sourceGrid (h N) (n N)‖^2) atTop atTop)
    (hv : ∀ᶠ N in atTop, ‖centeredClock (h N) (n N)‖^2 ≤
      C*‖sourceGrid (h N) (n N)‖^2) :
    Tendsto (fun N => ‖jointDivergence (gridInput (h N) (n N))‖) atTop atTop := by
  have hc : 0 < 1+C := by linarith
  have hl := hq.atTop_div_const hc
  have hs : Tendsto (fun N => ‖jointDivergence (gridInput (h N) (n N))‖^2) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hl
    filter_upwards [hv,hq.eventually (eventually_gt_atTop (0:ℝ))] with N hvN hqN
    exact native_energy_dominates hC hqN hvN
  have ht := Real.tendsto_sqrt_atTop.comp hs
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _)] using ht

theorem no_native_L2_limit (h : ℕ → ℝ≥0) (n : ℕ → ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hq : Tendsto (fun N => ‖sourceGrid (h N) (n N)‖^2) atTop atTop)
    (hv : ∀ᶠ N in atTop, ‖centeredClock (h N) (n N)‖^2 ≤
      C*‖sourceGrid (h N) (n N)‖^2) (v : IntrinsicSpace) :
    ¬ Tendsto (fun N => jointDivergence (gridInput (h N) (n N))) atTop (𝓝 v) := by
  intro ht
  exact not_tendsto_nhds_of_tendsto_atTop (native_norm_escape h n hC hq hv) _ ht.norm

theorem bounded_clock_implies_escape (h : ℕ → ℝ≥0) (n : ℕ → ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hq : Tendsto (fun N => ‖sourceGrid (h N) (n N)‖^2) atTop atTop)
    (hv : ∀ᶠ N in atTop, ‖centeredClock (h N) (n N)‖^2 ≤ C) :
    Tendsto (fun N => ‖jointDivergence (gridInput (h N) (n N))‖) atTop atTop := by
  apply native_norm_escape h n hC hq
  filter_upwards [hv,hq.eventually (eventually_ge_atTop (1:ℝ))] with N hvN hqN
  exact hvN.trans (by nlinarith)

end OperatorDerivativeRewrite.Foundation.IBMProjectedGridEscapeCriterion
