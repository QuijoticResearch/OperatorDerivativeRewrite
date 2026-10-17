import Foundation.BrownianVolatilitySquare

/-! Native slices and a quantitative failure of the stochastic-volatility square rule. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianVolatilitySquareDefect
open InfiniteGaussian GaussianTimeSpaceHermite GaussianHermiteIntegrand
open GaussianHermiteTimeIntegral GaussianHermiteTimeKernel GaussianWeightedTimeHermite
open GaussianPredictableFull GaussianTimeProductL2 GaussianProductDerivative
open BrownianVolatilitySquare GaussianHermiteRepresentation
open GaussianPredictableAdjoint
set_option backward.isDefEq.respectTransparency false

theorem square_mean (T : ℝ≥0) :
    (∫ ω, terminalSquare T ω ∂gaussianProduct) = (T : ℝ)^2/2 := by
  have h := congrArg (fun X : GaussianL2 => inner ℝ gaussianOne X) (corrected_representation T)
  rw [inner_sub_right, real_inner_smul_right,
    GaussianDeterministicGraphCore.gaussianOne_inner_self, mul_one,
    gaussianOne_inner_eq_integral, gaussianOne_inner_eq_integral, itoIntegral_centered] at h
  linarith

theorem candidate_slices (T : ℝ≥0) :
    scalarCurry (candidate T : TimeProbabilityL2) =ᵐ[volume]
      (Ioc 0 (T : ℝ)).indicator (fun t => (brownianCore t.toNNReal 3 : GaussianL2) +
        (2*t) • (brownianCore t.toNNReal 1 : GaussianL2)) := by
  change scalarCurry ((hermiteIntegrand 3 T : TimeProbabilityL2) +
    (2 : ℝ) • (weightedIntegrand (fun t => t) (fun _ => 1) 1 T : TimeProbabilityL2)) =ᵐ[volume] _
  rw [map_add, map_smul]
  filter_upwards [Lp.coeFn_add (scalarCurry (hermiteIntegrand 3 T))
      ((2 : ℝ) • scalarCurry (weightedIntegrand (fun t => t) (fun _ => 1) 1 T)),
    Lp.coeFn_smul (2 : ℝ) (scalarCurry (weightedIntegrand (fun t => t) (fun _ => 1) 1 T)),
    hermiteIntegrand_slices 3 T,
    weightedIntegrand_slices (fun t => t) (fun _ => 1) continuous_const hasDerivAt_id 1 T]
    with t ha hs h3 hw
  rw [ha, Pi.add_apply, hs, Pi.smul_apply, h3, hw]
  by_cases ht : t ∈ Ioc 0 (T : ℝ)
  · simp only [horizonValue, indicator_of_mem ht, smul_smul]
  · simp [horizonValue, ht]

theorem running_coefficient (t : ℝ≥0) (r : ℝ) :
    ((brownianCore t 3 : GaussianL2) + (2*r) • (brownianCore t 1 : GaussianL2))
      =ᵐ[gaussianProduct] fun ω =>
        (2*driver t ω+2*(r-t))*GaussianTimeProcess.process t ω := by
  filter_upwards [Lp.coeFn_add (brownianCore t 3 : GaussianL2)
      ((2*r) • (brownianCore t 1 : GaussianL2)),
    Lp.coeFn_smul (2*r) (brownianCore t 1 : GaussianL2),
    Lp.coeFn_smul (1/2 : ℝ) (brownianCore t 2 : GaussianL2),
    brownianCore_coeFn t 1, brownianCore_coeFn t 2, brownianCore_coeFn t 3]
      with ω ha hs hd h1 h2 h3
  have hm : driver t ω = (1/2 : ℝ) * value 2 (GaussianTimeProcess.process t ω) t := by
    change ((1/2 : ℝ) • (brownianCore t 2 : GaussianL2)) ω = _
    rw [hd, Pi.smul_apply, h2]
    rfl
  rw [ha, Pi.add_apply, hs, Pi.smul_apply, h1, h3, hm]
  exact polynomial_correct _ _ _

theorem correction_slices (T : ℝ≥0) :
    scalarCurry (correction T : TimeProbabilityL2) =
      (2 : ℝ) • tailField (fun t => t) continuous_id 1 T := by
  change scalarCurry ((2 : ℝ) • (integratedHermite (fun _ => 1) 1 T : TimeProbabilityL2)) = _
  rw [map_smul, integratedHermite_slices (fun t => t) (fun _ => 1)
    continuous_id continuous_const hasDerivAt_id]

theorem correction_norm_sq (T : ℝ≥0) : ‖correction T‖^2 = (T : ℝ)^4/3 := by
  have hn : ‖correction T‖^2 = ‖scalarCurry (correction T : TimeProbabilityL2)‖^2 := by
    rw [scalarCurry.norm_map]
    rfl
  rw [hn, correction_slices, BochnerL2Dominated.norm_sq_integral]
  calc
    _ = ∫ t, (Ioc 0 (T : ℝ)).indicator (fun t => 4*t*((T : ℝ)-t)^2) t := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul (2 : ℝ) (tailField (fun t => t) continuous_id 1 T),
        tailField_coeFn (fun t => t) continuous_id 1 T] with t hs ht
      rw [hs, Pi.smul_apply, ht]
      by_cases h : t ∈ Ioc 0 (T : ℝ)
      · simp only [indicator_of_mem h, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
          brownianCore_norm_sq, Nat.factorial_one, Nat.cast_one, one_mul, pow_one,
          Real.coe_toNNReal _ h.1.le]
        ring
      · simp [h]
    _ = ∫ t in 0..(T : ℝ), 4*t*((T : ℝ)-t)^2 := by
      rw [integral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le T.coe_nonneg]
    _ = _ := by
      have hd (t : ℝ) : HasDerivAt
          (fun t => 2*(T : ℝ)^2*t^2-(8/3 : ℝ)*T*t^3+t^4)
          (4*t*((T : ℝ)-t)^2) t := by
        convert ((((hasDerivAt_id t).pow 2).const_mul (2*(T : ℝ)^2)).sub
          (((hasDerivAt_id t).pow 3).const_mul ((8/3 : ℝ)*T))).add
          ((hasDerivAt_id t).pow 4) using 1 <;> (try funext x) <;> simp <;> ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
        ((continuous_const.mul continuous_id).mul
          ((continuous_const.sub continuous_id).pow 2) |>.intervalIntegrable _ _)]
      simp
      ring

theorem terminal_defect (T : ℝ≥0) :
    terminalSquare T - ((T : ℝ)^2/2) • gaussianOne - itoIntegral (candidate T) =
      itoIntegral (correction T) := by
  rw [← corrected_representation, ← map_sub, correction_identity]

theorem defect_eq_integrated_quadratic (T : ℝ≥0) :
    terminalSquare T - ((T : ℝ)^2/2) • gaussianOne - itoIntegral (candidate T) =
      ∫ t in 0..(T : ℝ), (brownianCore t.toNNReal 2 : GaussianL2) := by
  rw [terminal_defect, correction, map_smul,
    integral_integratedHermite (fun _ => (1 : ℝ)) continuous_const]
  norm_num [smul_smul]

theorem terminal_defect_norm_sq (T : ℝ≥0) :
    ‖terminalSquare T - ((T : ℝ)^2/2) • gaussianOne - itoIntegral (candidate T)‖^2 =
      (T : ℝ)^4/3 := by
  rw [terminal_defect, itoIntegral_norm, correction_norm_sq]

theorem candidate_fails (T : ℝ≥0) (hT : 0 < T) :
    itoIntegral (candidate T) ≠ terminalSquare T - ((T : ℝ)^2/2) • gaussianOne := by
  intro h
  have he := terminal_defect_norm_sq T
  rw [h, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] at he
  have hp : 0 < (T : ℝ)^4/3 := by positivity
  linarith

end OperatorDerivativeRewrite.Foundation.BrownianVolatilitySquareDefect
