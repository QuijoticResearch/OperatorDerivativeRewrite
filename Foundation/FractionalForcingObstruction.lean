import Foundation.FractionalForcingKernel

/-! The actual zero-generator forcing response rules out stronger mean-square
power regularity at the initial time. No sample-path Holder conclusion is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Topology
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.FractionalForcingObstruction
open FractionalForcingKernel

/-- Every exponent exceeding the actual variance exponent fails on every
positive initial interval, for every proposed real bound constant. -/
theorem no_higher_initial_power_bound (α : ℝ) (hα : 1/2 < α)
    (p : ℝ) (hp : 2*α-1 < p) (C δ : ℝ) (hδ : 0 < δ) :
    ∃ t : ℝ≥0, 0 < t ∧ (t : ℝ) < δ ∧ t ≤ 1 ∧
      C * (t : ℝ)^p < ‖stochasticResponse α hα t - stochasticResponse α hα 0‖^2 := by
  let d : ℝ := (Real.Gamma α)^2 * (2*α-1)
  have hd : 0 < d := mul_pos
    (sq_pos_of_pos (Real.Gamma_pos_of_pos (by linarith))) (by linarith)
  have hc : Continuous (fun x : ℝ => C * x^(p-(2*α-1))) :=
    continuous_const.mul (Real.continuous_rpow_const (by linarith))
  have ht : Tendsto (fun x : ℝ => C * x^(p-(2*α-1)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa [Real.zero_rpow (by linarith : p-(2*α-1) ≠ 0)] using
      (hc.tendsto (0 : ℝ)).mono_left
        (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds (0 : ℝ) from inf_le_left)
  have hsmall := ht.eventually (eventually_lt_nhds (inv_pos.mpr hd))
  have hpos : ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < x := self_mem_nhdsWithin
  have hδ' : ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0), x < δ :=
    (eventually_lt_nhds hδ).filter_mono inf_le_left
  have hone : ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0), x < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono inf_le_left
  obtain ⟨x, hxp, hxd, hx1, hxc⟩ := (hpos.and (hδ'.and (hone.and hsmall))).exists
  refine ⟨⟨x, hxp.le⟩, hxp, hxd, hx1.le, ?_⟩
  rw [stochasticResponse_zero, sub_zero, stochasticResponse_norm_sq]
  have hr : 0 < x^(2*α-1) := Real.rpow_pos_of_pos hxp _
  have hm := mul_lt_mul_of_pos_right hxc hr
  have he : x^(p-(2*α-1)) * x^(2*α-1) = x^p := by
    rw [← Real.rpow_add hxp, sub_add_cancel]
  rw [mul_assoc, he] at hm
  change C * x^p < x^(2*α-1) / d
  simpa only [div_eq_mul_inv, mul_comm] using hm

/-- In particular, orders below one cannot satisfy an O(t) initial variance bound. -/
theorem no_initial_brownian_variance_bound (α : ℝ) (hα : 1/2 < α)
    (hα1 : α < 1) (C δ : ℝ) (hδ : 0 < δ) :
    ∃ t : ℝ≥0, 0 < t ∧ (t : ℝ) < δ ∧ t ≤ 1 ∧
      C * (t : ℝ) < ‖stochasticResponse α hα t - stochasticResponse α hα 0‖^2 := by
  simpa only [Real.rpow_one] using
    no_higher_initial_power_bound α hα 1 (by linarith) C δ hδ

end OperatorDerivativeRewrite.Foundation.FractionalForcingObstruction
