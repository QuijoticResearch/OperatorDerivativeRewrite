import Foundation.IBMPhysicalCorrectionLocalTime
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Actual continuous Tanaka local-time square sums vanish in strong L1.
The integrable dominator is the actual terminal local time squared. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianLocalTimeSquares
open InfiniteGaussian GaussianBrownianQuadraticVariation BrownianMassContinuousLimit

def pathSquares (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) : ℝ :=
  ∑ i : Fin (n+1), (f (uniformTime T n i.succ)-f (uniformTime T n i.castSucc))^2

theorem grid_mem (T : ℝ≥0) (n : ℕ) (i : Fin (n+2)) : uniformTime T n i ∈ Icc 0 T := by
  refine ⟨bot_le, ?_⟩
  have h := uniformTime_monotone T n (Fin.le_last i)
  rwa [(uniformTime_endpoints T n).2] at h

theorem increment_sum (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) :
    (∑ i : Fin (n+1), (f (uniformTime T n i.succ)-f (uniformTime T n i.castSucc))) =
      f T-f 0 := by
  rw [Finset.sum_sub_distrib]
  have h := Fin.sum_univ_succ (fun i : Fin (n+2) => f (uniformTime T n i))
  have h' := Fin.sum_univ_castSucc (fun i : Fin (n+2) => f (uniformTime T n i))
  rw [(uniformTime_endpoints T n).1] at h
  rw [(uniformTime_endpoints T n).2] at h'
  linarith

theorem pathSquares_bound (f : ℝ≥0 → ℝ) (hf : Monotone f) (h0 : f 0 = 0)
    (T : ℝ≥0) (n : ℕ) (K : ℝ)
    (hK : ∀ i : Fin (n+1), f (uniformTime T n i.succ)-f (uniformTime T n i.castSucc) ≤ K) :
    pathSquares f T n ≤ K*f T := by
  calc
    _ ≤ ∑ i : Fin (n+1), K*(f (uniformTime T n i.succ)-f (uniformTime T n i.castSucc)) := by
      apply Finset.sum_le_sum
      intro i _hi
      have hn := sub_nonneg.mpr (hf (uniformTime_monotone T n (Fin.castSucc_le_succ i)))
      nlinarith [hK i]
    _ = _ := by rw [← Finset.mul_sum, increment_sum, h0, sub_zero]

theorem pathSquares_terminal_bound (f : ℝ≥0 → ℝ) (hf : Monotone f) (h0 : f 0 = 0)
    (T : ℝ≥0) (n : ℕ) : pathSquares f T n ≤ (f T)^2 := by
  have h := pathSquares_bound f hf h0 T n (f T) (fun i => by
    have ha := hf (grid_mem T n i.castSucc).1
    have hb := hf (grid_mem T n i.succ).2
    rw [h0] at ha
    linarith)
  simpa only [pow_two] using h

theorem pathSquares_tendsto (f : ℝ≥0 → ℝ) (hc : Continuous f) (hf : Monotone f)
    (h0 : f 0 = 0) (T : ℝ≥0) : Tendsto (pathSquares f T) atTop (nhds 0) := by
  have hn : 0 ≤ f T := by simpa only [h0] using hf (show (0 : ℝ≥0) ≤ T from bot_le)
  have huc : UniformContinuousOn f (Icc 0 T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hc.continuousOn
  have hu := Metric.uniformContinuousOn_iff.mp huc
  have hm : Tendsto (fun n : ℕ => (T : ℝ)/(n+1)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hpos : 0 < f T+1 := by linarith
  obtain ⟨δ, hδ, hd⟩ := hu (ε/(f T+1)) (div_pos hε hpos)
  filter_upwards [(tendsto_order.mp hm).2 δ hδ] with n hmesh
  have hb := pathSquares_bound f hf h0 T n (ε/(f T+1)) (fun i => by
    have hdist : dist (uniformTime T n i.succ) (uniformTime T n i.castSucc) < δ := by
      change dist (uniformTime T n i.succ : ℝ) (uniformTime T n i.castSucc : ℝ) < δ
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr
        (show (uniformTime T n i.castSucc : ℝ) ≤ uniformTime T n i.succ from
          uniformTime_monotone T n (Fin.castSucc_le_succ i))), uniformTime_step]
      exact hmesh
    have he := hd _ (grid_mem T n i.succ) _ (grid_mem T n i.castSucc) hdist
    rw [Real.dist_eq] at he
    exact (le_abs_self _).trans he.le)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (Finset.sum_nonneg fun i _hi => sq_nonneg _)]
  have he := div_mul_cancel₀ ε (ne_of_gt hpos)
  have hp := div_pos hε hpos
  nlinarith

def squares (T : ℝ≥0) (n : ℕ) (Y : SampleSpace) : ℝ := pathSquares (limitPath Y) T n

theorem squares_nonnegative (T : ℝ≥0) (n : ℕ) (Y : SampleSpace) : 0 ≤ squares T n Y := by
  unfold squares pathSquares
  exact Finset.sum_nonneg fun i _hi => sq_nonneg _

theorem squares_measurable (T : ℝ≥0) (n : ℕ) : Measurable (squares T n) := by
  unfold squares pathSquares
  exact Finset.measurable_sum _ fun (i : Fin (n+1)) _hi =>
    (((ContinuousMap.measurable_eval (uniformTime T n i.succ)).comp limitPath_measurable).sub
      ((ContinuousMap.measurable_eval (uniformTime T n i.castSucc)).comp limitPath_measurable)).pow_const 2

theorem squares_bound (T : ℝ≥0) (n : ℕ) : ∀ᵐ Y ∂gaussianProduct,
    squares T n Y ≤ (limitPath Y T)^2 := by
  filter_upwards [limitPath_properties] with Y hp
  exact pathSquares_terminal_bound (limitPath Y) hp.2.1 hp.1 T n

theorem terminal_integrable (T : ℝ≥0) : Integrable (fun Y => (limitPath Y T)^2) gaussianProduct :=
  (BrownianMassLimitIdentification.coordinate_memLp T).integrable_sq

theorem squares_integrable (T : ℝ≥0) (n : ℕ) : Integrable (squares T n) gaussianProduct := by
  apply (terminal_integrable T).mono' (squares_measurable T n).aestronglyMeasurable
  filter_upwards [squares_bound T n] with Y hY
  rwa [Real.norm_of_nonneg (squares_nonnegative T n Y)]

theorem squares_pointwise_tendsto (T : ℝ≥0) : ∀ᵐ Y ∂gaussianProduct,
    Tendsto (fun n => squares T n Y) atTop (nhds 0) := by
  filter_upwards [limitPath_properties] with Y hp
  exact pathSquares_tendsto (limitPath Y) (limitPath Y).continuous hp.2.1 hp.1 T

theorem squares_mean_tendsto (T : ℝ≥0) :
    Tendsto (fun n => ∫ Y, squares T n Y ∂gaussianProduct) atTop (nhds 0) := by
  have h := tendsto_integral_of_dominated_convergence (fun Y => (limitPath Y T)^2)
    (F := fun n Y => squares T n Y) (f := fun _ => (0 : ℝ))
    (fun n => (squares_measurable T n).aestronglyMeasurable) (terminal_integrable T)
    (fun n => (squares_bound T n).mono fun Y hY => by
      rwa [Real.norm_of_nonneg (squares_nonnegative T n Y)]) (squares_pointwise_tendsto T)
  simpa only [integral_zero] using h

def squaresClass (T : ℝ≥0) (n : ℕ) : Lp ℝ 1 gaussianProduct :=
  (squares_integrable T n).toL1 (squares T n)

theorem squaresClass_ae (T : ℝ≥0) (n : ℕ) : squaresClass T n =ᵐ[gaussianProduct] squares T n :=
  (squares_integrable T n).coeFn_toL1

theorem squaresClass_tendsto (T : ℝ≥0) : Tendsto (squaresClass T) atTop (nhds 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero, squaresClass, L1.norm_of_fun_eq_integral_norm,
    Real.norm_of_nonneg (squares_nonnegative T _ _)] using squares_mean_tendsto T

end OperatorDerivativeRewrite.Foundation.BrownianLocalTimeSquares
