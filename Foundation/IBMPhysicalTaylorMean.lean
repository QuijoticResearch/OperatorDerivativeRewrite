import Foundation.IBMClockCubicVariation

/-! Squared Taylor remainders of the ACTUAL reflected physical primitive on
Brownian clock grids vanish in mean. This does not identify the stochastic
integral increment error or assert zero quadratic variation of the correction. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalTaylorMean
open InfiniteGaussian IBMConstructedSources GaussianBrownianQuadraticVariation
open IBMPhysicalWeakWiener IBMPhysicalReflectedPrimitive IBMPhysicalReflectedTaylor
open IBMPhysicalNoiseClock IBMClockCubicVariation
local instance : NormedSpace ℝ Kernel := NormedSpace.restrictScalars ℝ ℂ _
attribute [local instance] IBMPhysicalNegativeEmbedding.realContinuousSMul
attribute [local irreducible] IBMPhysicalReflectedPrimitive.corrected
  IBMPhysicalReflectedPrimitive.slope IBMConstructedSources.clockPath

def spatialRemainder (z : ℝ × ℝ) : ℝ :=
  ‖corrected z.2 - corrected z.1 - (z.2-z.1) • slope z.1‖^2

theorem spatialRemainder_continuous : Continuous spatialRemainder := by
  have hg : Continuous corrected := corrected_C1.continuous
  have hs : Continuous slope := slope_continuous
  exact (((hg.comp continuous_snd).sub (hg.comp continuous_fst)).sub
    ((continuous_snd.sub continuous_fst).smul (hs.comp continuous_fst))).norm.pow 2

def remainder (s t : ℝ≥0) (Y : SampleSpace) : ℝ :=
  spatialRemainder (clockPath Y s, clockPath Y t)

theorem clock_measurable (t : ℝ≥0) : Measurable (fun Y : SampleSpace => clockPath Y t) :=
  (ContinuousMap.measurable_eval _).comp clockPath_measurable

theorem remainder_measurable (s t : ℝ≥0) : Measurable (remainder s t) := by
  have hp : Measurable (fun Y : SampleSpace => (clockPath Y s, clockPath Y t)) :=
    (clock_measurable s).prodMk (clock_measurable t)
  exact spatialRemainder_continuous.measurable.comp hp

def remainderSum (T : ℝ≥0) (n : ℕ) (Y : SampleSpace) : ℝ :=
  ∑ i : Fin (n + 1), remainder (uniformTime T n i.castSucc) (uniformTime T n i.succ) Y

theorem remainderSum_nonnegative (T : ℝ≥0) (n : ℕ) (Y : SampleSpace) :
    0 ≤ remainderSum T n Y :=
  Finset.sum_nonneg fun i _hi => sq_nonneg _

theorem remainderSum_measurable (T : ℝ≥0) (n : ℕ) : Measurable (remainderSum T n) :=
  Finset.measurable_sum _ fun i _hi => remainder_measurable _ _

theorem remainderSum_bound (T : ℝ≥0) (n : ℕ) (Y : SampleSpace) :
    remainderSum T n Y ≤ 16*‖physicalDerivative‖^2 * cubic T n Y :=
  clock_grid_remainder_bound (uniformTime T n) Y

theorem remainderSum_integrable (T : ℝ≥0) (n : ℕ) :
    Integrable (remainderSum T n) gaussianProduct := by
  apply ((cubic_integrable T n).const_mul (16*‖physicalDerivative‖^2)).mono'
    (remainderSum_measurable T n).aestronglyMeasurable
  exact Eventually.of_forall fun Y => by
    rw [Real.norm_of_nonneg (remainderSum_nonnegative T n Y)]
    exact remainderSum_bound T n Y

theorem remainderSum_integral_bound (T : ℝ≥0) (n : ℕ) :
    (∫ Y, remainderSum T n Y ∂gaussianProduct) ≤
      16*‖physicalDerivative‖^2 * ∫ Y, cubic T n Y ∂gaussianProduct := by
  calc
    _ ≤ ∫ Y, 16*‖physicalDerivative‖^2 * cubic T n Y ∂gaussianProduct :=
      integral_mono_ae (remainderSum_integrable T n)
        ((cubic_integrable T n).const_mul _)
        (Eventually.of_forall fun Y => remainderSum_bound T n Y)
    _ = _ := integral_const_mul _ _

theorem remainderSum_mean_tendsto (T : ℝ≥0) :
    Tendsto (fun n => ∫ Y, remainderSum T n Y ∂gaussianProduct) atTop (nhds 0) := by
  apply squeeze_zero (fun n => integral_nonneg (remainderSum_nonnegative T n))
    (fun n => remainderSum_integral_bound T n)
  simpa only [mul_zero] using (cubic_mean_tendsto T).const_mul (16*‖physicalDerivative‖^2)

theorem remainderSum_norm_mean_tendsto (T : ℝ≥0) :
    Tendsto (fun n => ∫ Y, ‖remainderSum T n Y‖ ∂gaussianProduct) atTop (nhds 0) := by
  simpa only [Real.norm_of_nonneg (remainderSum_nonnegative T _ _)] using
    remainderSum_mean_tendsto T

def remainderClass (T : ℝ≥0) (n : ℕ) : Lp ℝ 1 gaussianProduct :=
  (remainderSum_integrable T n).toL1 (remainderSum T n)

theorem remainderClass_ae (T : ℝ≥0) (n : ℕ) :
    remainderClass T n =ᵐ[gaussianProduct] remainderSum T n :=
  (remainderSum_integrable T n).coeFn_toL1

theorem remainderClass_tendsto (T : ℝ≥0) :
    Tendsto (remainderClass T) atTop (nhds 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero, remainderClass, L1.norm_of_fun_eq_integral_norm] using
    remainderSum_norm_mean_tendsto T

end OperatorDerivativeRewrite.Foundation.IBMPhysicalTaylorMean
