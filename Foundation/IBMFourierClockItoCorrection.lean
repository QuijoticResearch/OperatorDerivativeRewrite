import Foundation.ReflectedDampingNativeIntegral
import Foundation.IBMFourierClockClarkOcone

/-! The completed physical-clock Ito correction is a directly constructed
L2 local-time/drift functional. Its original predictable adjoint supplies the
exact difference between terminal Clark--Ocone and the local running field.
Hidden-clock causality only; no unaveraged intrinsic IBM theorem is asserted. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMFourierClockItoCorrection
open InfiniteGaussian GaussianPredictableFull GaussianPredictableAdjoint
open IBMFourierSourceMeanIto
variable (a β w : ℕ → ℝ) (hv : Summable (fun k => |w k|))
  (h4 : Summable (fun k => |w k| * (a k) ^ 4))

def drift (T : ℝ≥0) : GaussianL2 :=
  GaussianReflectedC2Ito.drift (ReflectedDampingSeries.value (weight β w) (rate a))
    (ReflectedDampingSeries.value_C2 _ _ (rate_nonneg a)
      (weight_summable β w hv) (fourth_cost a β w h4))
    (ReflectedDampingSeriesIto.secondConstant (weight β w) (rate a))
    (fun x => by
      rw [ReflectedDampingSeries.value_second _ _ (rate_nonneg a)
        (weight_summable β w hv) (fourth_cost a β w h4)]
      exact ReflectedDampingSeries.second_bound _ _ (rate_nonneg a) (fourth_cost a β w h4) x) T

def correction (T : ℝ≥0) : GaussianL2 :=
  -(∑' k, weight β w k * rate a k) • BrownianMassLimitIdentification.coordinateClass T +
    (1/2 : ℝ) • drift a β w hv h4 T

theorem drift_actual (T : ℝ≥0) : drift a β w hv h4 T =ᵐ[gaussianProduct] fun Y =>
    ∫ s in (0 : ℝ)..(T : ℝ), ∑' k, weight β w k * (rate a k) ^ 2 *
      Real.exp (-rate a k * |IBMConstructedSources.clockPath Y s.toNNReal|) := by
  have hi := GaussianReflectedC2Ito.drift_coeFn
    (ReflectedDampingSeries.value (weight β w) (rate a))
    (ReflectedDampingSeries.value_C2 _ _ (rate_nonneg a)
      (weight_summable β w hv) (fourth_cost a β w h4))
    (ReflectedDampingSeriesIto.secondConstant (weight β w) (rate a))
    (fun x => by
      rw [ReflectedDampingSeries.value_second _ _ (rate_nonneg a)
        (weight_summable β w hv) (fourth_cost a β w h4)]
      exact ReflectedDampingSeries.second_bound _ _ (rate_nonneg a) (fourth_cost a β w h4) x) T
  change (drift a β w hv h4 T : SampleSpace → ℝ) =ᵐ[gaussianProduct] _ at hi
  simpa only [ReflectedDampingSeries.value_second _ _ (rate_nonneg a)
    (weight_summable β w hv) (fourth_cost a β w h4), ReflectedDampingSeries.second,
    GaussianDampedReflectedIto.curvature, abs_abs, mul_assoc] using hi

theorem correction_actual (T : ℝ≥0) : correction a β w hv h4 T =ᵐ[gaussianProduct]
    fun Y => -(∑' k, weight β w k * rate a k) * BrownianMassContinuousLimit.limitPath Y T +
      (1/2 : ℝ) * ∫ s in (0 : ℝ)..(T : ℝ), ∑' k, weight β w k * (rate a k) ^ 2 *
        Real.exp (-rate a k * |IBMConstructedSources.clockPath Y s.toNNReal|) := by
  filter_upwards [Lp.coeFn_add
    (-(∑' k, weight β w k * rate a k) • BrownianMassLimitIdentification.coordinateClass T)
    ((1/2 : ℝ) • drift a β w hv h4 T),
    Lp.coeFn_smul (-(∑' k, weight β w k * rate a k))
      (BrownianMassLimitIdentification.coordinateClass T),
    Lp.coeFn_smul (1/2 : ℝ) (drift a β w hv h4 T),
    MemLp.coeFn_toLp (BrownianMassLimitIdentification.coordinate_memLp T),
    drift_actual a β w hv h4 T] with Y ha hm hd hmass hD
  change correction a β w hv h4 T Y = _ at ha
  change BrownianMassLimitIdentification.coordinateClass T Y =
    BrownianMassContinuousLimit.limitPath Y T at hmass
  rw [ha, Pi.add_apply, hm, hd]
  simp only [Pi.smul_apply, smul_eq_mul, hD]
  rw [hmass]

theorem l2_ito (T : ℝ≥0) : mean a β w T - (∑' k, weight β w k) • gaussianOne =
    itoIntegral (running a β w hv h4 T) + correction a β w hv h4 T := by
  apply Lp.ext
  filter_upwards [actual_ito a β w hv h4 T, correction_actual a β w hv h4 T,
    Lp.coeFn_sub (mean a β w T) ((∑' k, weight β w k) • gaussianOne),
    Lp.coeFn_smul (∑' k, weight β w k) gaussianOne, gaussianOne_coeFn,
    Lp.coeFn_add (itoIntegral (running a β w hv h4 T)) (correction a β w hv h4 T)]
      with Y hi hc hs hm h1 ha
  rw [hs, ha, Pi.sub_apply, Pi.add_apply, hm, Pi.smul_apply, smul_eq_mul, h1, mul_one, hc]
  linear_combination hi

theorem terminal_adjoint (T : ℝ≥0) :
    IBMFourierClockClarkOcone.coefficient (fun k (_ : Unit) => a k) β w (fun _ => T) =
      running a β w hv h4 T + predictableAdjoint (correction a β w hv h4 T) := by
  have h := congrArg predictableAdjoint (l2_ito a β w hv h4 T)
  rw [map_sub, GaussianQuadraticCylinders.predictableAdjoint_constant, sub_zero,
    map_add, predictableAdjoint_integral] at h
  exact h

theorem terminal_eq_running_iff (T : ℝ≥0) :
    IBMFourierClockClarkOcone.coefficient (fun k (_ : Unit) => a k) β w (fun _ => T) =
      running a β w hv h4 T ↔ predictableAdjoint (correction a β w hv h4 T) = 0 := by
  rw [terminal_adjoint a β w hv h4 T, add_eq_left]

theorem correction_brownian (T : ℝ≥0) :
    correction a β w hv h4 T ∈ GaussianBrownianGeneratedSpace.brownianL2 := by
  have h1 : gaussianOne ∈ GaussianBrownianGeneratedSpace.brownianL2 :=
    stronglyMeasurable_const.aestronglyMeasurable.congr gaussianOne_coeFn.symm
  have hm := IBMFourierClockClarkOcone.clockMean_brownian
    (fun k (_ : Unit) => a k) β w (fun _ => T) hv
  have hc : correction a β w hv h4 T = mean a β w T -
      (∑' k, weight β w k) • gaussianOne - itoIntegral (running a β w hv h4 T) := by
    rw [l2_ito a β w hv h4 T]
    abel
  rw [hc]
  exact GaussianBrownianGeneratedSpace.brownianL2.sub_mem
    (GaussianBrownianGeneratedSpace.brownianL2.sub_mem hm
      (GaussianBrownianGeneratedSpace.brownianL2.smul_mem _ h1))
    (GaussianBrownianGeneratedSpace.itoIntegral_mem_brownianL2 _)

theorem correction_reconstruction (T : ℝ≥0) :
    itoIntegral (predictableAdjoint (correction a β w hv h4 T)) =
      correction a β w hv h4 T -
        (∫ Y, correction a β w hv h4 T Y ∂gaussianProduct) • gaussianOne :=
  GaussianBrownianPRP.brownian_representation _ (correction_brownian a β w hv h4 T)

theorem native_running_tendsto (T : ℝ≥0) :
    Tendsto (ReflectedDampingNativeIntegral.native (weight β w) (rate a) (rate_nonneg a) T)
      atTop (𝓝 (running a β w hv h4 T)) :=
  ReflectedDampingNativeIntegral.partial_tendsto (weight β w) (rate a) (rate_nonneg a)
    (weight_summable β w hv) (fourth_cost a β w h4) T

theorem native_integral_tendsto (T : ℝ≥0) :
    Tendsto (fun N => ∑ k ∈ Finset.range N, weight β w k •
      itoIntegral (GaussianDampedReflectedIto.running (rate a k) (rate_nonneg a k) T))
      atTop (𝓝 (itoIntegral (running a β w hv h4 T))) :=
  ReflectedDampingNativeIntegral.integral_tendsto (weight β w) (rate a) (rate_nonneg a)
    (weight_summable β w hv) (fourth_cost a β w h4) T

theorem correction_expectation (T : ℝ≥0) :
    (∫ Y, correction a β w hv h4 T Y ∂gaussianProduct) =
      (∫ Y, mean a β w T Y ∂gaussianProduct) - ∑' k, weight β w k := by
  have h := congrArg (fun F : GaussianL2 => inner ℝ gaussianOne F) (l2_ito a β w hv h4 T)
  rw [inner_sub_right, inner_smul_right, GaussianDeterministicGraphCore.gaussianOne_inner_self,
    mul_one, inner_add_right] at h
  simp only [gaussianOne_inner_eq_integral, itoIntegral_centered, zero_add] at h
  exact h.symm

end OperatorDerivativeRewrite.Foundation.IBMFourierClockItoCorrection
