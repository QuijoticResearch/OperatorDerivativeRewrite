import Foundation.GaussianPredictableSourceSlices

/-! The actual predictable IBM regularization has the verified bounded
recovery as its almost-every-time source-valued clock slices. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRegularizedPredictableSlices
open InfiniteGaussian GaussianTimeProductL2 GaussianClockValueOperators
open GaussianPredictableSourceSlices GaussianSourceHorizonRegularization
open IBMSchwartzFullReflectedIto IBMClockRegularizedSlope IBMNormalizedClockProfiles
open IBMRegularizedStochasticIdentity
set_option backward.isDefEq.respectTransparency false
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def positiveSlope (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (t : ℝ) : Field :=
  if ht : 0 < t then pointSlope g a n t.toNNReal (Real.toNNReal_pos.mpr ht) else 0

set_option maxHeartbeats 1000000 in
theorem integrand_slices (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    sourceCurry (zeroExtend T (integrand g a n T)) =ᵐ[volume]
      (Ioc (0 : ℝ) (T : ℝ)).indicator (positiveSlope g a n) := by
  have hz := zeroValue_ae T (integrand g a n T)
  change zeroExtend T (integrand g a n T) =ᵐ[timeProbability]
    (PredictableRealL2.horizon T).indicator (integrand g a n T).val at hz
  have hf := (ae_eq_restrict_iff_indicator_ae_eq (PredictableRealL2.horizon_measurable T)).mp
    (field_ae g a n T)
  have hj := hz.trans hf
  have hc := ProductL2Curry.curryEquiv_coeFn volume gaussianProduct (zeroExtend T (integrand g a n T))
  filter_upwards [hc,Measure.ae_ae_of_ae_prod hj] with t hc hj
  change sourceCurry (zeroExtend T (integrand g a n T)) t =ᵐ[gaussianProduct]
    fun ω => zeroExtend T (integrand g a n T) (t,ω) at hc
  by_cases ht : t ∈ Ioc (0 : ℝ) (T : ℝ)
  · rw [indicator_of_mem ht,positiveSlope,dif_pos ht.1]
    apply Lp.ext
    filter_upwards [hc,hj,pointSlope_actual_ae g a n (Real.toNNReal_pos.mpr ht.1)] with ω hc hj hp
    have hzt : (t,ω) ∈ PredictableRealL2.horizon T := ⟨ht,mem_univ _⟩
    exact hc.trans ((hj.trans (indicator_of_mem hzt _)).trans hp.symm)
  · rw [indicator_of_notMem ht]
    apply Lp.ext
    filter_upwards [hc,hj,Lp.coeFn_zero GaussianL2 2 gaussianProduct] with ω hc hj h0
    have hzt : (t,ω) ∉ PredictableRealL2.horizon T := fun h => ht h.1
    exact hc.trans ((hj.trans (indicator_of_notMem hzt _)).trans h0.symm)

/-- This joins the independently constructed predictable field and bounded
endpoint recovery. It is a full SOURCE-valued clock-L2 equality AE in time. -/
theorem stochasticField_slices (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    sourceCurry (zeroExtend T (stochasticField g a n T)) =ᵐ[volume]
      (Ioc (0 : ℝ) (T : ℝ)).indicator (fun t => recoveredSlope g a n t.toNNReal) := by
  apply regularization_slices_of_clock_limit
  filter_upwards [integrand_slices g a n T] with t ht
  by_cases hs : t ∈ Ioc (0 : ℝ) (T : ℝ)
  · rw [ht,indicator_of_mem hs,indicator_of_mem hs,positiveSlope,dif_pos hs.1]
    exact recoveredSlope_chaos_tendsto g a n (Real.toNNReal_pos.mpr hs.1)
  · rw [ht,indicator_of_notMem hs,indicator_of_notMem hs]
    simp only [map_zero,smul_zero,Finset.sum_const_zero]
    exact tendsto_const_nhds

/-- Measurability and L2 realization are obtained from the actual
predictable field, rather than assumed for the varying recovery operator. -/
theorem horizon_recovery_memLp (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    MemLp ((Ioc (0 : ℝ) (T : ℝ)).indicator (fun t => recoveredSlope g a n t.toNNReal))
      2 volume :=
  (memLp_congr_ae (stochasticField_slices g a n T)).mp
    (Lp.memLp (sourceCurry (zeroExtend T (stochasticField g a n T))))

theorem predictable_slice_uniform_energy (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    ∀ᵐ t ∂volume, ‖sourceCurry (zeroExtend T (stochasticField g a n T)) t‖ ^ 2 ≤
      (Ioc (0 : ℝ) (T : ℝ)).indicator
        (fun t => slopeBound g ^ 2 * absoluteMoment / Real.sqrt t) t := by
  filter_upwards [stochasticField_slices g a n T] with t ht
  rw [ht]
  by_cases hs : t ∈ Ioc (0 : ℝ) (T : ℝ)
  · rw [indicator_of_mem hs,indicator_of_mem hs]
    simpa only [Real.toNNReal_of_nonneg hs.1.le,NNReal.coe_mk] using
      recoveredSlope_uniform_energy g a n (Real.toNNReal_pos.mpr hs.1)
  · simp [hs]

theorem predictable_slices_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    ∀ᵐ t ∂volume, Tendsto
      (fun n => sourceCurry (zeroExtend T (stochasticField g a n T)) t) atTop
        (𝓝 ((Ioc (0 : ℝ) (T : ℝ)).indicator
          (fun t => recoveredSlopeLimit g a t.toNNReal) t)) := by
  filter_upwards [ae_all_iff.mpr (fun n => stochasticField_slices g a n T)] with t ht
  simp only [ht]
  by_cases hs : t ∈ Ioc (0 : ℝ) (T : ℝ)
  · simp only [indicator_of_mem hs]
    exact recoveredSlope_tendsto g a t.toNNReal
  · simp only [indicator_of_notMem hs]
    exact tendsto_const_nhds

end OperatorDerivativeRewrite.Foundation.IBMRegularizedPredictableSlices
