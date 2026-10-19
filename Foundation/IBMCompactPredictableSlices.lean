import Foundation.IBMCompactClockRecovery
import Foundation.IBMRegularizedTimeLimit

/-! The actual native predictable fields have the bounded endpoint recovery
as their time slices, for every compact C3 kernel. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMCompactPredictableSlices
open InfiniteGaussian GaussianTimeProductL2 GaussianClockValueOperators
open GaussianPredictableSourceSlices GaussianSourceHorizonRegularization
open IBMCompactKernelReflectedIto IBMCompactClockGraph IBMCompactClockRecovery
set_option backward.isDefEq.respectTransparency false
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def stochasticField (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (T : ℝ≥0) : GaussianSourceClockIto.Domain T :=
  sourceRegularization T (integrand g a hc hρ T)

def correction (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (T : ℝ≥0) : Field :=
  IBMRegularizedStochasticIdentity.smoothing (wholeClass g a hc hρ T)

theorem finite_stochastic_identity (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (T : ℝ≥0) :
    IBMRegularizedStochasticIdentity.smoothing (endpointClass g a hc hρ T) =
      GaussianSourceClockIto.integral T (stochasticField g a hc hρ T)+correction g a hc hρ T := by
  rw [finite_kernel_identity,map_add]
  change IBMRegularizedStochasticIdentity.smoothing
    (GaussianSourceClockIto.integral T (integrand g a hc hρ T))+correction g a hc hρ T = _
  rw [IBMRegularizedStochasticIdentity.smoothing_integral]
  rfl

set_option maxHeartbeats 1000000 in
theorem integrand_slices (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (T : ℝ≥0) :
    sourceCurry (zeroExtend T (integrand g a hc hρ T)) =ᵐ[volume]
      (Ioc (0 : ℝ) (T : ℝ)).indicator (fun t => pointSlope g a hc hρ t.toNNReal) := by
  have hz := zeroValue_ae T (integrand g a hc hρ T)
  change zeroExtend T (integrand g a hc hρ T) =ᵐ[timeProbability]
    (PredictableRealL2.horizon T).indicator (integrand g a hc hρ T).val at hz
  have hf := (ae_eq_restrict_iff_indicator_ae_eq (PredictableRealL2.horizon_measurable T)).mp
    (field_ae g a hc hρ T)
  have hj := hz.trans hf
  have hcur := ProductL2Curry.curryEquiv_coeFn volume gaussianProduct
    (zeroExtend T (integrand g a hc hρ T))
  filter_upwards [hcur,Measure.ae_ae_of_ae_prod hj] with t hcur hj
  change sourceCurry (zeroExtend T (integrand g a hc hρ T)) t =ᵐ[gaussianProduct]
    fun ω => zeroExtend T (integrand g a hc hρ T) (t,ω) at hcur
  by_cases ht : t ∈ Ioc (0 : ℝ) (T : ℝ)
  · rw [indicator_of_mem ht]
    apply Lp.ext
    filter_upwards [hcur,hj,pointSlope_ae g a hc hρ t.toNNReal] with ω hcur hj hp
    have hzt : (t,ω) ∈ PredictableRealL2.horizon T := ⟨ht,mem_univ _⟩
    exact hcur.trans ((hj.trans (indicator_of_mem hzt _)).trans hp.symm)
  · rw [indicator_of_notMem ht]
    apply Lp.ext
    filter_upwards [hcur,hj,Lp.coeFn_zero GaussianL2 2 gaussianProduct] with ω hcur hj h0
    have hzt : (t,ω) ∉ PredictableRealL2.horizon T := fun h => ht h.1
    exact hcur.trans ((hj.trans (indicator_of_notMem hzt _)).trans h0.symm)

theorem stochasticField_slices (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (T : ℝ≥0) :
    sourceCurry (zeroExtend T (stochasticField g a hc hρ T)) =ᵐ[volume]
      (Ioc (0 : ℝ) (T : ℝ)).indicator (fun t => recoveredSlope g a hc hρ t.toNNReal) := by
  apply regularization_slices_of_clock_limit
  filter_upwards [integrand_slices g a hc hρ T] with t ht
  by_cases hs : t ∈ Ioc (0 : ℝ) (T : ℝ)
  · rw [ht,indicator_of_mem hs,indicator_of_mem hs]
    exact recoveredSlope_chaos_tendsto g a hc hρ (Real.toNNReal_pos.mpr hs.1)
  · rw [ht,indicator_of_notMem hs,indicator_of_notMem hs]
    simp only [map_zero,smul_zero,Finset.sum_const_zero]
    exact tendsto_const_nhds

theorem predictable_slice_uniform_energy (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ)
    (hpos : ∀ x, 0 ≤ ρ x) (hmass : (∫ x, ρ x) = 1) (T : ℝ≥0) :
    ∀ᵐ t ∂volume, ‖sourceCurry (zeroExtend T (stochasticField g a hc hρ T)) t‖^2 ≤
      IBMRegularizedTimeLimit.majorant g T t := by
  filter_upwards [stochasticField_slices g a hc hρ T] with t ht
  rw [ht]
  by_cases hs : t ∈ Ioc (0 : ℝ) (T : ℝ)
  · rw [indicator_of_mem hs,IBMRegularizedTimeLimit.majorant,indicator_of_mem hs]
    simpa only [Real.toNNReal_of_nonneg hs.1.le,NNReal.coe_mk] using
      recoveredSlope_uniform_energy g a hc hρ hpos hmass (Real.toNNReal_pos.mpr hs.1)
  · simp [IBMRegularizedTimeLimit.majorant,hs]

end OperatorDerivativeRewrite.Foundation.IBMCompactPredictableSlices
