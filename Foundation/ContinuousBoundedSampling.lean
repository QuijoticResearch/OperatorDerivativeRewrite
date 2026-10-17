import Foundation.StoppingTimeRounding
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-! Bounded optional sampling for actual continuous real martingales.
Countable-range sampling and uniform integrability supply the limiting step;
neither a right-continuous filtration nor an independent random clock is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.ContinuousBoundedSampling
open StoppingTimeRounding
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  (ℱ : Filtration ℝ≥0 m) (M : ℝ≥0 → Ω → ℝ)
  (hM : Martingale M ℱ μ) (hc : ∀ ω, Continuous (fun t => M t ω))
  (τ : Ω → ℝ≥0) (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
  (N : ℕ) (hN : ∀ ω, τ ω ≤ N)

def sampled (n : ℕ) (ω : Ω) : ℝ := M (rounded n (τ ω)) ω

theorem stoppedValue_coe : stoppedValue M (fun ω => (τ ω : WithTop ℝ≥0)) =
    fun ω => M (τ ω) ω := by
  funext ω
  rfl

include hM hτ hN in
theorem sampled_ae_condExp (n : ℕ) :
    sampled M τ n =ᵐ[μ] μ[M (N : ℝ≥0) |
      (rounded_isStoppingTime ℱ τ hτ n).measurableSpace] := by
  have hs := hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
    (rounded_isStoppingTime ℱ τ hτ n)
    (fun ω => show (rounded n (τ ω) : WithTop ℝ≥0) ≤ (N : ℝ≥0) from
      WithTop.coe_le_coe.mpr (rounded_bounded n (τ ω) (hN ω)))
    (rounded_countable_range n τ)
  rw [stoppedValue_coe] at hs
  exact hs

include hM hτ hN in
theorem sampled_uniformIntegrable : UniformIntegrable (sampled M τ) 1 μ := by
  have hu := (hM.integrable (N : ℝ≥0)).uniformIntegrable_condExp
    (fun n => (rounded_isStoppingTime ℱ τ hτ n).measurableSpace_le)
  exact hu.ae_eq (fun n => (sampled_ae_condExp μ ℱ M hM τ hτ N hN n).symm)

include hc in
theorem sampled_ae_tendsto : ∀ᵐ ω ∂μ,
    Tendsto (fun n => sampled M τ n ω) atTop (𝓝 (M (τ ω) ω)) :=
  Eventually.of_forall (fun ω => (hc ω).continuousAt.tendsto.comp (rounded_tendsto (τ ω)))

include hM hc hτ hN in
theorem stopped_integrable : Integrable (fun ω => M (τ ω) ω) μ :=
  (sampled_uniformIntegrable μ ℱ M hM τ hτ N hN).integrable_of_ae_tendsto
    (sampled_ae_tendsto μ M hc τ)

include hM hc hτ hN in
theorem sampled_L1_tendsto :
    Tendsto (fun n => eLpNorm (sampled M τ n-(fun ω => M (τ ω) ω)) 1 μ) atTop (𝓝 0) := by
  have hu := sampled_uniformIntegrable μ ℱ M hM τ hτ N hN
  exact tendsto_Lp_finite_of_tendsto_ae le_rfl (by simp)
    hu.aestronglyMeasurable (memLp_one_iff_integrable.mpr (stopped_integrable μ ℱ M hM hc τ hτ N hN))
    hu.1 (sampled_ae_tendsto μ M hc τ)

include hM hc hτ hN in
theorem stopped_ae_condExp :
    (fun ω => M (τ ω) ω) =ᵐ[μ] μ[M (N : ℝ≥0) | hτ.measurableSpace] := by
  have hi := stopped_integrable μ ℱ M hM hc τ hτ N hN
  have hu := sampled_uniformIntegrable μ ℱ M hM τ hτ N hN
  have hL := sampled_L1_tendsto μ ℱ M hM hc τ hτ N hN
  have hs : Measurable[hτ.measurableSpace] (fun ω => M (τ ω) ω) := by
    simpa only [stoppedValue_coe] using
      measurable_stoppedValue (hM.stronglyAdapted.isStronglyProgressive_of_continuous hc) hτ
  apply ae_eq_condExp_of_forall_setIntegral_eq hτ.measurableSpace_le (hM.integrable (N : ℝ≥0))
    (fun _ _ _ => hi.integrableOn) _ hs.stronglyMeasurable.aestronglyMeasurable
  intro A hA _
  have hlin : Tendsto (fun n => ∫⁻ ω, ‖sampled M τ n ω-M (τ ω) ω‖ₑ ∂μ) atTop (𝓝 0) := by
    convert hL using 1
    funext n
    rw [eLpNorm_one_eq_lintegral_enorm ((hu.aestronglyMeasurable n).sub hi.aestronglyMeasurable)]
    rfl
  have ht := tendsto_setIntegral_of_L1 (fun ω => M (τ ω) ω) hi.aestronglyMeasurable
    (Eventually.of_forall fun n => memLp_one_iff_integrable.mp (hu.memLp n)) hlin A
  have he (n : ℕ) : (∫ ω in A, sampled M τ n ω ∂μ) = ∫ ω in A, M (N : ℝ≥0) ω ∂μ := by
    rw [integral_congr_ae (ae_restrict_of_ae (sampled_ae_condExp μ ℱ M hM τ hτ N hN n))]
    exact setIntegral_condExp (rounded_isStoppingTime ℱ τ hτ n).measurableSpace_le
      (hM.integrable (N : ℝ≥0))
      ((hτ.measurableSpace_mono (rounded_isStoppingTime ℱ τ hτ n)
        (fun ω => WithTop.coe_le_coe.mpr (le_rounded n (τ ω)))) A hA)
  exact tendsto_nhds_unique ht (by simp only [he]; exact tendsto_const_nhds)

include hM hc hτ hN in
theorem stopped_expectation :
    (∫ ω, M (τ ω) ω ∂μ) = ∫ ω, M (N : ℝ≥0) ω ∂μ := by
  rw [integral_congr_ae (stopped_ae_condExp μ ℱ M hM hc τ hτ N hN)]
  exact integral_condExp hτ.measurableSpace_le

end OperatorDerivativeRewrite.Foundation.ContinuousBoundedSampling
