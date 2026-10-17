import Foundation.BrownianMassContinuousLimit

/-! The actual continuous mass limit realizes the independently proved
Tanaka residual at each fixed time. Occupation/support remain separate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianMassLimitIdentification
open InfiniteGaussian GaussianTimeProcess GaussianConditionalIto
open BrownianMassFastSubsequence BrownianMassContinuousLimit BrownianTanakaResidual
open BrownianTanakaApproximation BrownianSmoothMassRealization

theorem coordinate_ae (T : ℝ≥0) :
    (fun ω => limitPath ω T) =ᵐ[gaussianProduct] mass T := by
  have hL := (approximateMass_tendsto T).comp subsequence_strictMono.tendsto_atTop
  have hM := tendstoInMeasure_of_tendsto_Lp hL
  obtain ⟨s, hs, hsae⟩ := hM.exists_seq_tendsto_ae
  filter_upwards [limitPath_tendsto, hsae,
    ae_all_iff.mpr (fun j => approximateMass_coeFn (subsequence j) T)] with ω hp hl hr
  have he : Continuous (fun f : C(ℝ≥0, ℝ) => f T) := by fun_prop
  have ht := (he.continuousAt.tendsto.comp hp).comp hs.tendsto_atTop
  have ht' : Tendsto (fun k => approximateMass (subsequence (s k)) T ω)
      atTop (𝓝 (limitPath ω T)) := by
    simpa only [Function.comp_def, hr] using ht
  exact tendsto_nhds_unique ht' hl

theorem coordinate_memLp (T : ℝ≥0) : MemLp (fun ω => limitPath ω T) 2 gaussianProduct :=
  (Lp.memLp (mass T)).ae_eq (coordinate_ae T).symm

def coordinateClass (T : ℝ≥0) : GaussianL2 := (coordinate_memLp T).toLp _

theorem coordinateClass_eq (T : ℝ≥0) : coordinateClass T = mass T := by
  apply Lp.ext
  exact (MemLp.coeFn_toLp (coordinate_memLp T)).trans (coordinate_ae T)

theorem jointly_measurable : Measurable (fun z : ℝ≥0 × SampleSpace => limitPath z.2 z.1) :=
  continuous_eval.measurable.comp
    ((limitPath_measurable.comp measurable_snd).prodMk measurable_fst)

theorem coordinate_raw_past (T : ℝ≥0) :
    AEStronglyMeasurable[naturalFiltration T] (fun ω => limitPath ω T) gaussianProduct := by
  have h : mass T ∈ pastL2 T :=
    (pastL2 T).sub_mem (GaussianLipschitzIntegrands.valueL2_past absLip T)
      (BrownianSignConditional.terminal_past T)
  change AEStronglyMeasurable[naturalFiltration T] (mass T) gaussianProduct at h
  exact h.congr (coordinate_ae T).symm

theorem tanaka_ae (T : ℝ≥0) : ∀ᵐ ω ∂gaussianProduct,
    |IBMConstructedSources.clockPath ω T| = BrownianSignIntegral.terminal T ω + limitPath ω T := by
  filter_upwards [coordinate_ae T, Lp.coeFn_sub (absoluteValue T)
    (BrownianSignIntegral.terminal T), absoluteValue_coeFn T] with ω hc hs hv
  change mass T ω = absoluteValue T ω - BrownianSignIntegral.terminal T ω at hs
  rw [hc, hs, hv]
  ring

end OperatorDerivativeRewrite.Foundation.BrownianMassLimitIdentification
