import Foundation.IBMSchwartzSlopeLowerBound
import Foundation.BrownianZeroOccupation

/-! A necessary condition for actual all-chaos native Schwartz inputs to be
Cauchy. This is proved on the ORIGINAL horizon measure via an actual a.e.
convergent L2 subsequence, not by interchanging pointwise and L2 limits. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzNativeCauchyCriterion
open InfiniteGaussian IBMShiftedJetMoments IBMQuarticPrimitiveLimit
open IBMSchwartzFullReflectedIto BrownianClockWeightedEnergy

def meanLimit (g : SchwartzMap ℝ ℝ) (a r : ℝ) : ℝ := M g a (baseCoefficient r) 1 0

theorem meanLimit_continuous (g : SchwartzMap ℝ ℝ) (a : ℝ) :
    Continuous (meanLimit g a) :=
  (IBMSchwartzPhysicalSlope.mean_continuous g a 1).comp
    (firstChaosEmbedding.toContinuousLinearMap.adjoint.continuous.comp
      IBMContinuousScenery.sourceScenery_continuous)

theorem native_cauchy_forces_mean_zero (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0)
    (h : CauchySeq (fun n => integrand g a n T)) :
    ∀ᵐ z ∂PredictableRealL2.horizonMeasure T gaussianProduct,
      meanLimit g a |sigma z| = 0 := by
  have hf : CauchySeq (fun n => IBMSchwartzFullReflectedIto.field g a n T) := by
    rw [Metric.cauchySeq_iff] at h ⊢
    exact h
  obtain ⟨v,hv⟩ := cauchySeq_tendsto_of_complete hf
  obtain ⟨ns,hns,ha⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  have hall : ∀ᵐ z ∂PredictableRealL2.horizonMeasure T gaussianProduct,
      ∀ j, IBMSchwartzFullReflectedIto.field g a (ns j) T z =
        signedSlope g a (ns j) (sigma z) :=
    ae_all_iff.mpr (fun j => field_ae g a (ns j) T)
  filter_upwards [ha,hall,BrownianClockWeightedEnergy.sigma_nonzero T] with z hz he hsig
  by_contra hm
  have hsign : ‖BrownianSignIntegral.signum (sigma z)‖ = 1 := by
    rw [Real.norm_eq_abs]
    have hs := BrownianSignIntegral.signum_sq hsig
    nlinarith [abs_nonneg (BrownianSignIntegral.signum (sigma z)),
      sq_abs (BrownianSignIntegral.signum (sigma z))]
  have hn : Tendsto (fun j => ‖IBMSchwartzSourceSecondDerivative.spatialSlope g a (ns j)
      |sigma z|‖) atTop (𝓝 ‖v z‖) := by
    have hn := hz.norm
    simpa only [he,signedSlope,norm_smul,hsign,one_mul] using hn
  have hesc := (IBMSchwartzSlopeLowerBound.spatial_norm_escape g a |sigma z| hm).comp
    hns.tendsto_atTop
  exact not_tendsto_nhds_of_tendsto_atTop hesc _ hn

theorem correction_cauchy_forces_mean_zero (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0)
    (h : CauchySeq (fun n => IBMSchwartzNativeJointIto.correction g a n T)) :
    ∀ᵐ z ∂PredictableRealL2.horizonMeasure T gaussianProduct,
      meanLimit g a |sigma z| = 0 := by
  have hs := (IBMSchwartzNativeJointIto.correction_cauchy_iff g a T).mp h
  have hu : CauchySeq (fun n => integrand g a n T) := by
    simpa only [Metric.cauchySeq_iff,IBMSchwartzNativeJointIto.scalarInput,
      (IBMSchwartzNativeJointIto.flatten T).isometry.dist_eq] using hs
  exact native_cauchy_forces_mean_zero g a T hu

theorem meanLimit_zero (g : SchwartzMap ℝ ℝ) (a : ℝ) :
    meanLimit g a 0 = IBMCorrectionStein.jet g 1 a := by
  have hz : IBMContinuousScenery.sourceScenery 0 = 0 := by
    apply norm_eq_zero.mp
    simpa using IBMRandomTimeHilbert.sourceScenery_norm_sq 0
  have hb : baseCoefficient 0 = 0 := by simp only [baseCoefficient,hz,map_zero]
  rw [meanLimit,hb,moment_zero]
  calc
    _ = ∫ _ : SampleSpace, IBMCorrectionStein.jet g 1 a ∂gaussianProduct := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_zero ℝ 2 gaussianProduct] with X hX
      simp only [map_zero,hX,Pi.zero_apply,IBMCorrectionStein.shiftedJet,add_zero]
    _ = _ := by simp

theorem native_cauchy_forces_origin_zero (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0)
    (hT : 0 < T) (h : CauchySeq (fun n => integrand g a n T)) :
    IBMCorrectionStein.jet g 1 a = 0 := by
  have hm : MeasurableSet {z : ℝ × SampleSpace | meanLimit g a |sigma z| = 0} :=
    measurableSet_eq_fun ((meanLimit_continuous g a).measurable.comp
      (continuous_abs.measurable.comp sigma_measurable)) measurable_const
  have hz := native_cauchy_forces_mean_zero g a T h
  rw [PredictableRealL2.horizonMeasure_eq_product] at hz
  have hy := (Measure.ae_ae_comm hm).mp ((Measure.ae_prod_iff_ae_ae hm).mp hz)
  have hzero : ∀ᵐ Y ∂gaussianProduct, IBMConstructedSources.clockPath Y 0 = 0 :=
    (IBMConstructedSources.clockPath_coordinate_ae 0).trans GaussianTimeProcess.process_zero_ae
  obtain ⟨Y,hY,h0⟩ := (hy.and hzero).exists
  let f : ℝ → ℝ := fun s => meanLimit g a |IBMConstructedSources.clockPath Y s.toNNReal|
  have hf : Continuous f := (meanLimit_continuous g a).comp
    (((IBMConstructedSources.clockPath Y).continuous.comp continuous_real_toNNReal).abs)
  have hrep : f =ᵐ[(volume : Measure ℝ).restrict (Icc 0 (T : ℝ))] fun _ => (0 : ℝ) := by
    rw [← Measure.restrict_congr_set (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := (T : ℝ)))]
    exact hY
  have he := Measure.eqOn_of_ae_eq hrep hf.continuousOn continuousOn_const
    (show Icc (0 : ℝ) T ⊆ closure (interior (Icc (0 : ℝ) T)) by
      rw [closure_interior_Icc (show (0 : ℝ) ≠ T from ne_of_lt hT)])
  have he0 := he (show (0 : ℝ) ∈ Icc (0 : ℝ) T from ⟨le_rfl,T.coe_nonneg⟩)
  simpa only [f,Real.toNNReal_zero,h0,abs_zero,meanLimit_zero] using he0

theorem native_not_cauchy (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) (hT : 0 < T)
    (hg : IBMCorrectionStein.jet g 1 a ≠ 0) :
    ¬ CauchySeq (fun n => integrand g a n T) :=
  fun h => hg (native_cauchy_forces_origin_zero g a T hT h)

theorem correction_not_cauchy (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) (hT : 0 < T)
    (hg : IBMCorrectionStein.jet g 1 a ≠ 0) :
    ¬ CauchySeq (fun n => IBMSchwartzNativeJointIto.correction g a n T) := by
  intro h
  have hs := (IBMSchwartzNativeJointIto.correction_cauchy_iff g a T).mp h
  apply native_not_cauchy g a T hT hg
  simpa only [Metric.cauchySeq_iff,IBMSchwartzNativeJointIto.scalarInput,
    (IBMSchwartzNativeJointIto.flatten T).isometry.dist_eq] using hs

theorem integral_not_cauchy (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) (hT : 0 < T)
    (hg : IBMCorrectionStein.jet g 1 a ≠ 0) :
    ¬ CauchySeq (fun n => IBMIntrinsicOperators.clockDerivative.adjoint
      ⟨IBMSchwartzNativeJointIto.field g a n T,
        IBMSchwartzNativeJointIto.clock_mem g a n T⟩) := by
  intro h
  apply native_not_cauchy g a T hT hg
  simpa only [Metric.cauchySeq_iff,IBMSchwartzNativeJointIto.clock_value,
    IBMTimeAveragedObservable.jointRealization.isometry.dist_eq,integralValue,
    (GaussianSourceClockIto.integral T).isometry.dist_eq] using h

end OperatorDerivativeRewrite.Foundation.IBMSchwartzNativeCauchyCriterion
