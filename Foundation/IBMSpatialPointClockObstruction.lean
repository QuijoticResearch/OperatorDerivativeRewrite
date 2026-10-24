import Foundation.IBMSpatialPointClockRealization

/-! The PARTICULAR native signed-Dirac clock integral and whole correction
have physical H^-1 limits but no ordinary joint-probability L2 limits. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialPointClockObstruction
open InfiniteGaussian GaussianTimeHilbert IBMSpatialPointClockEnergy
open IBMPhysicalNoiseClock IBMPhysicalNoiseCalculus IBMPhysicalNoiseVectors
open IBMPhysicalNegativeEmbedding IBMSpatialPointClockRealization IBMFirstSourceClockGraph
local instance : InnerProductSpace ℝ IBMPhysicalWeakWiener.Kernel :=
  InnerProductSpace.rclikeToReal ℂ _
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable

def endpoint (n : ℕ) (T : ℝ≥0) : Lp TimeHilbert 2 gaussianProduct :=
  mollifiedKernel n T-Lp.const 2 gaussianProduct (convolutionKernel (IBMMollifier.kernel n) 0)

theorem endpoint_tendsto (T : ℝ≥0) :
    Tendsto (fun n => endpoint n T) atTop (𝓝 (sourceKernel T)) := by
  have hc := (Lp.constL 2 gaussianProduct ℝ).continuous.tendsto _ |>.comp (mollifier_kernel_tendsto 0)
  have h0 : (Lp.constL 2 gaussianProduct ℝ) (vector 0) =
      (0 : Lp TimeHilbert 2 gaussianProduct) := by rw [vector_zero, map_zero]
  rw [h0] at hc
  have hz : Tendsto (fun n => Lp.const 2 gaussianProduct
      (convolutionKernel (IBMMollifier.kernel n) 0)) atTop (𝓝 (0 : Lp TimeHilbert 2 gaussianProduct)) := by
    simpa only [Function.comp_def, Lp.constL_apply] using hc
  simpa only [endpoint, sub_zero] using (mollifiedKernel_tendsto T).sub hz

def correction (n : ℕ) (T : ℝ≥0) : Lp TimeHilbert 2 gaussianProduct :=
  endpoint n T-integralValue n T

theorem endpoint_embedding (n : ℕ) (T : ℝ≥0) :
    embedding.compLpL 2 gaussianProduct (endpoint n T) = IBMPhysicalPointKernelIto.endpoint n T := by
  rw [endpoint, map_sub, IBMPhysicalPointKernelIto.endpoint]
  congr 1

theorem correction_embedding (n : ℕ) (T : ℝ≥0) :
    embedding.compLpL 2 gaussianProduct (correction n T) = IBMPhysicalPointKernelIto.correction n T := by
  rw [correction, map_sub, endpoint_embedding, integral_embedding]
  rfl

theorem integral_hminus_tendsto (T : ℝ≥0) :
    Tendsto (fun n => embedding.compLpL 2 gaussianProduct (integralValue n T)) atTop
      (𝓝 (IBMPhysicalPointClockIntegral.limitIntegralValue T)) := by
  simpa only [integral_embedding] using IBMPhysicalPointClockIntegral.integralValue_tendsto T

theorem correction_hminus_tendsto (T : ℝ≥0) :
    Tendsto (fun n => embedding.compLpL 2 gaussianProduct (correction n T)) atTop
      (𝓝 (IBMPhysicalPointKernelIto.correctionLimit T)) := by
  simpa only [correction_embedding] using IBMPhysicalPointKernelIto.correction_tendsto T

theorem correction_norm_escape (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => ‖correction n T‖) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  have he := (endpoint_tendsto T).norm.eventually
    (gt_mem_nhds (lt_add_one ‖sourceKernel T‖))
  have hi := (integral_norm_escape T hT).eventually
    (eventually_ge_atTop (b+‖sourceKernel T‖+1))
  filter_upwards [he, hi] with n he hi
  have hn : ‖integralValue n T‖ ≤ ‖endpoint n T‖+‖correction n T‖ := by
    have hh := norm_sub_le (endpoint n T) (correction n T)
    have heq : endpoint n T-correction n T = integralValue n T := by
      unfold correction
      abel
    rwa [heq] at hh
  linarith

def realize : Lp TimeHilbert 2 gaussianProduct →ₗᵢ[ℝ]
    Lp ℝ 2 IBMSourceLaws.jointMeasure :=
  (ProductL2Curry.swap gaussianProduct gaussianProduct).comp
    ((ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm.toLinearIsometry.comp
      IBMClockPhysicalOccupation.noiseLift)

theorem realize_sections (U : Lp TimeHilbert 2 gaussianProduct) : ∀ᵐ Y ∂gaussianProduct,
    (fun X => realize U (X,Y)) =ᵐ[gaussianProduct]
      IBMPhysicalNoiseRealization.physicalNoise (U Y) := by
  have hs := Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp
    (ProductL2Curry.swap_coeFn gaussianProduct gaussianProduct
      ((ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm
        (IBMClockPhysicalOccupation.noiseLift U)))
  filter_upwards [ae_ae_of_ae_prod hs,
    ProductL2Curry.curryEquiv_symm_coeFn gaussianProduct gaussianProduct
      (IBMClockPhysicalOccupation.noiseLift U),
    BochnerLinearIsometry.lift_coeFn gaussianProduct IBMPhysicalNoiseRealization.physicalNoise U]
    with Y hs hc hn
  filter_upwards [hs, hc] with X hs hc
  change realize U (X,Y) = _ at hs
  simp only [Function.comp_apply, Prod.swap_prod_mk] at hs
  rw [hs, ← hc]
  change IBMClockPhysicalOccupation.noiseLift U Y X = _
  change IBMClockPhysicalOccupation.noiseLift U Y = _ at hn
  rw [hn]

attribute [local irreducible] realize IBMConstructedSources.ibmValue

theorem source_actual (T : ℝ≥0) : realize (sourceKernel T) =ᵐ[IBMSourceLaws.jointMeasure]
    IBMConstructedSources.ibmValue T := by
  have hm : Measurable (IBMConstructedSources.ibmValue T) :=
    IBMConstructedSources.ibmValue_jointly_measurable.comp
      (show Measurable (fun w : IBMSourceLaws.JointSample => (T,w)) from
        measurable_const.prodMk measurable_id)
  have hr : Measurable (realize (sourceKernel T)) :=
    (Lp.stronglyMeasurable (realize (sourceKernel T))).measurable
  have h : (fun z : SampleSpace × SampleSpace => realize (sourceKernel T) (z.2,z.1))
      =ᵐ[gaussianProduct.prod gaussianProduct]
        fun z => IBMConstructedSources.ibmValue T (z.2,z.1) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
      (hr.comp measurable_swap)
      (hm.comp measurable_swap))).mpr
    filter_upwards [realize_sections (sourceKernel T), sourceKernel_actual_realization T]
      with Y hr hs
    exact hr.trans hs
  have hs := Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp h
  change (fun x : SampleSpace × SampleSpace => realize (sourceKernel T) x)
    =ᵐ[gaussianProduct.prod gaussianProduct] fun x => IBMConstructedSources.ibmValue T x
  simpa only [Function.comp_def, Prod.swap, Prod.mk.eta] using hs

theorem combined_joint_tendsto (T : ℝ≥0) :
    Tendsto (fun n => realize (integralValue n T)+realize (correction n T)) atTop
      (𝓝 (realize (sourceKernel T))) := by
  have h := realize.continuous.tendsto (sourceKernel T) |>.comp (endpoint_tendsto T)
  have he (n : ℕ) : realize (integralValue n T)+realize (correction n T) =
      realize (endpoint n T) := by
    rw [← map_add]
    congr 1
    unfold correction
    abel
  simpa only [Function.comp_def, ← he] using h

theorem integral_joint_norm_escape (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => ‖realize (integralValue n T)‖) atTop atTop := by
  simpa only [realize.norm_map] using integral_norm_escape T hT

theorem correction_joint_norm_escape (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => ‖realize (correction n T)‖) atTop atTop := by
  simpa only [realize.norm_map] using correction_norm_escape T hT

theorem integral_joint_not_tendsto (T : ℝ≥0) (hT : 0 < T)
    (F : Lp ℝ 2 IBMSourceLaws.jointMeasure) :
    ¬ Tendsto (fun n => realize (integralValue n T)) atTop (𝓝 F) := by
  intro hf
  exact not_tendsto_nhds_of_tendsto_atTop (integral_joint_norm_escape T hT) _ hf.norm

theorem correction_joint_not_tendsto (T : ℝ≥0) (hT : 0 < T)
    (F : Lp ℝ 2 IBMSourceLaws.jointMeasure) :
    ¬ Tendsto (fun n => realize (correction n T)) atTop (𝓝 F) := by
  intro hf
  exact not_tendsto_nhds_of_tendsto_atTop (correction_joint_norm_escape T hT) _ hf.norm

end OperatorDerivativeRewrite.Foundation.IBMSpatialPointClockObstruction
