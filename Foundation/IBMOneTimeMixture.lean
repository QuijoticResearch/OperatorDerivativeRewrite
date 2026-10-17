import Foundation.SignedIBMRealization
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Actual one-time Gaussian mixtures of the constructed signed and absolute-clock IBM. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMOneTimeMixture
set_option backward.isDefEq.respectTransparency false
open InfiniteGaussian IBMSourceLaws IBMConstructedSources GaussianHilbertProcess
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable

def gaussianKernel : Kernel ℝ ℝ where
  toFun r := gaussianReal 0 ‖r‖₊
  measurable' := by fun_prop

theorem gaussianKernel_apply (r : ℝ) : gaussianKernel r=gaussianReal 0 ‖r‖₊ := rfl

instance gaussianKernel_markov : IsMarkovKernel gaussianKernel where
  isProbabilityMeasure r := by change IsProbabilityMeasure (gaussianReal 0 ‖r‖₊); infer_instance

def mixture (t : ℝ≥0) : Measure ℝ := (gaussianReal 0 t).bind gaussianKernel

instance mixture_probability (t : ℝ≥0) : IsProbabilityMeasure (mixture t) :=
  isProbabilityMeasure_bind gaussianKernel.aemeasurable (Eventually.of_forall fun _ => inferInstance)

theorem scenery_law (r : ℝ) :
    HasLaw (fun ξ : SampleSpace => sceneryPath ξ r) (gaussianReal 0 ‖r‖₊) gaussianProduct := by
  have hb : HasLaw (sceneryBase r) (gaussianReal 0 ‖r‖₊) gaussianProduct := by
    refine ⟨(sceneryBase_measurable r).aemeasurable,?_⟩
    unfold sceneryBase
    rw [isonormal_law]
    apply congrArg (gaussianReal 0)
    apply NNReal.eq
    norm_num [FractionalSpectralGeometry.normalized_norm_sq,Real.norm_eq_abs] <;> rfl
  exact hb.congr (sceneryPath_coordinate_ae r)

theorem clock_law (t : ℝ≥0) :
    HasLaw (fun ω : SampleSpace => clockPath ω t) (gaussianReal 0 t) gaussianProduct :=
  clock_isBrownian.toIsPreBrownianReal.hasLaw_eval t

theorem composition_law (t : ℝ≥0) (Y : JointSample → ℝ) (hY : Measurable Y)
    (rfn : ℝ → ℝ)
    (hvalue : ∀ ξ ω : SampleSpace, Y (ξ,ω)=sceneryPath ξ (rfn (clockPath ω t)))
    (hvariance : ∀ r : ℝ, ‖rfn r‖₊=‖r‖₊) : jointMeasure.map Y=mixture t := by
  ext A hA
  rw [Measure.map_apply hY hA,jointMeasure,Measure.prod_apply_symm (hY hA)]
  have hfiber (ω : SampleSpace) :
      gaussianProduct ((fun ξ : SampleSpace => (ξ,ω)) ⁻¹' (Y ⁻¹' A)) =
        gaussianKernel (clockPath ω t) A := by
    have hl := scenery_law (rfn (clockPath ω t))
    have he := congrArg (fun μ : Measure ℝ => μ A) hl.map_eq
    have hscene : Measurable (fun ξ : SampleSpace => sceneryPath ξ (rfn (clockPath ω t))) :=
      (ContinuousMap.measurable_eval _).comp sceneryPath_measurable
    rw [Measure.map_apply hscene hA] at he
    simp only [hvariance] at he
    change gaussianProduct ((fun ξ => Y (ξ,ω)) ⁻¹' A) = _
    simpa only [hvalue,gaussianKernel_apply] using he
  rw [mixture,Measure.bind_apply hA gaussianKernel.aemeasurable]
  calc
    (∫⁻ ω, gaussianProduct ((fun ξ : SampleSpace => (ξ,ω)) ⁻¹' (Y ⁻¹' A)) ∂gaussianProduct) =
        ∫⁻ ω, gaussianKernel (clockPath ω t) A ∂gaussianProduct := lintegral_congr hfiber
    _ = ∫⁻ r, gaussianKernel r A ∂gaussianReal 0 t :=
      (clock_law t).lintegral_comp (gaussianKernel.measurable_coe hA).aemeasurable

theorem signed_value_law (t : ℝ≥0) :
    HasLaw (SignedIBMRealization.value t) (mixture t) jointMeasure := by
  have hp : Measurable (fun ω : JointSample => (t,ω)) := measurable_const.prodMk measurable_id
  have hm : Measurable (SignedIBMRealization.value t) := by
    change Measurable ((fun p : ℝ≥0 × JointSample => SignedIBMRealization.value p.1 p.2) ∘ (fun ω : JointSample => (t,ω)))
    exact SignedIBMRealization.value_jointly_measurable.comp hp
  refine ⟨hm.aemeasurable,?_⟩
  exact composition_law t _ hm id (by intros; rfl) (by intro r; rfl)

theorem absolute_value_law (t : ℝ≥0) :
    HasLaw (IBMConstructedSources.ibmValue t) (mixture t) jointMeasure := by
  have hp : Measurable (fun ω : JointSample => (t,ω)) := measurable_const.prodMk measurable_id
  have hm : Measurable (IBMConstructedSources.ibmValue t) := by
    change Measurable ((fun p : ℝ≥0 × JointSample => IBMConstructedSources.ibmValue p.1 p.2) ∘ (fun ω : JointSample => (t,ω)))
    exact IBMConstructedSources.ibmValue_jointly_measurable.comp hp
  refine ⟨hm.aemeasurable,?_⟩
  apply composition_law t _ hm abs (by intros; rfl)
  intro r
  apply NNReal.eq
  simp [Real.norm_eq_abs]

theorem same_one_time_law (t : ℝ≥0) :
    jointMeasure.map (SignedIBMRealization.value t) =
      jointMeasure.map (IBMConstructedSources.ibmValue t) :=
  (signed_value_law t).map_eq.trans (absolute_value_law t).map_eq.symm

end OperatorDerivativeRewrite.Foundation.IBMOneTimeMixture
