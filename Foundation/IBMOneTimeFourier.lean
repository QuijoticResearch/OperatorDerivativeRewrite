import Foundation.IBMOneTimeMixture
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-! Actual characteristic functions of the constructed IBM one-time laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMOneTimeFourier
set_option backward.isDefEq.respectTransparency false
open InfiniteGaussian IBMSourceLaws IBMConstructedSources IBMOneTimeMixture

def observable (u x : ℝ) : ℂ := Complex.exp (((u*x : ℝ) : ℂ)*Complex.I)

theorem observable_continuous (u : ℝ) : Continuous (observable u) := by unfold observable; fun_prop

theorem observable_norm (u x : ℝ) : ‖observable u x‖=1 := by
  simp only [observable,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,Real.exp_zero]

theorem observable_integrable (u : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (observable u) μ :=
  Integrable.of_bound (observable_continuous u).aestronglyMeasurable 1
    (Eventually.of_forall fun x => (observable_norm u x).le)

theorem charFun_eq_observable (μ : Measure ℝ) (u : ℝ) :
    charFun μ u=∫ x, observable u x ∂μ := by
  simp only [charFun_apply_real,observable,Complex.ofReal_mul]

def clockTransform (t : ℝ≥0) (a : ℝ) : ℝ := ∫ r : ℝ, Real.exp (-a*|r|) ∂gaussianReal 0 t

theorem scenery_characteristic (u r : ℝ) :
    (∫ ξ : SampleSpace, observable u (sceneryPath ξ r) ∂gaussianProduct) =
      (Real.exp (-(u^2/2)*|r|) : ℂ) := by
  have h := (IBMOneTimeMixture.scenery_law r).integral_comp
    (observable_continuous u).aestronglyMeasurable
  change (∫ ξ : SampleSpace, observable u (sceneryPath ξ r) ∂gaussianProduct) =
    ∫ x : ℝ, observable u x ∂gaussianReal 0 ‖r‖₊ at h
  rw [← charFun_eq_observable] at h
  rw [h,charFun_gaussianReal,Complex.ofReal_exp]
  congr 1
  simp only [Complex.ofReal_zero,mul_zero,zero_mul,zero_sub]
  push_cast
  simp only [coe_nnnorm,Real.norm_eq_abs]
  ring

theorem mixture_characteristic (t : ℝ≥0) (u : ℝ) :
    charFun (mixture t) u=(clockTransform t (u^2/2) : ℂ) := by
  have hLaw := (signed_value_law t).integral_comp
    (observable_continuous u).aestronglyMeasurable
  change (∫ ω : JointSample, observable u (SignedIBMRealization.value t ω) ∂jointMeasure) =
    ∫ x : ℝ, observable u x ∂mixture t at hLaw
  have hi := (signed_value_law t).integrable_comp (observable_integrable u (mixture t))
  change Integrable (fun ω : JointSample => observable u (SignedIBMRealization.value t ω))
    (gaussianProduct.prod gaussianProduct) at hi
  calc
    charFun (mixture t) u =
        ∫ ω : JointSample, observable u (SignedIBMRealization.value t ω) ∂jointMeasure := by
      rw [charFun_eq_observable]
      exact hLaw.symm
    _ = ∫ ω : SampleSpace, ∫ ξ : SampleSpace,
        observable u (sceneryPath ξ (clockPath ω t)) ∂gaussianProduct ∂gaussianProduct :=
      integral_prod_symm _ hi
    _ = ∫ ω : SampleSpace, (Real.exp (-(u^2/2)*|clockPath ω t|) : ℂ) ∂gaussianProduct := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ω => scenery_characteristic u (clockPath ω t)
    _ = ∫ r : ℝ, (Real.exp (-(u^2/2)*|r|) : ℂ) ∂gaussianReal 0 t :=
      (clock_law t).integral_comp (show AEStronglyMeasurable
        (fun r : ℝ => (Real.exp (-(u^2/2)*|r|) : ℂ)) (gaussianReal 0 t) from by fun_prop)
    _ = (clockTransform t (u^2/2) : ℂ) := integral_complex_ofReal

theorem signed_characteristic (t : ℝ≥0) (u : ℝ) :
    charFun (jointMeasure.map (SignedIBMRealization.value t)) u=
      (clockTransform t (u^2/2) : ℂ) := by
  rw [(signed_value_law t).map_eq,mixture_characteristic]

theorem absolute_characteristic (t : ℝ≥0) (u : ℝ) :
    charFun (jointMeasure.map (IBMConstructedSources.ibmValue t)) u=
      (clockTransform t (u^2/2) : ℂ) := by
  rw [(absolute_value_law t).map_eq,mixture_characteristic]

end OperatorDerivativeRewrite.Foundation.IBMOneTimeFourier
