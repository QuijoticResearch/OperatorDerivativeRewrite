import Foundation.GaussianDensityTranslation

/-! One-step Gaussian transport with an arbitrary measurable past state and coefficient. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianPastKernelTransport
open GaussianCore GaussianRandomDensityKernel GaussianDensityTranslation
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
variable {S : Type*} [MeasurableSpace S]

def shift (a : S → ℝ) (p : S × ℝ) : S × ℝ := (p.1,p.2+a p.1)

def likelihood (a : S → ℝ) (p : S × ℝ) : ℝ := kernel (a p.1) p.2

theorem shift_measurable {a : S → ℝ} (ha : Measurable a) : Measurable (shift a) :=
  measurable_fst.prodMk (measurable_snd.add (ha.comp measurable_fst))

theorem likelihood_measurable {a : S → ℝ} (ha : Measurable a) : Measurable (likelihood a) :=
  kernel_continuous.measurable.comp ((ha.comp measurable_fst).prodMk measurable_snd)

theorem likelihood_positive (a : S → ℝ) (p : S × ℝ) : 0<likelihood a p := kernel_positive _ _

theorem weighted_lintegral (μ : Measure S) [SFinite μ] (a : S → ℝ) (ha : Measurable a)
    (f : S × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, ENNReal.ofReal (likelihood a p)*f (shift a p) ∂μ.prod γ)=∫⁻ p, f p ∂μ.prod γ := by
  have hm : Measurable (fun p => ENNReal.ofReal (likelihood a p)*f (shift a p)) :=
    (likelihood_measurable ha).ennreal_ofReal.mul (hf.comp (shift_measurable ha))
  rw [lintegral_prod _ hm.aemeasurable,lintegral_prod f hf.aemeasurable]
  apply lintegral_congr_ae
  exact Filter.Eventually.of_forall (fun x =>
    fiber_lintegral (a x) (fun y => f (x,y))
      (hf.comp (measurable_const.prodMk measurable_id)))

theorem normalized_lintegral (μ : Measure S) [IsProbabilityMeasure μ] (a : S → ℝ)
    (ha : Measurable a) : (∫⁻ p, ENNReal.ofReal (likelihood a p) ∂μ.prod γ)=1 := by
  simpa using weighted_lintegral μ a ha (fun _ => 1) measurable_const

end OperatorDerivativeRewrite.Foundation.GaussianPastKernelTransport
