import Foundation.IBMSchwartzHeatSemigroup
import Foundation.GaussianBoundedBanachStein

/-! Actual all-source Bochner increment covariance for the nonlinear IBM heat
mean. Positive remaining variance is essential; the terminal rough curve is
not differentiated. This is a transition identity, not yet native Ito recovery. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzHeatIncrement
open IBMSchwartzHalfHolderHeat IBMSchwartzHeatDerivative IBMSchwartzHeatSemigroup
attribute [local irreducible] curve heatMean heatScore GaussianHalfHolderScore.score
  GaussianBoundedHeatDerivative.mean

theorem score_integrable (g : SchwartzMap ℝ ℝ) (a b : ℝ) (u v : ℝ≥0)
    (hv : 0 < v) :
    Integrable (fun x => heatScore g a (b+x) v) (gaussianReal 0 u) := by
  apply (integrable_const
    ((constant g*GaussianHalfHolderScore.mass)/Real.sqrt (Real.sqrt v))).mono'
  · exact ((heatScore_stronglyMeasurable g a).comp_measurable
      (((measurable_const : Measurable (fun _ : ℝ => b)).add measurable_id).prodMk
        measurable_const)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => heatScore_norm g a _ _ hv

theorem mean_increment (g : SchwartzMap ℝ ℝ) (a b : ℝ) (u v : ℝ≥0)
    (hv : 0 < v) :
    (∫ x, x • heatMean g a (b+x) v ∂gaussianReal 0 u) =
      (u : ℝ) • heatScore g a b (u+v) := by
  have hD : StronglyMeasurable (fun x : ℝ => heatScore g a x v) :=
    (heatScore_stronglyMeasurable g a).comp_measurable
      (measurable_id.prodMk measurable_const)
  have hM : 0 ≤ SchwartzMap.seminorm ℝ 0 0 g := apply_nonneg _ _
  have hB : 0 ≤ (constant g*GaussianHalfHolderScore.mass)/Real.sqrt (Real.sqrt v) :=
    div_nonneg (mul_nonneg (constant_nonneg g) GaussianHalfHolderScore.mass_nonneg)
      (Real.sqrt_nonneg _)
  have hs := GaussianBoundedBanachStein.scaled_stein
    (fun x => heatMean g a x v) (fun x => heatScore g a x v)
    (fun x => heatMean_hasDerivAt g a x v hv) hD
    (SchwartzMap.seminorm ℝ 0 0 g)
    ((constant g*GaussianHalfHolderScore.mass)/Real.sqrt (Real.sqrt v))
    hM hB (fun x => heatMean_bound g a x v)
    (fun x => heatScore_norm g a x v hv) b u
  rw [gradient_semigroup g a b u v hv] at hs
  exact hs

theorem derivative_tower (g : SchwartzMap ℝ ℝ) (a b : ℝ) (u v : ℝ≥0)
    (hv : 0 < v) :
    HasDerivAt (fun t => ∫ x, heatMean g a (t+x) v ∂gaussianReal 0 u)
      (∫ x, heatScore g a (b+x) v ∂gaussianReal 0 u) b := by
  have he : (fun t => ∫ x, heatMean g a (t+x) v ∂gaussianReal 0 u) =
      fun t => heatMean g a t (u+v) := funext fun t => value_semigroup g a t u v
  rw [he, gradient_semigroup g a b u v hv]
  exact heatMean_hasDerivAt g a b (u+v) (by
    have hv' : (0 : ℝ) < v := hv
    positivity)

theorem conditional_score (g : SchwartzMap ℝ ℝ) (a : ℝ) (S R v : ℝ≥0)
    (hSR : S ≤ R) (hv : 0 < v) :
    InfiniteGaussian.gaussianProduct[
      fun Y => heatScore g a (GaussianTimeProcess.process R Y) v |
        GaussianTimeProcess.naturalFiltration S] =ᵐ[InfiniteGaussian.gaussianProduct]
      fun Y => heatScore g a (GaussianTimeProcess.process S Y) (((R-S)+v : ℝ≥0) : ℝ) := by
  have hf : StronglyMeasurable (fun x : ℝ => heatScore g a x v) :=
    (heatScore_stronglyMeasurable g a).comp_measurable
      (measurable_id.prodMk measurable_const)
  have hi : Integrable
      (fun Y => heatScore g a (GaussianTimeProcess.process R Y) v)
      InfiniteGaussian.gaussianProduct := by
    apply (integrable_const
      ((constant g*GaussianHalfHolderScore.mass)/Real.sqrt (Real.sqrt v))).mono'
    · exact (hf.comp_measurable
        (GaussianTimeProcess.process_stronglyMeasurable R).measurable).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun Y => heatScore_norm g a _ _ hv
  have h := GaussianBrownianConditionalTransition.conditional_transition S R hSR
    (fun x => heatScore g a x v) hf hi
  filter_upwards [h] with Y hY
  exact hY.trans (gradient_semigroup g a (GaussianTimeProcess.process S Y) (R-S) v hv)

end OperatorDerivativeRewrite.Foundation.IBMSchwartzHeatIncrement
