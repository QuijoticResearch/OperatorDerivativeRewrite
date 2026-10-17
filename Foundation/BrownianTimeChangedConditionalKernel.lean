import Foundation.BrownianTimeChangedVariance
import Mathlib.Probability.Kernel.CondDistrib

/-! Genuine two-time regular conditional kernels of the constructed process.
These are disintegrations under its actual starting law, not an asserted
time-homogeneous transition semigroup or full-past Markov theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianTimeChangedConditionalKernel
open InfiniteGaussian BrownianMassRandomTimeChange BrownianTimeChangedMartingales
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath
  BrownianMassRandomTimeChange.inverse BrownianRandomMassClock.mass

def state (κ t : ℝ≥0) (ω : SampleSpace) : ℝ := changedPath κ ω t
def marginal (κ t : ℝ≥0) : Measure ℝ := gaussianProduct.map (state κ t)
def pairLaw (κ s t : ℝ≥0) : Measure (ℝ × ℝ) :=
  gaussianProduct.map (fun ω => (state κ s ω,state κ t ω))
def pairKernel (κ s t : ℝ≥0) : Kernel ℝ ℝ := condDistrib (state κ t) (state κ s) gaussianProduct

theorem state_measurable (κ t : ℝ≥0) : Measurable (state κ t) := changedPath_coordinate_measurable κ t

instance marginal_probability (κ t : ℝ≥0) : IsProbabilityMeasure (marginal κ t) :=
  (Measure.isProbabilityMeasure_map_iff (state_measurable κ t).aemeasurable).mpr inferInstance

instance pairKernel_markov (κ s t : ℝ≥0) : IsMarkovKernel (pairKernel κ s t) := by
  unfold pairKernel
  infer_instance

theorem pairLaw_disintegration (κ s t : ℝ≥0) :
    marginal κ s ⊗ₘ pairKernel κ s t = pairLaw κ s t :=
  compProd_map_condDistrib (state_measurable κ s).aemeasurable (state_measurable κ t).aemeasurable

theorem pairKernel_marginal_transport (κ s t : ℝ≥0) :
    pairKernel κ s t ∘ₘ marginal κ s = marginal κ t :=
  condDistrib_comp_map (state_measurable κ s).aemeasurable (state_measurable κ t).aemeasurable

theorem diagonal_kernel (κ s : ℝ≥0) : pairKernel κ s s =ᵐ[marginal κ s] Kernel.id :=
  condDistrib_self (state_measurable κ s).aemeasurable

theorem bounded_conditional (κ s t : ℝ≥0) (f : ℝ → ℝ) (hf : Measurable f)
    (K : ℝ) (hK : ∀ x, ‖f x‖ ≤ K) :
    gaussianProduct[(fun ω => f (state κ t ω)) |
      MeasurableSpace.comap (state κ s) inferInstance] =ᵐ[gaussianProduct]
      (fun ω => ∫ y, f y ∂pairKernel κ s t (state κ s ω)) := by
  have hi : Integrable (fun ω => f (state κ t ω)) gaussianProduct :=
    (integrable_const K).mono' (hf.comp (state_measurable κ t)).aestronglyMeasurable
      (Eventually.of_forall fun ω => hK _)
  exact condExp_ae_eq_integral_condDistrib (state_measurable κ s)
    (state_measurable κ t).aemeasurable hf.stronglyMeasurable hi

theorem current_mean (κ s t : ℝ≥0) (hst : s ≤ t) :
    gaussianProduct[state κ t | MeasurableSpace.comap (state κ s) inferInstance]
      =ᵐ[gaussianProduct] state κ s := by
  have hM := changed_brownian_martingale κ
  have hcur : MeasurableSpace.comap (state κ s) inferInstance ≤ physicalPast κ s :=
    (hM.stronglyAdapted s).measurable.comap_le
  have hm : StronglyMeasurable[MeasurableSpace.comap (state κ s) inferInstance] (state κ s) :=
    (comap_measurable (state κ s)).stronglyMeasurable
  calc
    _ =ᵐ[gaussianProduct] gaussianProduct[gaussianProduct[state κ t | physicalPast κ s] |
        MeasurableSpace.comap (state κ s) inferInstance] :=
      (condExp_condExp_of_le hcur ((physicalPast κ).le s)).symm
    _ =ᵐ[gaussianProduct] gaussianProduct[state κ s |
        MeasurableSpace.comap (state κ s) inferInstance] := condExp_congr_ae (hM.condExp_ae_eq hst)
    _ =ᵐ[gaussianProduct] state κ s := by
      rw [condExp_of_stronglyMeasurable (state_measurable κ s).comap_le hm (hM.integrable s)]

theorem row_mean_on_state (κ s t : ℝ≥0) (hst : s ≤ t) :
    (fun ω => ∫ y, y ∂pairKernel κ s t (state κ s ω)) =ᵐ[gaussianProduct] state κ s :=
  (condExp_ae_eq_integral_condDistrib' (state_measurable κ s)
    ((changed_brownian_martingale κ).integrable t)).symm.trans (current_mean κ s t hst)

theorem row_identity_integrable (κ s t : ℝ≥0) :
    ∀ᵐ x ∂marginal κ s, Integrable (fun y : ℝ => y) (pairKernel κ s t x) := by
  have hj : Integrable (fun z : ℝ × ℝ => z.2) (pairLaw κ s t) := by
    rw [pairLaw, integrable_map_measure measurable_snd.aestronglyMeasurable
      ((state_measurable κ s).prodMk (state_measurable κ t)).aemeasurable]
    exact (changed_brownian_martingale κ).integrable t
  exact ((measurable_snd.aestronglyMeasurable.ae_integrable_condDistrib_map_iff
    (state_measurable κ s).aemeasurable (state_measurable κ t).aemeasurable).mpr hj).1

end OperatorDerivativeRewrite.Foundation.BrownianTimeChangedConditionalKernel
