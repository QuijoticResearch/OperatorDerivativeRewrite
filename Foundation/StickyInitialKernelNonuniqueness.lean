import Foundation.BrownianTimeChangedConditionalKernel

/-! The actual initial law does not identify a kernel on unobserved states.
Two distinct Markov kernels give the same actual initial two-time law.
This is a precise version issue, not nonuniqueness of a sticky martingale problem. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.StickyInitialKernelNonuniqueness
open InfiniteGaussian IBMConstructedSources BrownianMassRandomTimeChange
open BrownianTimeChangedConditionalKernel
set_option backward.isDefEq.respectTransparency false

theorem initial_state_ae (κ : ℝ≥0) : state κ 0 =ᵐ[gaussianProduct] fun _ => 0 := by
  filter_upwards [clockPath_coordinate_ae 0, GaussianTimeProcess.process_zero_ae] with ω hb h0
  change clockPath ω (inverse κ ω 0) = 0
  rw [inverse_zero,hb,h0]

theorem initial_marginal (κ : ℝ≥0) : marginal κ 0 = Measure.dirac (0 : ℝ) := by
  rw [marginal, Measure.map_congr (initial_state_ae κ), Measure.map_const]
  simp

def zeroKernel : Kernel ℝ ℝ := Kernel.const ℝ (Measure.dirac (0 : ℝ))

instance zeroKernel_markov : IsMarkovKernel zeroKernel := by unfold zeroKernel; infer_instance

theorem zeroKernel_eq_id_ae (κ : ℝ≥0) : zeroKernel =ᵐ[marginal κ 0] Kernel.id := by
  rw [initial_marginal]
  simp only [Filter.EventuallyEq, ae_dirac_eq, Filter.eventually_pure]
  rfl

theorem zeroKernel_ne_id : zeroKernel ≠ Kernel.id := by
  intro h
  have he := congrArg (fun K : Kernel ℝ ℝ => K 1 {0}) h
  norm_num [zeroKernel, Kernel.id_apply] at he

theorem identity_disintegrates_initial (κ : ℝ≥0) :
    marginal κ 0 ⊗ₘ Kernel.id = pairLaw κ 0 0 := by
  rw [Measure.compProd_congr (diagonal_kernel κ 0).symm]
  exact pairLaw_disintegration κ 0 0

theorem zeroKernel_disintegrates_initial (κ : ℝ≥0) :
    marginal κ 0 ⊗ₘ zeroKernel = pairLaw κ 0 0 := by
  rw [Measure.compProd_congr ((zeroKernel_eq_id_ae κ).trans (diagonal_kernel κ 0).symm)]
  exact pairLaw_disintegration κ 0 0

end OperatorDerivativeRewrite.Foundation.StickyInitialKernelNonuniqueness
