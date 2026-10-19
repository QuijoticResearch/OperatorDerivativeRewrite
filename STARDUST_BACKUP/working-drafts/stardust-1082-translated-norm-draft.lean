import Foundation.IBMPhysicalDerivativeKernel
noncomputable section
open MeasureTheory
open OperatorDerivativeRewrite.Foundation
open IBMPhysicalDerivativeKernel
example (ρ : ℝ → ℝ) (hc : Continuous ρ) (hs : HasCompactSupport ρ) (x : ℝ) :
    ‖translatedClass ρ hc hs x‖ = (eLpNorm ρ 2 volume).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae (translatedClass_coeFn ρ hc hs x)]
  change (eLpNorm (ρ ∘ fun w : ℝ => x-w) 2 volume).toReal = _
  rw [eLpNorm_comp_measurePreserving hc.aestronglyMeasurable
    (volume.measurePreserving_sub_left x)]
