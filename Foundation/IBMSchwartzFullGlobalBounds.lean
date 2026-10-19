import Foundation.IBMSchwartzPhysicalGlobalBounds

noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
open OperatorDerivativeRewrite.Foundation
open InfiniteGaussian GaussianTimeProcess
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzFullGlobalBounds
open GaussianTimeHilbert IBMGaussianSteinMoments IBMPhysicalNoiseRealization
open IBMSchwartzPhysicalFirstKernel IBMPhysicalNoiseCalculus IBMPhysicalDerivativeKernel
open IBMSchwartzSecondProjection IBMSchwartzSourceSecondDerivative IBMSchwartzHeatBounds
open IBMCorrectionStein

theorem jet_one_norm (n : ℕ) (r : ℝ) :
    ‖tripleCoefficient n r 1‖ = (eLpNorm (IBMMollifier.kernel n) 2 volume).toReal := by
  have hn : ‖physicalJet n r 1‖ = ‖tripleCoefficient n r 1‖ := by
    rw [← physicalToCoefficient.norm_map (physicalJet n r 1),physicalJet,triple_coefficient_physical]
  rw [← hn]
  change ‖convolutionKernel (deriv (IBMMollifier.kernel n)) r‖ = _
  rw [derivative_eq_translated ((IBMMollifier.kernel_smooth n).of_le (by norm_num))
    (IBMMollifier.kernel_compactSupport n)]
  exact IBMSchwartzPhysicalGlobalBounds.translated_norm _ _ _ _

theorem jet_two_norm (n : ℕ) (r : ℝ) :
    ‖tripleCoefficient n r 2‖ = (eLpNorm (deriv (IBMMollifier.kernel n)) 2 volume).toReal := by
  have hn : ‖physicalJet n r 2‖ = ‖tripleCoefficient n r 2‖ := by
    rw [← physicalToCoefficient.norm_map (physicalJet n r 2),physicalJet,triple_coefficient_physical]
  rw [← hn]
  change ‖convolutionKernel (deriv (deriv (IBMMollifier.kernel n))) r‖ = _
  rw [derivative_eq_translated (((IBMMollifier.kernel_smooth n).of_le (by norm_num) :
    ContDiff ℝ 2 (IBMMollifier.kernel n)).deriv' (n := 1))
    (IBMMollifier.kernel_compactSupport n).deriv]
  exact IBMSchwartzPhysicalGlobalBounds.translated_norm _ _ _ _

theorem slope_bound (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r, ‖spatialSlope g a n r‖ ≤ C := by
  let C := SchwartzMap.seminorm ℝ 0 0 (jet g 1)*(eLpNorm (IBMMollifier.kernel n) 2 volume).toReal
  refine ⟨C,by positivity,fun r => ?_⟩
  have he := weightedClass_norm_le g a (tripleCoefficient n r 0) 1
    (firstChaosEmbedding (tripleCoefficient n r 1))
  rw [firstChaosEmbedding.norm_map,jet_one_norm] at he
  exact he

theorem curvature_bound (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r, ‖mollifiedClass g a n r‖ ≤ C := by
  let B0 := (eLpNorm (IBMMollifier.kernel n) 2 volume).toReal
  let B1 := (eLpNorm (deriv (IBMMollifier.kernel n)) 2 volume).toReal
  refine ⟨2*SchwartzMap.seminorm ℝ 0 0 (jet g 2)*B0^2+
    SchwartzMap.seminorm ℝ 0 0 (jet g 1)*B1,by positivity,fun r => ?_⟩
  have he := correction_norm_le g a (tripleCoefficient n r 0)
    (tripleCoefficient n r 1) (tripleCoefficient n r 2)
  rw [jet_one_norm,jet_two_norm] at he
  exact he

theorem spatial_C2 (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) :
    ContDiff ℝ 2 (IBMFullSchwartzTerminal.spatial g a n) := by
  have he : deriv (IBMFullSchwartzTerminal.spatial g a n) = spatialSlope g a n :=
    funext fun r => (spatial_hasDerivAt g a n r).deriv
  have hd : deriv (spatialSlope g a n) = mollifiedClass g a n :=
    funext fun r => (spatialSlope_hasDerivAt g a n r).deriv
  have hs : ContDiff ℝ 1 (spatialSlope g a n) := contDiff_one_iff_deriv.mpr
    ⟨fun r => (spatialSlope_hasDerivAt g a n r).differentiableAt,
      by rw [hd]; exact IBMSchwartzSourceContinuity.mollifiedClass_continuous g a n⟩
  rw [show (2 : WithTop ℕ∞) = 1+1 by norm_num,contDiff_succ_iff_deriv]
  exact ⟨fun r => (spatial_hasDerivAt g a n r).differentiableAt,by simp,by rw [he];exact hs⟩
end OperatorDerivativeRewrite.Foundation.IBMSchwartzFullGlobalBounds
