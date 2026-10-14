import Foundation.IBMOffsetTranslation

/-! Exact two-sided boundary covariance of the actual Gaussian scenery mollifier. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace OperatorDerivativeRewrite.Foundation.IBMBoundaryVariance
open InfiniteGaussian FractionalSpectralKernel FractionalSpectralGeometry
open GaussianHilbertProcess IBMFiniteScenerySmoothing IBMContinuousScenery
open IBMContinuousBulkVariance IBMOffsetTranslation IBMMollifier
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable

theorem offsetDirection_inner_general (a b x : ℝ) {ρ : ℝ → ℝ}
    (hρ : Continuous ρ) :
    inner ℝ (offsetDirection a b x ρ) (offsetDirection a b x ρ) =
      ∫ s in Set.Icc a b, ρ (-s) *
        (∫ r in Set.Icc a b, ρ (-r) *
          FractionalSpectralGeometry.covariance (1/2) (x + r) (x + s)) := by
  have hi := offsetDirection_integrable a b x hρ
  change inner ℝ (offsetDirection a b x ρ)
    (∫ s in Set.Icc a b, ρ (-s) • direction (x + s)) = _
  rw [← integral_inner hi]
  apply setIntegral_congr_fun measurableSet_Icc
  intro s hs
  dsimp only
  rw [real_inner_smul_right, real_inner_comm]
  change ρ (-s) * inner ℝ (direction (x + s))
    (∫ r in Set.Icc a b, ρ (-r) • direction (x + r)) = _
  rw [← integral_inner hi]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro r hr
  dsimp only
  rw [real_inner_smul_right, real_inner_comm]
  simp only [direction, normalized_inner]

theorem offsetScenery_boundary_variance (a b x : ℝ) {ρ : ℝ → ℝ}
    (hρ : Continuous ρ) :
    ‖offsetScenery a b x ρ‖^2 =
      ∫ s in Set.Icc a b, ρ (-s) *
        (∫ r in Set.Icc a b, ρ (-r) *
          (x + min r s + max (-(x + r)) 0 + max (-(x + s)) 0)) := by
  rw [offsetScenery, LinearIsometry.norm_map,
    ← real_inner_self_eq_norm_sq, offsetDirection_inner_general a b x hρ]
  congr 1
  funext s
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro r hr
  dsimp only
  rw [covariance_boundary_decomposition]

theorem concrete_wholeLineScenery_boundary_variance (n : ℕ) (x : ℝ) :
    ‖wholeLineScenery (IBMMollifier.kernel n) x‖^2 =
      ∫ s in Set.Icc (-(bump n).rOut) (bump n).rOut, IBMMollifier.kernel n (-s) *
        (∫ r in Set.Icc (-(bump n).rOut) (bump n).rOut,
          IBMMollifier.kernel n (-r) *
            (x + min r s + max (-(x + r)) 0 + max (-(x + s)) 0)) := by
  rw [concrete_wholeLineScenery_eq_offset]
  exact offsetScenery_boundary_variance _ _ _ (IBMMollifier.kernel_smooth n).continuous

end OperatorDerivativeRewrite.Foundation.IBMBoundaryVariance
