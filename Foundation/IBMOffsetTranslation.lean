import Foundation.IBMContinuousBulkVariance

/-! Translation bridge from fixed offset kernels to the established scenery convolution. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace OperatorDerivativeRewrite.Foundation.IBMOffsetTranslation
open IBMContinuousBulkVariance IBMContinuousScenery
open FractionalSpectralKernel IBMFiniteScenerySmoothing
open IBMMollifier

theorem offsetDirection_eq_kernelDirection (a b x : ℝ) (ρ : ℝ → ℝ)
    (hab : a ≤ b) :
    offsetDirection a b x ρ = kernelDirection (x + a) (x + b) x ρ := by
  unfold offsetDirection kernelDirection
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]
  have htrans := intervalIntegral.integral_comp_add_right
    (fun z : ℝ => ρ (x - z) • direction z) x
    (a := a) (b := b)
  have hpoint : (fun r : ℝ => ρ (-r) • direction (x + r)) =
      (fun r : ℝ => ρ (x - (r + x)) • direction (r + x)) := by
    funext r
    simp [add_comm]
  rw [hpoint, htrans]
  rw [show a + x = x + a by ring, show b + x = x + b by ring]
  rw [intervalIntegral.integral_of_le (by linarith : x + a ≤ x + b)]
  rw [← integral_Icc_eq_integral_Ioc]

theorem wholeLineScenery_eq_offsetScenery (a b x : ℝ) (ρ : ℝ → ℝ)
    (hab : a ≤ b)
    (hsupp : ∀ r, r ∉ Set.Icc (x + a) (x + b) → ρ (x - r) = 0) :
    wholeLineScenery ρ x = offsetScenery a b x ρ := by
  rw [wholeLineScenery_eq_embedding (x + a) (x + b) x ρ hsupp,
    ← offsetDirection_eq_kernelDirection a b x ρ hab]
  rfl

theorem concrete_wholeLineScenery_eq_offset (n : ℕ) (x : ℝ) :
    wholeLineScenery (kernel n) x =
      offsetScenery (-(bump n).rOut) (bump n).rOut x (kernel n) := by
  apply wholeLineScenery_eq_offsetScenery
  · linarith [(bump n).rOut_pos]
  · intro r hr
    apply concreteMollifier_support n x r
    simpa [sub_eq_add_neg] using hr

/-- The exact interior affine variance of the original whole-line Gaussian
scenery mollifier, not merely an auxiliary translated field. -/
theorem concrete_wholeLineScenery_affine_variance (n : ℕ) (x : ℝ)
    (hbulk : (bump n).rOut ≤ x) :
    ‖wholeLineScenery (kernel n) x‖^2 =
      x + offsetCorrection (-(bump n).rOut) (bump n).rOut (kernel n) := by
  rw [concrete_wholeLineScenery_eq_offset]
  exact concreteOffsetScenery_affine_variance n x hbulk

theorem concrete_wholeLineVariance_deriv (n : ℕ) (x : ℝ)
    (hbulk : (bump n).rOut < x) :
    deriv (wholeLineVariance (kernel n)) x = 1 := by
  let C := offsetCorrection (-(bump n).rOut) (bump n).rOut (kernel n)
  have heq : wholeLineVariance (kernel n) =ᶠ[nhds x] (fun y : ℝ => y + C) := by
    filter_upwards [lt_mem_nhds hbulk] with y hy
    exact concrete_wholeLineScenery_affine_variance n y hy.le
  exact ((hasDerivAt_id x).add_const C).congr_of_eventuallyEq heq |>.deriv

theorem concrete_wholeLineVariance_second_deriv (n : ℕ) (x : ℝ)
    (hbulk : (bump n).rOut < x) :
    deriv (fun y => deriv (wholeLineVariance (kernel n)) y) x = 0 := by
  have heq : (fun y => deriv (wholeLineVariance (kernel n)) y) =ᶠ[nhds x]
      (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [lt_mem_nhds hbulk] with y hy
    exact concrete_wholeLineVariance_deriv n y hy
  exact ((hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq heq).deriv

/-- Both covariance contractions required for the paper's interior Gaussian
Stein calculation, derived from the actual normalized whole-line mollifier. -/
theorem concrete_interior_cross_covariance (n : ℕ) (x : ℝ)
    (hbulk : (bump n).rOut < x) :
    inner ℝ (wholeLineScenery (kernel n) x)
      (wholeLineScenery (deriv (kernel n)) x) = 1 / 2 := by
  exact wholeLine_cross_covariance_half (kernel n) (kernel_compactSupport n)
    ((kernel_smooth n).of_le (by norm_num)) x
    (concrete_wholeLineVariance_deriv n x hbulk)

theorem concrete_interior_covariance_cancellation (n : ℕ) (x : ℝ)
    (hbulk : (bump n).rOut < x) :
    ‖wholeLineScenery (deriv (kernel n)) x‖ ^ 2 +
      inner ℝ (wholeLineScenery (kernel n) x)
        (wholeLineScenery (deriv (deriv (kernel n))) x) = 0 := by
  exact wholeLine_covariance_cancellation (kernel n) (kernel_compactSupport n)
    ((kernel_smooth n).of_le (by norm_num)) x
    (concrete_wholeLineVariance_second_deriv n x hbulk)

end OperatorDerivativeRewrite.Foundation.IBMOffsetTranslation
