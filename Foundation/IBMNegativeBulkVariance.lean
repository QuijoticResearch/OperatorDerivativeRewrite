import Foundation.IBMGaussianSteinMoments

/-! Exact affine variance of the mollified two-sided scenery on the negative half-line. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace OperatorDerivativeRewrite.Foundation.IBMNegativeBulkVariance
open InfiniteGaussian FractionalSpectralKernel FractionalSpectralGeometry
open GaussianHilbertProcess IBMFiniteScenerySmoothing IBMContinuousScenery
open IBMContinuousBulkVariance IBMOffsetTranslation IBMMollifier
open IBMGaussianSteinMoments IBMJointMollifierGaussian
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable

theorem negative_shifted_direction_inner (x r s : ℝ)
    (hr : x + r ≤ 0) (hs : x + s ≤ 0) :
    inner ℝ (direction (x + r)) (direction (x + s)) =
      -x - max r s := by
  simp only [direction, normalized_inner]
  rw [covariance_boundary_decomposition]
  rw [max_eq_left (by linarith : 0 ≤ -(x+r)),
    max_eq_left (by linarith : 0 ≤ -(x+s))]
  linarith [min_add_max r s]

def negativeOffsetCorrection (a b : ℝ) (ρ : ℝ → ℝ) : ℝ :=
  ∫ s in Set.Icc a b, ρ (-s) *
    (∫ r in Set.Icc a b, ρ (-r) * max r s)

theorem offsetDirection_negative_inner (a b x : ℝ) {ρ : ℝ → ℝ}
    (hρ : Continuous ρ) (hbulk : x + b ≤ 0) :
    inner ℝ (offsetDirection a b x ρ) (offsetDirection a b x ρ) =
      ∫ s in Set.Icc a b, ρ (-s) *
        (∫ r in Set.Icc a b, ρ (-r) * (-x - max r s)) := by
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
  rw [negative_shifted_direction_inner x r s (by linarith [hr.2])
    (by linarith [hs.2])]

theorem offsetDirection_negative_affine_variance (a b x : ℝ) {ρ : ℝ → ℝ}
    (hρ : Continuous ρ) (hbulk : x + b ≤ 0)
    (hmass : (∫ r in Set.Icc a b, ρ (-r)) = 1) :
    ‖offsetDirection a b x ρ‖^2 = -x - negativeOffsetCorrection a b ρ := by
  rw [← real_inner_self_eq_norm_sq, offsetDirection_negative_inner a b x hρ hbulk]
  unfold negativeOffsetCorrection
  have hinner (s : ℝ) :
      (∫ r in Set.Icc a b, ρ (-r) * (-x - max r s)) =
      -x - ∫ r in Set.Icc a b, ρ (-r) * max r s := by
    simp_rw [mul_sub]
    rw [integral_sub]
    · rw [integral_mul_const, hmass, one_mul]
    · exact ((hρ.comp continuous_neg).mul continuous_const).integrableOn_Icc
    · exact ((hρ.comp continuous_neg).mul
        (continuous_id.max continuous_const)).integrableOn_Icc
  have hc : Continuous (fun s : ℝ =>
      ∫ r in Set.Icc a b, ρ (-r) * max r s) := by
    apply continuous_parametric_integral_of_continuous
    · fun_prop
    · exact isCompact_Icc
  simp_rw [hinner, mul_sub]
  rw [integral_sub]
  · rw [integral_mul_const, hmass, one_mul]
  · exact ((hρ.comp continuous_neg).mul continuous_const).integrableOn_Icc
  · exact ((hρ.comp continuous_neg).mul hc).integrableOn_Icc

theorem concrete_wholeLineScenery_negative_affine_variance (n : ℕ) (x : ℝ)
    (hbulk : x ≤ -(bump n).rOut) :
    ‖wholeLineScenery (kernel n) x‖^2 =
      -x - negativeOffsetCorrection (-(bump n).rOut) (bump n).rOut (kernel n) := by
  rw [concrete_wholeLineScenery_eq_offset, offsetScenery, LinearIsometry.norm_map]
  apply offsetDirection_negative_affine_variance _ _ _ (kernel_smooth n).continuous
  · linarith
  · simpa using concreteMollifier_mass n 0

theorem concrete_negative_variance_deriv (n : ℕ) (x : ℝ)
    (hbulk : x < -(bump n).rOut) :
    deriv (wholeLineVariance (kernel n)) x = -1 := by
  let C := negativeOffsetCorrection (-(bump n).rOut) (bump n).rOut (kernel n)
  have heq : wholeLineVariance (kernel n) =ᶠ[nhds x] (fun y : ℝ => -y - C) := by
    filter_upwards [gt_mem_nhds hbulk] with y hy
    exact concrete_wholeLineScenery_negative_affine_variance n y hy.le
  exact (((hasDerivAt_id x).neg).sub_const C).congr_of_eventuallyEq heq |>.deriv

theorem concrete_negative_variance_second_deriv (n : ℕ) (x : ℝ)
    (hbulk : x < -(bump n).rOut) :
    deriv (fun y => deriv (wholeLineVariance (kernel n)) y) x = 0 := by
  have heq : (fun y => deriv (wholeLineVariance (kernel n)) y) =ᶠ[nhds x]
      (fun _ : ℝ => (-1 : ℝ)) := by
    filter_upwards [gt_mem_nhds hbulk] with y hy
    exact concrete_negative_variance_deriv n y hy
  exact ((hasDerivAt_const x (-1 : ℝ)).congr_of_eventuallyEq heq).deriv

theorem concrete_negative_cross_covariance (n : ℕ) (x : ℝ)
    (hbulk : x < -(bump n).rOut) :
    inner ℝ (wholeLineScenery (kernel n) x)
      (wholeLineScenery (deriv (kernel n)) x) = -1 / 2 := by
  have hslope := concrete_negative_variance_deriv n x hbulk
  rw [wholeLineVariance_deriv (kernel n) (kernel_compactSupport n)
    ((kernel_smooth n).of_le (by norm_num)) x] at hslope
  linarith

theorem concrete_negative_covariance_cancellation (n : ℕ) (x : ℝ)
    (hbulk : x < -(bump n).rOut) :
    ‖wholeLineScenery (deriv (kernel n)) x‖ ^ 2 +
      inner ℝ (wholeLineScenery (kernel n) x)
        (wholeLineScenery (deriv (deriv (kernel n))) x) = 0 := by
  exact wholeLine_covariance_cancellation (kernel n) (kernel_compactSupport n)
    ((kernel_smooth n).of_le (by norm_num)) x
    (concrete_negative_variance_second_deriv n x hbulk)

/-- The quartic Stein coefficient is even in the bulk variance slope, so it
equals `1/4` on both exterior half-lines despite their opposite slopes. -/
theorem concrete_negative_quartic_correction_expectation (n : ℕ) (x : ℝ)
    (hbulk : x < -(bump n).rOut) :
    (∫ ω, (1 / 2 : ℝ) *
        (gaussianTriple n x 0 ω)^2 * (gaussianTriple n x 1 ω)^2 +
        (1 / 6 : ℝ) *
        (gaussianTriple n x 0 ω)^3 * gaussianTriple n x 2 ω
      ∂gaussianProduct) = 1 / 4 := by
  rw [quartic_correction_variance_geometry,
    concrete_negative_variance_deriv n x hbulk,
    concrete_negative_variance_second_deriv n x hbulk]
  ring

end OperatorDerivativeRewrite.Foundation.IBMNegativeBulkVariance
