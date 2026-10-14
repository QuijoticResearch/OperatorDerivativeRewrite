import Foundation.IBMFiniteBulkVariance
import Foundation.IBMConcreteMollifier

/-! Continuous offset-kernel form of positive-half-line Brownian bulk covariance. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace OperatorDerivativeRewrite.Foundation.IBMContinuousBulkVariance
open InfiniteGaussian FractionalSpectralKernel FractionalSpectralGeometry
open GaussianHilbertProcess
open IBMFiniteScenerySmoothing IBMFiniteBulkVariance IBMContinuousScenery
open IBMMollifier
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable

def offsetDirection (a b x : ℝ) (ρ : ℝ → ℝ) : SpectralSpace :=
  ∫ r in Set.Icc a b, ρ (-r) • direction (x + r)

def offsetScenery (a b x : ℝ) (ρ : ℝ → ℝ) : GaussianL2 :=
  isonormalEmbedding SpectralSpace (offsetDirection a b x ρ)

theorem offsetScenery_eq_integral (a b x : ℝ) (ρ : ℝ → ℝ) :
    offsetScenery a b x ρ =
      ∫ r in Set.Icc a b, ρ (-r) • sourceScenery (x + r) := by
  unfold offsetScenery offsetDirection
  rw [← (isonormalEmbedding SpectralSpace).integral_comp_comm]
  congr 1
  funext r
  simp only [sourceScenery, map_smul]


theorem offsetDirection_integrable (a b x : ℝ) {ρ : ℝ → ℝ}
    (hρ : Continuous ρ) :
    IntegrableOn (fun r : ℝ => ρ (-r) • direction (x + r)) (Set.Icc a b) volume := by
  apply Continuous.integrableOn_Icc
  exact (hρ.comp continuous_neg).smul
    (direction_continuous.comp (continuous_const.add continuous_id))

theorem offsetDirection_inner (a b x : ℝ) {ρ : ℝ → ℝ}
    (hρ : Continuous ρ) (hbulk : 0 ≤ x + a) :
    inner ℝ (offsetDirection a b x ρ) (offsetDirection a b x ρ) =
      ∫ s in Set.Icc a b, ρ (-s) *
        (∫ r in Set.Icc a b, ρ (-r) * (x + min r s)) := by
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
  rw [positive_shifted_direction_inner x r s (by linarith [hr.1])
    (by linarith [hs.1])]

def offsetCorrection (a b : ℝ) (ρ : ℝ → ℝ) : ℝ :=
  ∫ s in Set.Icc a b, ρ (-s) *
    (∫ r in Set.Icc a b, ρ (-r) * min r s)

private theorem abs_eq_add_negative_part (z : ℝ) :
    |z| = z + 2 * max (-z) 0 := by
  by_cases hz : 0 ≤ z
  · rw [abs_of_nonneg hz, max_eq_right (by linarith : -z ≤ 0)]
    ring
  · have hneg : z ≤ 0 := le_of_lt (lt_of_not_ge hz)
    rw [abs_of_nonpos hneg, max_eq_left (by linarith : 0 ≤ -z)]
    ring

/-- The exact two-sided Brownian covariance differs from the positive-bulk
formula by two negative-part terms. These are supported near the scenery origin
for compact offset kernels. -/
theorem covariance_boundary_decomposition (x r s : ℝ) :
    FractionalSpectralGeometry.covariance (1/2) (x + r) (x + s) =
      x + min r s + max (-(x + r)) 0 + max (-(x + s)) 0 := by
  simp only [FractionalSpectralGeometry.covariance,
    show (2 : ℝ) * (1/2) = 1 by norm_num,
    Real.rpow_one]
  rw [abs_eq_add_negative_part (x + r),
    abs_eq_add_negative_part (x + s)]
  by_cases hrs : r ≤ s
  · rw [abs_of_nonneg (by linarith : 0 ≤ (x + s) - (x + r)), min_eq_left hrs]
    ring
  · have hsr : s ≤ r := le_of_lt (lt_of_not_ge hrs)
    rw [abs_of_nonpos (by linarith : (x + s) - (x + r) ≤ 0), min_eq_right hsr]
    ring

theorem offsetDirection_affine_variance (a b x : ℝ) {ρ : ℝ → ℝ}
    (hρ : Continuous ρ) (hbulk : 0 ≤ x + a)
    (hmass : (∫ r in Set.Icc a b, ρ (-r)) = 1) :
    ‖offsetDirection a b x ρ‖^2 = x + offsetCorrection a b ρ := by
  rw [← real_inner_self_eq_norm_sq, offsetDirection_inner a b x hρ hbulk]
  unfold offsetCorrection
  have hinner (s : ℝ) :
      (∫ r in Set.Icc a b, ρ (-r) * (x + min r s)) =
      x + ∫ r in Set.Icc a b, ρ (-r) * min r s := by
    simp_rw [mul_add]
    rw [integral_add]
    · rw [integral_mul_const, hmass, one_mul]
    · exact ((hρ.comp continuous_neg).mul continuous_const).integrableOn_Icc
    · exact ((hρ.comp continuous_neg).mul
        (continuous_id.min continuous_const)).integrableOn_Icc
  have hc : Continuous (fun s : ℝ =>
      ∫ r in Set.Icc a b, ρ (-r) * min r s) := by
    apply continuous_parametric_integral_of_continuous
    · fun_prop
    · exact isCompact_Icc
  simp_rw [hinner, mul_add]
  rw [integral_add]
  · rw [integral_mul_const, hmass, one_mul]
  · exact ((hρ.comp continuous_neg).mul continuous_const).integrableOn_Icc
  · exact ((hρ.comp continuous_neg).mul hc).integrableOn_Icc

theorem offsetScenery_affine_variance (a b x : ℝ) {ρ : ℝ → ℝ}
    (hρ : Continuous ρ) (hbulk : 0 ≤ x + a)
    (hmass : (∫ r in Set.Icc a b, ρ (-r)) = 1) :
    ‖offsetScenery a b x ρ‖^2 = x + offsetCorrection a b ρ := by
  rw [offsetScenery, LinearIsometry.norm_map]
  exact offsetDirection_affine_variance a b x hρ hbulk hmass

theorem concreteOffsetScenery_affine_variance (n : ℕ) (x : ℝ)
    (hbulk : (bump n).rOut ≤ x) :
    ‖offsetScenery (-(bump n).rOut) (bump n).rOut x (kernel n)‖^2 =
      x + offsetCorrection (-(bump n).rOut) (bump n).rOut (kernel n) := by
  apply offsetScenery_affine_variance _ _ _ (kernel_smooth n).continuous
  · linarith
  · simpa using concreteMollifier_mass n 0


end OperatorDerivativeRewrite.Foundation.IBMContinuousBulkVariance
