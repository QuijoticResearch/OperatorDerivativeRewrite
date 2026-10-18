import Foundation.IBMQuarticHeatDomain

/-! Actual time/positive-space Fubini for the quartic second-source
curvature, using the proved heat-potential Bochner domain. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMQuarticHeatFubini
open InfiniteGaussian IBMClockHeatPotential IBMClockHeatOccupation
open IBMQuarticHeatDomain

def heatValue (n : ℕ) (p : ℝ × ℝ) : GaussianL2 :=
  (2*heatKernel p.1 p.2) •
    GaussianNumberSectors.projection 2 (IBMQuarticSecondGeometry.spatialQuartic n p.2)

theorem heatValue_stronglyMeasurable (n : ℕ) : StronglyMeasurable (heatValue n) := by
  have hm : Measurable (fun p : ℝ × ℝ => heatKernel p.1 p.2) :=
    (IBMClockGaussianTail.density_continuous.measurable.comp
      (measurable_snd.div (Real.continuous_sqrt.measurable.comp measurable_fst))).div
      (Real.continuous_sqrt.measurable.comp measurable_fst)
  exact (hm.const_mul 2).stronglyMeasurable.smul
    ((IBMQuarticSpatialWeakLimit.projected_continuous n).stronglyMeasurable.comp_measurable measurable_snd)

theorem heatValue_time_integrable (n : ℕ) (r : ℝ) (T : ℝ≥0) :
    Integrable (fun s => heatValue n (s,r)) (volume.restrict (Ioc 0 (T : ℝ))) := by
  exact (((heatKernel_time_integrable r T.coe_nonneg).const_mul 2).1).smul_const
    (GaussianNumberSectors.projection 2 (IBMQuarticSecondGeometry.spatialQuartic n r))

theorem heatValue_time_integral (n : ℕ) {r : ℝ} (hr : 0 ≤ r) (T : ℝ≥0) (hT : 0 < T) :
    (∫ s in Ioc 0 (T : ℝ), heatValue n (s,r)) = potential T r •
      GaussianNumberSectors.projection 2 (IBMQuarticSecondGeometry.spatialQuartic n r) := by
  unfold heatValue
  simp only [Prod.fst, Prod.snd]
  rw [← intervalIntegral.integral_of_le T.coe_nonneg,
    intervalIntegral.integral_smul_const, intervalIntegral.integral_const_mul,
    ← potential_eq_time_integral (NNReal.coe_pos.mpr hT) hr]

theorem heatValue_time_norm_integral (n : ℕ) {r : ℝ} (hr : 0 ≤ r) (T : ℝ≥0) (hT : 0 < T) :
    (∫ s in Ioc 0 (T : ℝ), ‖heatValue n (s,r)‖) = ‖potential T r •
      GaussianNumberSectors.projection 2 (IBMQuarticSecondGeometry.spatialQuartic n r)‖ := by
  have he (s : ℝ) : ‖heatValue n (s,r)‖ = (2*heatKernel s r) *
      ‖GaussianNumberSectors.projection 2 (IBMQuarticSecondGeometry.spatialQuartic n r)‖ := by
    rw [heatValue, norm_smul, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (heatKernel_nonneg s r))]
  simp_rw [he]
  rw [integral_mul_const, ← intervalIntegral.integral_of_le T.coe_nonneg,
    intervalIntegral.integral_const_mul, ← potential_eq_time_integral (NNReal.coe_pos.mpr hT) hr,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (potential_nonneg (NNReal.coe_pos.mpr hT) hr)]

theorem heatValue_integrable (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    Integrable (heatValue n) ((volume.restrict (Ioc 0 (T : ℝ))).prod (volume.restrict (Ioi 0))) := by
  apply (integrable_prod_iff' (heatValue_stronglyMeasurable n).aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall fun r => heatValue_time_integrable n r T, ?_⟩
  apply (weighted_curvature_integrableOn n T hT).norm.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  exact (heatValue_time_norm_integral n (show 0 ≤ r from le_of_lt hr) T hT).symm

theorem time_space_identity (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    (∫ s in Ioc 0 (T : ℝ), ∫ r in Ioi 0, heatValue n (s,r)) =
      ∫ r in Ioi 0, potential T r •
        GaussianNumberSectors.projection 2 (IBMQuarticSecondGeometry.spatialQuartic n r) := by
  rw [integral_integral_swap (f := fun s r => heatValue n (s,r)) (heatValue_integrable n T hT)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  exact heatValue_time_integral n (show 0 ≤ r from le_of_lt hr) T hT

end OperatorDerivativeRewrite.Foundation.IBMQuarticHeatFubini
