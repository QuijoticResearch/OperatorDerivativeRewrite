import Foundation.IBMFoldedHeatTimeEnergy
import Foundation.BrownianClockWeightedEnergy

/-! Finite expected energy for the actual continuous Brownian clock substituted
into the folded heat candidate. No canonical-integrand identification is assumed. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMFoldedHeatClockEnergy
open InfiniteGaussian BrownianClockWeightedEnergy IBMFoldedHeatTimeEnergy

def raw (T : ℝ≥0) (z : ℝ × SampleSpace) : ℝ :=
  energy T (fun s => sigma (s,z.2)) z.1

theorem raw_measurable (T : ℝ≥0) : Measurable (raw T) := by
  change Measurable (fun z : ℝ × SampleSpace =>
    (1-Real.exp (-(sigma z)^2/((T : ℝ)-z.1)))/
      (2*Real.sqrt (Real.pi*((T : ℝ)-z.1))))
  have hσ := sigma_measurable
  fun_prop

theorem raw_integrable (T : ℝ≥0) : Integrable (raw T) (base T) := by
  have hi : Integrable (fun z : ℝ × SampleSpace =>
      (2*Real.sqrt Real.pi)⁻¹*((T : ℝ)-z.1)^(-(1/2 : ℝ))) (base T) := by
    rw [base, PredictableRealL2.horizonMeasure_eq_product]
    have he : Integrable (fun s => (2*Real.sqrt Real.pi)⁻¹*
        ((T : ℝ)-s)^(-(1/2 : ℝ))) (volume.restrict (Ioc 0 (T : ℝ))) := by
      simpa only [IntegrableOn, intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg]
        using envelope_intervalIntegrable (T : ℝ)
    simpa only [mul_one] using he.mul_prod
      (integrable_const (1 : ℝ) : Integrable (fun _ : SampleSpace => (1 : ℝ)) gaussianProduct)
  apply hi.mono' (raw_measurable T).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (PredictableRealL2.horizon_measurable T)] with z hz
  have hs : z.1 ≤ (T : ℝ) := hz.1.2
  rw [Real.norm_eq_abs, raw,
    abs_of_nonneg (energy_nonneg T (fun s => sigma (s,z.2)) hs)]
  exact energy_bound T (fun s => sigma (s,z.2)) hs

theorem clock_path_energy (T : ℝ≥0) (Y : SampleSpace) :
    IntervalIntegrable (fun s => raw T (s,Y)) volume 0 T := by
  apply energy_intervalIntegrable T.coe_nonneg
  exact sigma_measurable.comp (measurable_id.prodMk measurable_const)

theorem clock_spatial_energy (T : ℝ≥0) (s : ℝ) (hs : s < T) (Y : SampleSpace) :
    ‖IBMFoldedHeatEnergy.spatial (sigma (s,Y)) (Real.toNNReal ((T : ℝ)-s)) (by
      exact_mod_cast Real.toNNReal_pos.mpr (sub_pos.mpr hs))‖^2 = raw T (s,Y) :=
  actual_spatial_energy T (fun t => sigma (t,Y)) hs

end OperatorDerivativeRewrite.Foundation.IBMFoldedHeatClockEnergy
