import Foundation.IBMSpatialSignedReconstruction
import Foundation.BochnerL2MajorantRealization
import Foundation.BrownianClockWeightedEnergy

/-! Actual diagonal occupation along the constructed continuous Brownian clock.
The pathwise action exists on all bounded continuous tests; convergence of the
native spatial kernels is asserted only on the previously verified domain. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialPathOccupation
open InfiniteGaussian IBMSpatialBoundedTestOperator IBMClockOverlapEnergy
open IBMConstructedSources IBMSpatialKernelOccupation

def integrand (F : Tests) (p : ℝ × SampleSpace) : ℝ :=
  F (|clockPath p.2 p.1.toNNReal|,|clockPath p.2 p.1.toNNReal|)

theorem integrand_measurable (F : Tests) : Measurable (integrand F) :=
  F.continuous.measurable.comp ((BrownianClockWeightedEnergy.sigma_measurable.norm).prodMk
    (BrownianClockWeightedEnergy.sigma_measurable.norm))

theorem integrand_bound (F : Tests) (p : ℝ × SampleSpace) : ‖integrand F p‖ ≤ ‖F‖ :=
  F.norm_coe_le_norm _

theorem integrand_time_integrable (F : Tests) (T : ℝ≥0) (Y : SampleSpace) :
    Integrable (fun t => integrand F (t,Y)) (window T) :=
  Integrable.of_bound (((integrand_measurable F).comp
    (measurable_id.prodMk measurable_const)).aestronglyMeasurable) ‖F‖
      (ae_of_all _ fun t => integrand_bound F (t,Y))

def pathValue (F : Tests) (T : ℝ≥0) (Y : SampleSpace) : ℝ :=
  ∫ t, integrand F (t,Y) ∂window T

theorem pathValue_measurable (F : Tests) (T : ℝ≥0) : Measurable (pathValue F T) :=
  ((integrand_measurable F).stronglyMeasurable.integral_prod_left' (μ := window T)).measurable

theorem pathValue_bound (F : Tests) (T : ℝ≥0) (Y : SampleSpace) :
    ‖pathValue F T Y‖ ≤ (T:ℝ)*‖F‖ := by
  have hb := norm_integral_le_of_norm_le_const (μ := window T)
    (ae_of_all _ fun t => integrand_bound F (t,Y))
  simpa [pathValue,window,Measure.real,Real.volume_Ioc,
    ENNReal.toReal_ofReal T.coe_nonneg,mul_comm] using hb

theorem pathValue_integrable (F : Tests) (T : ℝ≥0) :
    Integrable (pathValue F T) gaussianProduct :=
  Integrable.of_bound (pathValue_measurable F T).aestronglyMeasurable ((T:ℝ)*‖F‖)
    (ae_of_all _ fun Y => pathValue_bound F T Y)

def value (F : Tests) (T : ℝ≥0) : Values := (pathValue_integrable F T).toL1 _

theorem value_actual (F : Tests) (T : ℝ≥0) :
    value F T =ᵐ[gaussianProduct] pathValue F T := (pathValue_integrable F T).coeFn_toL1

theorem value_norm_bound (F : Tests) (T : ℝ≥0) : ‖value F T‖ ≤ (T:ℝ)*‖F‖ := by
  rw [value,L1.norm_of_fun_eq_integral_norm]
  have hb := integral_mono (pathValue_integrable F T).norm (integrable_const ((T:ℝ)*‖F‖))
    (pathValue_bound F T)
  simpa [Measure.real] using hb

theorem pathValue_add (F G : Tests) (T : ℝ≥0) (Y : SampleSpace) :
    pathValue (F+G) T Y = pathValue F T Y+pathValue G T Y := by
  exact integral_add (integrand_time_integrable F T Y) (integrand_time_integrable G T Y)

theorem pathValue_smul (c : ℝ) (F : Tests) (T : ℝ≥0) (Y : SampleSpace) :
    pathValue (c • F) T Y = c*pathValue F T Y := integral_const_mul c _

def pathOperator (T : ℝ≥0) (Y : SampleSpace) : Tests →L[ℝ] ℝ :=
  ({ toFun := fun F => pathValue F T Y
     map_add' := fun F G => pathValue_add F G T Y
     map_smul' := fun c F => pathValue_smul c F T Y } : Tests →ₗ[ℝ] ℝ).mkContinuous
    (T:ℝ) (fun F => pathValue_bound F T Y)

theorem pathOperator_norm (T : ℝ≥0) (Y : SampleSpace) : ‖pathOperator T Y‖ ≤ (T:ℝ) :=
  (pathOperator T Y).opNorm_le_bound T.coe_nonneg (fun F => pathValue_bound F T Y)

theorem value_add (F G : Tests) (T : ℝ≥0) : value (F+G) T = value F T+value G T := by
  apply Lp.ext
  filter_upwards [value_actual (F+G) T,value_actual F T,value_actual G T,
    Lp.coeFn_add (value F T) (value G T)] with Y ha hf hg hs
  rw [ha,hs,Pi.add_apply,hf,hg,pathValue_add]

theorem value_smul (c : ℝ) (F : Tests) (T : ℝ≥0) : value (c • F) T = c • value F T := by
  apply Lp.ext
  filter_upwards [value_actual (c • F) T,value_actual F T,Lp.coeFn_smul c (value F T)] with Y ha hf hs
  rw [ha,hs,Pi.smul_apply,hf,smul_eq_mul,pathValue_smul]

def operator (T : ℝ≥0) : Tests →L[ℝ] Values :=
  ({ toFun := fun F => value F T
     map_add' := fun F G => value_add F G T
     map_smul' := fun c F => value_smul c F T } : Tests →ₗ[ℝ] Values).mkContinuous
    (T:ℝ) (fun F => value_norm_bound F T)

theorem old_drift_actual (F : Tests) {K : ℝ≥0} (hF : LipschitzWith K F) (T : ℝ≥0) :
    IBMClockWeightedFoldedVariation.drift (diagonal F) (diagonal_lipschitz F hF) T =ᵐ[gaussianProduct]
      pathValue F T := by
  unfold IBMClockWeightedFoldedVariation.drift
  rw [intervalIntegral.integral_of_le T.coe_nonneg]
  apply BochnerL2MajorantRealization.integral_coeFn_ae
    (g := integrand F) (B := fun _ => ‖F‖)
  · exact (((GaussianLipschitzIntegrands.valueL2_continuous (diagonal_lipschitz F hF)).comp
      continuous_real_toNNReal).intervalIntegrable 0 (T:ℝ)).1
  · exact (integrand_measurable F).stronglyMeasurable
  · apply ae_of_all
    intro t
    filter_upwards [GaussianLipschitzIntegrands.valueL2_coeFn
      (diagonal_lipschitz F hF) t.toNNReal,clockPath_coordinate_ae t.toNNReal] with Y hv hc
    rw [hv]
    change F (|GaussianTimeProcess.process t.toNNReal Y|,|GaussianTimeProcess.process t.toNNReal Y|) =
      F (|clockPath Y t.toNNReal|,|clockPath Y t.toNNReal|)
    rw [hc]
  · exact memLp_const ‖F‖
  · exact ae_of_all _ fun p => integrand_bound F p

theorem old_occupation_eq (F : Tests) {K : ℝ≥0} (hF : LipschitzWith K F) (T : ℝ≥0) :
    occupation F hF T = value F T := by
  apply Lp.ext
  filter_upwards [IBMClippedClockStrongLimit.clockL1_actual
    (IBMClockWeightedFoldedVariation.drift (diagonal F) (diagonal_lipschitz F hF) T),
    old_drift_actual F hF T,value_actual F T] with Y hl hd hv
  exact hl.trans (hd.trans hv.symm)

end OperatorDerivativeRewrite.Foundation.IBMSpatialPathOccupation
