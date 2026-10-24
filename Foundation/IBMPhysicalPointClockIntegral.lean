import Foundation.IBMPhysicalClockIto
import Foundation.IBMPhysicalPointClockField
import Foundation.IBMPhysicalRunningIto
import Foundation.IBMSchwartzPhysicalReflectedIto

/-! The actual signed-Dirac coefficient has an original physical H^-1
Brownian integral, agreeing with every actual scenery-tested scalar integral. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalPointClockIntegral
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 IBMPhysicalClockIto
open IBMPhysicalPointClockField

def integrand (n : ℕ) (T : ℝ≥0) : Domain T :=
  ⟨IBMSchwartzPhysicalClockIntegral.restriction T (field n T), (field_predictable n T).restrict.congr
    (LpToLpRestrictCLM_coeFn ℂ (PredictableRealL2.horizon T) (field n T)).symm⟩

def limitIntegrand (T : ℝ≥0) : Domain T :=
  ⟨IBMSchwartzPhysicalClockIntegral.restriction T (limitField T), (limitField_predictable T).restrict.congr
    (LpToLpRestrictCLM_coeFn ℂ (PredictableRealL2.horizon T) (limitField T)).symm⟩

theorem integrand_tendsto (T : ℝ≥0) :
    Tendsto (fun n => integrand n T) atTop (𝓝 (limitIntegrand T)) := by
  apply tendsto_subtype_rng.mpr
  exact (IBMSchwartzPhysicalClockIntegral.restriction T).continuous.tendsto _ |>.comp (field_tendsto T)

def integralValue (n : ℕ) (T : ℝ≥0) :
    Lp (H^{(-1 : ℝ)}(ℝ)) 2 gaussianProduct := integral T (integrand n T)

def limitIntegralValue (T : ℝ≥0) :
    Lp (H^{(-1 : ℝ)}(ℝ)) 2 gaussianProduct := integral T (limitIntegrand T)

theorem integralValue_tendsto (T : ℝ≥0) :
    Tendsto (fun n => integralValue n T) atTop (𝓝 (limitIntegralValue T)) :=
  (integral_isometry T).continuous.tendsto _ |>.comp (integrand_tendsto T)

theorem integralValue_difference_norm (n m : ℕ) (T : ℝ≥0) :
    ‖integralValue n T-integralValue m T‖ =
      ‖integrand n T-integrand m T‖ := by
  exact (dist_eq_norm _ _).symm.trans
    (((integral_isometry T).dist_eq (integrand n T) (integrand m T)).trans
      (dist_eq_norm _ _))

local instance : NormedSpace ℝ H^{(-1 : ℝ)}(ℝ) := NormedSpace.restrictScalars ℝ ℂ _

theorem integrand_ae (n : ℕ) (T : ℝ≥0) : (integrand n T).val =ᵐ[
    PredictableRealL2.horizonMeasure T gaussianProduct] fun z => spatial n (BrownianClockWeightedEnergy.sigma z) := by
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (PredictableRealL2.horizon T) (field n T),
    ae_restrict_of_ae (field_ae n T),
    ae_restrict_mem (PredictableRealL2.horizon_measurable T)] with z hr hf hz
  change (integrand n T).val z = _ at hr
  rw [hr, hf, Set.indicator_of_mem hz]

theorem limitIntegrand_ae (T : ℝ≥0) : (limitIntegrand T).val =ᵐ[
    PredictableRealL2.horizonMeasure T gaussianProduct] fun z => spatialLimit (BrownianClockWeightedEnergy.sigma z) := by
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (PredictableRealL2.horizon T) (limitField T),
    ae_restrict_of_ae (limitField_ae T),
    ae_restrict_mem (PredictableRealL2.horizon_measurable T)] with z hr hf hz
  change (limitIntegrand T).val z = _ at hr
  rw [hr, hf, Set.indicator_of_mem hz]

theorem integralValue_test (n : ℕ) (T : ℝ≥0) (L : IBMPhysicalWeakWiener.Tests) :
    L.compLpL 2 gaussianProduct (integralValue n T) =
      GaussianPredictableFull.itoIntegral (IBMPhysicalRunningIntegrand.native n T L) := by
  apply IBMSchwartzPhysicalReflectedIto.scalarization_full
  have he : (fun z => L ((integrand n T).val z)) =ᵐ[
      PredictableRealL2.horizonMeasure T gaussianProduct]
      fun z => IBMPhysicalRunningIntegrand.spatial n L (BrownianClockWeightedEnergy.sigma z) := by
    filter_upwards [integrand_ae n T] with z hz
    rw [hz, spatial, map_smul, smul_eq_mul,
      IBMPhysicalRunningIntegrand.spatial, IBMPhysicalRunningPrimitive.first_physical]
  exact (IBMPhysicalRunningIntegrand.native_coeFn n T L).trans
    ((ae_eq_restrict_iff_indicator_ae_eq (PredictableRealL2.horizon_measurable T)).mp he).symm

theorem limitIntegralValue_test (T : ℝ≥0) (L : IBMPhysicalWeakWiener.Tests) :
    L.compLpL 2 gaussianProduct (limitIntegralValue T) =
      GaussianPredictableFull.itoIntegral (IBMPhysicalRunningIntegrand.limitIntegrand T L) := by
  apply IBMSchwartzPhysicalReflectedIto.scalarization_full
  have he : (fun z => L ((limitIntegrand T).val z)) =ᵐ[
      PredictableRealL2.horizonMeasure T gaussianProduct]
      fun z => IBMPhysicalRunningIntegrand.spatialLimit L (BrownianClockWeightedEnergy.sigma z) := by
    filter_upwards [limitIntegrand_ae T] with z hz
    rw [hz, spatialLimit, map_smul, smul_eq_mul]
    rfl
  exact (IBMPhysicalRunningIntegrand.limitField_coeFn T L).trans
    ((ae_eq_restrict_iff_indicator_ae_eq (PredictableRealL2.horizon_measurable T)).mp he).symm

end OperatorDerivativeRewrite.Foundation.IBMPhysicalPointClockIntegral
