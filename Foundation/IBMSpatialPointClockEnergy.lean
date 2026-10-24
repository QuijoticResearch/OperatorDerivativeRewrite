import Foundation.IBMPhysicalForwardIntegral
import Foundation.IBMPhysicalWhiteNoiseObstruction
import Foundation.IBMClockOccupationConvolution
import Foundation.GaussianRealParameterizedItoScalar

/-! Actual spatial-L2 signed translated-mollifier clock fields and integrals.
Their norms are computed in spatial L2, not physical H^-1. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialPointClockEnergy
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProcess GaussianTimeProductL2
open IBMClockOccupationConvolution GaussianPredictableFull GaussianHermiteIntegrand
open GaussianHermiteRepresentation BrownianClockWeightedEnergy GaussianComplexHorizonIto
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

theorem profile_norm (n : ℕ) (r : ℝ) :
    ‖profileClass n r‖ = ‖IBMPhysicalWhiteNoiseObstruction.profile n‖ := by
  exact (IBMSchwartzPhysicalGlobalBounds.translated_norm _ _ _ r).trans
    (IBMSchwartzPhysicalGlobalBounds.translated_norm _ _ _ 0).symm

def spatial (n : ℕ) (r : ℝ) : TimeHilbert :=
  BrownianSignIntegral.signum r • profileClass n |r|

theorem spatial_stronglyMeasurable (n : ℕ) : StronglyMeasurable (spatial n) :=
  BrownianSignIntegral.signum_measurable.stronglyMeasurable.smul
    ((profileClass_continuous n).stronglyMeasurable.comp_measurable continuous_abs.measurable)

theorem spatial_bound (n : ℕ) (r : ℝ) :
    ‖spatial n r‖ ≤ ‖IBMPhysicalWhiteNoiseObstruction.profile n‖ := by
  rw [spatial, norm_smul, profile_norm]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (BrownianSignIntegral.signum_bound r) (norm_nonneg (IBMPhysicalWhiteNoiseObstruction.profile n))

theorem spatial_energy (n : ℕ) (r : ℝ) (hr : r ≠ 0) :
    ‖spatial n r‖^2 = ‖IBMPhysicalWhiteNoiseObstruction.profile n‖^2 := by
  rw [spatial, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, profile_norm,
    BrownianSignIntegral.signum_sq hr, one_mul]

def raw (n : ℕ) (z : ℝ × SampleSpace) : TimeHilbert := spatial n (sigma z)

theorem raw_memLp (n : ℕ) (T : ℝ≥0) :
    MemLp (raw n) 2 (PredictableRealL2.horizonMeasure T gaussianProduct) := by
  apply (memLp_const ‖IBMPhysicalWhiteNoiseObstruction.profile n‖).mono'
    ((spatial_stronglyMeasurable n).comp_measurable sigma_measurable).aestronglyMeasurable
  exact Eventually.of_forall fun z => spatial_bound n (sigma z)

theorem raw_predictable (n : ℕ) (T : ℝ≥0) :
    AEStronglyMeasurable[PredictableRealL2.predictable naturalFiltration]
      (raw n) (PredictableRealL2.horizonMeasure T gaussianProduct) := by
  obtain ⟨b,hb,he⟩ := ((mem_fullPredictable_iff _).mp (hermiteIntegrand 1 T).property).1
  refine ⟨spatial n ∘ b, (spatial_stronglyMeasurable n).comp_measurable hb.measurable, ?_⟩
  filter_upwards [ae_restrict_of_ae he,
    ae_restrict_of_ae (BrownianSignIntegral.brownian_field_joint T),
    ae_restrict_mem (PredictableRealL2.horizon_measurable T)] with z hb hB hz
  change spatial n (sigma z) = spatial n (b z)
  rw [← hb, hB, indicator_of_mem hz]

def input (n : ℕ) (T : ℝ≥0) : lpMeas TimeHilbert ℝ
    (PredictableRealL2.predictable naturalFiltration) 2
    (PredictableRealL2.horizonMeasure T gaussianProduct) :=
  ⟨(raw_memLp n T).toLp (raw n),
    (raw_predictable n T).congr (raw_memLp n T).coeFn_toLp.symm⟩

theorem input_ae (n : ℕ) (T : ℝ≥0) : (input n T).val =ᵐ[
    PredictableRealL2.horizonMeasure T gaussianProduct] raw n :=
  (raw_memLp n T).coeFn_toLp

def trim (n : ℕ) (T : ℝ≥0) : Lp TimeHilbert 2 (predictableMeasure T) :=
  lpMeasToLpTrimLie TimeHilbert ℝ 2
    (PredictableRealL2.horizonMeasure T gaussianProduct)
    (PredictableRealL2.predictable_le naturalFiltration) (input n T)

def integralValue (n : ℕ) (T : ℝ≥0) : Lp TimeHilbert 2 gaussianProduct :=
  GaussianParameterizedIto.realIntegral volume T (trim n T)

theorem integral_energy (n : ℕ) (T : ℝ≥0) :
    ‖integralValue n T‖^2 = (T : ℝ)*‖IBMPhysicalWhiteNoiseObstruction.profile n‖^2 := by
  rw [integralValue, (GaussianParameterizedIto.realIntegral volume T).norm_map]
  have ht : ‖trim n T‖ = ‖(input n T).val‖ :=
    (lpMeasToLpTrimLie TimeHilbert ℝ 2
      (PredictableRealL2.horizonMeasure T gaussianProduct)
      (PredictableRealL2.predictable_le naturalFiltration)).norm_map (input n T)
  rw [ht, BochnerL2Dominated.norm_sq_integral]
  have he : (fun z => ‖(input n T).val z‖^2) =ᵐ[
      PredictableRealL2.horizonMeasure T gaussianProduct]
        fun _ => ‖IBMPhysicalWhiteNoiseObstruction.profile n‖^2 := by
    filter_upwards [input_ae n T, sigma_nonzero T] with z hi hz
    rw [hi]
    exact spatial_energy n (sigma z) hz
  rw [integral_congr_ae he]
  rw [PredictableRealL2.horizonMeasure_eq_product T gaussianProduct]
  simp [Measure.real, Measure.prod_apply, Real.volume_Ioc, mul_comm]

theorem integral_norm (n : ℕ) (T : ℝ≥0) :
    ‖integralValue n T‖ = Real.sqrt T*‖IBMPhysicalWhiteNoiseObstruction.profile n‖ := by
  have he := integral_energy n T
  have ht := Real.sq_sqrt T.coe_nonneg
  nlinarith [norm_nonneg (integralValue n T),
    mul_nonneg (Real.sqrt_nonneg T) (norm_nonneg (IBMPhysicalWhiteNoiseObstruction.profile n))]

theorem integral_norm_escape (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => ‖integralValue n T‖) atTop atTop := by
  have hp : Tendsto (fun n => ‖IBMPhysicalWhiteNoiseObstruction.profile n‖) atTop atTop := by
    simpa only [IBMPhysicalNoiseRealization.physicalNoise.norm_map] using
      IBMPhysicalWhiteNoiseObstruction.whiteNoise_norm_escape
  simpa only [integral_norm] using hp.const_mul_atTop
    (Real.sqrt_pos.mpr (show (0 : ℝ) < T from hT))

end OperatorDerivativeRewrite.Foundation.IBMSpatialPointClockEnergy
