import Foundation.CubeGroundMass
import Foundation.CubeSlabL2
import Foundation.BochnerL2Dominated

/-! Exact weighted domains for the actual Wilson ground law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.CubeNativeL2Domain
open CubeTemporalSlab CubeWilsonSlab CubeSlabGround
attribute [local irreducible] CubeWilsonSlab.kernel boundaryHaar
variable {beta : ℝ} (d : GroundData beta)
private instance stationary_probability : IsProbabilityMeasure d.stationary := d.stationary_probability

/-- Integrability transport uses the actual normalized square-ground density. -/
theorem integrable_iff (f : State → ℝ) :
    Integrable f d.stationary ↔ Integrable (fun U => d.function U^2*f U) boundaryHaar := by
  change Integrable f ((ENNReal.ofReal (SignedDensityProbabilitySampling.mass boundaryHaar
    (fun U => d.function U^2)))⁻¹ • SignedAbsoluteIntegration.absoluteDensity boundaryHaar
      (fun U => d.function U^2)) ↔ _
  have hm : SignedDensityProbabilitySampling.mass boundaryHaar
      (fun U => d.function U^2)=d.normalizer := by
    unfold SignedDensityProbabilitySampling.mass GroundData.normalizer
    simp only [abs_pow,sq_abs]
  rw [hm,integrable_inv_smul_measure
    (ne_of_gt (ENNReal.ofReal_pos.mpr d.normalizer_pos)) ENNReal.ofReal_ne_top]
  unfold SignedAbsoluteIntegration.absoluteDensity
  simp only [abs_pow,sq_abs]
  have h := integrable_withDensity_iff_integrable_smul₀'
    (d.measurable.pow_const 2).ennreal_ofReal.aemeasurable
    (ae_of_all boundaryHaar (fun _ => ENNReal.ofReal_lt_top)) (g := f)
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul] using h

/-- The strictly positive ground density has exactly the Haar null sets. -/
theorem ae_iff (p : State → Prop) :
    (∀ᵐ U ∂d.stationary,p U) ↔ ∀ᵐ U ∂boundaryHaar,p U := by
  change (∀ᵐ U ∂(ENNReal.ofReal (SignedDensityProbabilitySampling.mass boundaryHaar
    (fun U => d.function U^2)))⁻¹ • SignedAbsoluteIntegration.absoluteDensity boundaryHaar
      (fun U => d.function U^2),p U) ↔ _
  rw [Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)]
  unfold SignedAbsoluteIntegration.absoluteDensity
  simp only [abs_pow,sq_abs]
  rw [ae_withDensity_iff (d.measurable.pow_const 2).ennreal_ofReal]
  constructor
  · intro h
    filter_upwards [h] with U hU
    exact hU (ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (d.function_pos U))))
  · intro h
    filter_upwards [h] with U hU
    exact fun _ => hU
/-- No boundedness assumption on the observable is needed. -/
theorem weighted_memLp (f : State → ℝ) (hf : Measurable f)
    (hmem : MemLp f 2 d.stationary) :
    MemLp (fun U => d.function U*f U) 2 boundaryHaar := by
  apply (memLp_two_iff_integrable_sq (d.measurable.mul hf).aestronglyMeasurable).mpr
  have h := (integrable_iff d (fun U => f U^2)).mp hmem.integrable_sq
  simpa only [Pi.mul_apply,mul_pow] using h

/-- Exact native-to-Haar squared norm, including the ground normalization. -/
theorem weighted_square_integral (f : State → ℝ) (hmem : MemLp f 2 d.stationary) :
    (∫ U,(d.function U*f U)^2 ∂boundaryHaar)=d.normalizer*‖hmem.toLp f‖^2 := by
  have hn := BochnerL2Dominated.norm_sq_integral (hmem.toLp f)
  have hi : (∫ U,‖hmem.toLp f U‖^2 ∂d.stationary)=(∫ U,f U^2 ∂d.stationary) := by
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hmem] with U hU
    simp only [hU,Real.norm_eq_abs,sq_abs]
  rw [hi,d.stationary_integral (fun U => f U^2)] at hn
  have he : (fun U => d.function U^2*f U^2)=(fun U => (d.function U*f U)^2) := by
    funext U
    ring
  rw [he] at hn
  exact ((eq_div_iff d.normalizer_pos.ne').mp hn).symm.trans (mul_comm _ _)

/-- Cauchy--Schwarz for the Haar integral of a native L2 observable times its ground. -/
theorem weighted_abs_integral_bound (f : State → ℝ) (hf : Measurable f)
    (hmem : MemLp f 2 d.stationary) :
    (∫ U,d.function U*|f U| ∂boundaryHaar) ≤ Real.sqrt d.normalizer*‖hmem.toLp f‖ := by
  have hmem' := weighted_memLp d f hf hmem
  have hmabs : MemLp (fun U => |d.function U*f U|) 2 boundaryHaar := by
    simpa only [Real.norm_eq_abs] using hmem'.norm
  have h := variance_nonneg (fun U => |d.function U*f U|) boundaryHaar
  rw [variance_eq_sub hmabs] at h
  have he : (fun U => |d.function U*f U|)=(fun U => d.function U*|f U|) := by
    funext U
    rw [abs_mul,abs_of_pos (d.function_pos U)]
  have hs : (∫ U,|d.function U*f U|^2 ∂boundaryHaar)=d.normalizer*‖hmem.toLp f‖^2 := by
    simpa only [sq_abs] using weighted_square_integral d f hmem
  simp only [Pi.pow_apply] at h
  rw [hs,he] at h
  have hp := Real.sq_sqrt d.normalizer_pos.le
  have hn := mul_nonneg (Real.sqrt_nonneg d.normalizer) (norm_nonneg (hmem.toLp f))
  nlinarith [sq_nonneg ((∫ U,d.function U*|f U| ∂boundaryHaar)+
    Real.sqrt d.normalizer*‖hmem.toLp f‖)]

end OperatorDerivativeRewrite.Foundation.CubeNativeL2Domain
