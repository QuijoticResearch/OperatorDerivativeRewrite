import Foundation.SignedSchwartzHigherWeights

/-! Exact signed L1 domain transport by a measurable density ratio. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.SignedDensityL1Transport
open SignedAbsoluteIntegration
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

theorem weighted_norm_ae (K N W : Ω → ℝ)
    (hc : (fun x => K x*W x) =ᵐ[μ] N) (G : Ω → ℂ) :
    (fun x => ‖|K x| • ((W x:ℂ)*G x)‖) =ᵐ[μ]
      (fun x => ‖|N x| • G x‖) := by
  filter_upwards [hc] with x hx
  simp only [norm_smul, Real.norm_eq_abs, abs_abs, norm_mul, Complex.norm_real]
  rw [← mul_assoc, ← abs_mul, hx]

theorem integrable_iff (K N W : Ω → ℝ) (hK : Measurable K) (hN : Measurable N)
    (hW : Measurable W) (hc : (fun x => K x*W x) =ᵐ[μ] N)
    (G : Ω → ℂ) (hG : Measurable G) :
    Integrable (fun x => (W x:ℂ)*G x) (absoluteDensity μ K) ↔
      Integrable G (absoluteDensity μ N) := by
  rw [absolute_integrable_iff μ K hK, absolute_integrable_iff μ N hN]
  have hmK : Measurable (fun x => |K x|) := by
    simpa only [Real.norm_eq_abs] using hK.norm
  have hmN : Measurable (fun x => |N x|) := by
    simpa only [Real.norm_eq_abs] using hN.norm
  exact integrable_congr'
    (hmK.smul ((Complex.measurable_ofReal.comp hW).mul hG)).aestronglyMeasurable
    (hmN.smul hG).aestronglyMeasurable (weighted_norm_ae μ K N W hc G)

theorem norm_integral_eq (K N W : Ω → ℝ) (hK : Measurable K) (hN : Measurable N)
    (hc : (fun x => K x*W x) =ᵐ[μ] N) (G : Ω → ℂ) :
    (∫ x, ‖(W x:ℂ)*G x‖ ∂absoluteDensity μ K) =
      (∫ x, ‖G x‖ ∂absoluteDensity μ N) := by
  have hmK : Measurable (fun x => |K x|) := by
    simpa only [Real.norm_eq_abs] using hK.norm
  have hmN : Measurable (fun x => |N x|) := by
    simpa only [Real.norm_eq_abs] using hN.norm
  rw [absoluteDensity, absoluteDensity,
    integral_withDensity_eq_integral_toReal_smul hmK.ennreal_ofReal
      (Eventually.of_forall fun x => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul hmN.ennreal_ofReal
      (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hc] with x hx
  rw [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal (abs_nonneg _)]
  simp only [smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [← mul_assoc, ← abs_mul, hx]

theorem weighted_measure (K N W : Ω → ℝ) (hK : Measurable K) (hW : Measurable W)
    (hc : (fun x => K x*W x) =ᵐ[μ] N) :
    (absoluteDensity μ K).withDensity (fun x => (‖W x‖₊:ℝ≥0∞)) = absoluteDensity μ N := by
  have hmK : Measurable (fun x => |K x|) := by
    simpa only [Real.norm_eq_abs] using hK.norm
  rw [absoluteDensity, absoluteDensity, ← withDensity_mul μ hmK.ennreal_ofReal
    hW.nnnorm.coe_nnreal_ennreal]
  apply withDensity_congr_ae
  filter_upwards [hc] with x hx
  change ENNReal.ofReal |K x| * (‖W x‖₊:ℝ≥0∞) = ENNReal.ofReal |N x|
  have hw : (‖W x‖₊:ℝ≥0∞) = ENNReal.ofReal |W x| := Real.enorm_eq_ofReal_abs _
  rw [hw, ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, hx]

def modulusTransport (K N W : Ω → ℝ) (hK : Measurable K) (hW : Measurable W)
    (hc : (fun x => K x*W x) =ᵐ[μ] N) :
    Lp ℂ 1 (absoluteDensity μ N) →ₗᵢ[ℝ] Lp ℂ 1 (absoluteDensity μ K) := by
  rw [← weighted_measure μ K N W hK hW hc]
  exact withDensitySMulLI (absoluteDensity μ K) hW.nnnorm

theorem signed_integral_eq (K N W : Ω → ℝ) (hKi : Integrable K μ) (hNi : Integrable N μ)
    (hK : Measurable K) (hN : Measurable N) (hW : Measurable W)
    (hc : (fun x => K x*W x) =ᵐ[μ] N) (G : Ω → ℂ) (hG : Measurable G)
    (hi : Integrable G (absoluteDensity μ N)) :
    (∫ᵛ x, (W x:ℂ)*G x ∂<•μ.withDensityᵥ K) = (∫ᵛ x, G x ∂<•μ.withDensityᵥ N) := by
  rw [integral_density μ K hKi hK _
    ((integrable_iff μ K N W hK hN hW hc G hG).mpr hi),
    integral_density μ N hNi hN G hi]
  apply integral_congr_ae
  filter_upwards [hc] with x hx
  simp only [Complex.real_smul]
  rw [← mul_assoc, ← Complex.ofReal_mul, hx]

end OperatorDerivativeRewrite.Foundation.SignedDensityL1Transport
