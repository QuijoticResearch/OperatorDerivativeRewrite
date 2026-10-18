import Foundation.HigherEvenBandHeatLimit
import Foundation.SignedDensityIntegral

/-! Actual complex process approximations realize the signed heat kernel on an entire Fourier test domain. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherEvenSignedRealization
open BandLimitedComplexExtension HigherEvenRenewalEnergy
open HigherHeatSignedLaws HigherHeatCylinderFourier

theorem phase_identity (ξ x : ℝ) :
    phase (-(ξ/(2*Real.pi))) x = Complex.exp (Complex.I*(ξ : ℂ)*(x : ℂ)) := by
  rw [phase,Real.fourierChar_apply]
  congr 1
  push_cast
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

theorem kernel_exponential (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (ξ : ℝ) :
    (∫ x : ℝ, Complex.exp (Complex.I*(ξ : ℂ)*(x : ℂ))*(realKernel m hm t ht x : ℂ)) =
      (Real.exp (-(t : ℝ)*ξ^(2*m)) : ℂ) := by
  simp_rw [← phase_identity]
  rw [kernel_fourier,HigherHeatL2.symbol]
  congr 2
  have hp : 2*Real.pi ≠ 0 := by positivity
  have he : 2*Real.pi*(-(ξ/(2*Real.pi))) = -ξ := by field_simp
  rw [he,neg_pow,Even.neg_one_pow (even_two_mul m),one_mul]

theorem kernel_frequency_integrable (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R)) :
    Integrable (fun p : ℝ × ℝ => φ p.1*Complex.exp (Complex.I*(p.1 : ℂ)*(p.2 : ℂ))*
      (realKernel m hm t ht p.2 : ℂ)) ((band R).prod volume) := by
  have hK : Integrable (fun x : ℝ => (realKernel m hm t ht x : ℂ)) :=
    (realKernel m hm t ht).integrable.ofReal
  have hme : Measurable (fun p : ℝ × ℝ => Complex.exp (Complex.I*(p.1 : ℂ)*(p.2 : ℂ))*
      (realKernel m hm t ht p.2 : ℂ)) := by fun_prop
  apply (hφ.norm.mul_prod hK.norm).mono'
    (by
      have hprod : AEStronglyMeasurable (fun p : ℝ × ℝ => φ p.1*(Complex.exp
        (Complex.I*(p.1 : ℂ)*(p.2 : ℂ))*(realKernel m hm t ht p.2 : ℂ)))
          ((band R).prod volume) :=
        hφ.aestronglyMeasurable.comp_fst.mul hme.aestronglyMeasurable
      simpa only [← mul_assoc] using hprod)
  apply Eventually.of_forall
  intro p
  change ‖φ p.1*Complex.exp (Complex.I*(p.1 : ℂ)*(p.2 : ℂ))*
    (realKernel m hm t ht p.2 : ℂ)‖ ≤ ‖φ p.1‖*‖(realKernel m hm t ht p.2 : ℂ)‖
  have he : ‖Complex.exp (Complex.I*(p.1 : ℂ)*(p.2 : ℂ))‖ = 1 := by
    rw [← phase_identity,phase_norm]
  simp [he]

theorem kernel_pairing (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R)) :
    (∫ x : ℝ, extension R φ (x : ℂ)*(realKernel m hm t ht x : ℂ)) =
      ∫ ξ, φ ξ*(Real.exp (-(t : ℝ)*ξ^(2*m)) : ℂ) ∂band R := by
  have hi := kernel_frequency_integrable m hm t ht R φ hφ
  unfold extension
  simp_rw [← integral_mul_const]
  rw [← integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards with ξ
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  simpa only [mul_assoc] using congrArg (fun z : ℂ => φ ξ*z) (kernel_exponential m hm t ht ξ)

theorem kernel_extension_integrable (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R)) :
    Integrable (fun x : ℝ => extension R φ (x : ℂ)*(realKernel m hm t ht x : ℂ)) := by
  have hi := (kernel_frequency_integrable m hm t ht R φ hφ).integral_prod_right
  simpa only [extension,integral_mul_const] using hi

theorem real_extension_bound (R : ℝ≥0) (φ : ℝ → ℂ) (x : ℝ) :
    ‖extension R φ (x : ℂ)‖ ≤ ∫ ξ, ‖φ ξ‖ ∂band R := by
  unfold extension
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  filter_upwards with ξ
  rw [norm_mul,← phase_identity,phase_norm,mul_one]

theorem signed_law_pairing (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R)) :
    (∫ᵛ x : ℝ, extension R φ (x : ℂ) ∂<•law m hm t ht) =
      ∫ ξ, φ ξ*(Real.exp (-(t : ℝ)*ξ^(2*m)) : ℂ) ∂band R := by
  have he := SignedDensityIntegral.integral_density volume (realKernel m hm t ht)
    (realKernel m hm t ht).integrable (realKernel m hm t ht).continuous.measurable
    (fun x : ℝ => extension R φ (x : ℂ))
    ((extension_continuous R φ hφ).measurable.comp Complex.continuous_ofReal.measurable)
    (∫ ξ, ‖φ ξ‖ ∂band R) (real_extension_bound R φ)
  change (∫ᵛ x : ℝ, extension R φ (x : ℂ)
    ∂<•volume.withDensityᵥ (realKernel m hm t ht)) = _
  rw [he]
  simpa only [Complex.real_smul,mul_comm] using kernel_pairing m hm t ht R φ hφ

theorem actual_expectation_tendsto (m : ℕ) [NeZero m] (t : ℝ≥0) (ht : 0 < t)
    (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R)) :
    Tendsto (fun n => ∫ ω, extension R φ (HigherEvenRenewalProcess.process m
      (smallAmplitude n) (acceleratedTime m n t) ω) ∂HigherEvenRenewalProcess.probability m)
      atTop (𝓝 (∫ x : ℝ, extension R φ (x : ℂ)*
        (realKernel m (NeZero.pos m) t ht x : ℂ))) := by
  rw [kernel_pairing m (NeZero.pos m) t ht R φ hφ]
  exact HigherEvenBandHeatLimit.actual_expectation_tendsto m t R φ hφ

theorem actual_signed_law_limit (m : ℕ) [NeZero m] (t : ℝ≥0) (ht : 0 < t)
    (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R)) :
    Tendsto (fun n => ∫ ω, extension R φ (HigherEvenRenewalProcess.process m
      (smallAmplitude n) (acceleratedTime m n t) ω) ∂HigherEvenRenewalProcess.probability m)
      atTop (𝓝 (∫ᵛ x : ℝ, extension R φ (x : ℂ) ∂<•law m (NeZero.pos m) t ht)) := by
  rw [signed_law_pairing m (NeZero.pos m) t ht R φ hφ]
  exact HigherEvenBandHeatLimit.actual_expectation_tendsto m t R φ hφ

end OperatorDerivativeRewrite.Foundation.HigherEvenSignedRealization
