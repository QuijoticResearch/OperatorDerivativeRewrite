import Foundation.MarkedRenewalExponentialTransform
import Foundation.BandLimitedComplexExtension

/-! Compact-frequency expectations for actual bounded-mark renewal processes. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.MarkedRenewalFourierTests
open MarkedRenewalRealization BandLimitedComplexExtension
variable {A : Type*} [MeasurableSpace A]

theorem radial_integrable (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (hz : Measurable z) (C : ℝ) (hC : ∀ k, ‖z k‖ ≤ C) (t : ℝ≥0)
    (B : ℝ) (hB : 0 ≤ B) :
    Integrable (fun ω => Real.exp (B*‖process z t ω‖)) (probability μ) := by
  apply (MarkedRenewalExponentialTransform.count_geometric_integrable μ t
    (Real.exp (B*C))).mono'
      ((Real.continuous_exp.measurable.comp
        (measurable_const.mul (process_measurable z hz t).norm)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro ω
  change ‖Real.exp (B*‖process z t ω‖)‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ B*((ExponentialRenewalCount.count t ω.1 : ℝ)*C) :=
      mul_le_mul_of_nonneg_left
        (position_norm_bound z C hC (ExponentialRenewalCount.count t ω.1) ω.2) hB
    _ = _ := by ring

theorem joint_integrable (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (hz : Measurable z) (C : ℝ) (hC : ∀ k, ‖z k‖ ≤ C) (t : ℝ≥0)
    (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R)) :
    Integrable (fun p : ℝ × Sample A =>
      φ p.1*Complex.exp (Complex.I*(p.1 : ℂ)*process z t p.2))
      ((band R).prod (probability μ)) := by
  have hd := hφ.norm.mul_prod (radial_integrable μ z hz C hC t R R.coe_nonneg)
  have hm : AEStronglyMeasurable (fun p : ℝ × Sample A =>
      φ p.1*Complex.exp (Complex.I*(p.1 : ℂ)*process z t p.2))
      ((band R).prod (probability μ)) :=
    hφ.aestronglyMeasurable.comp_fst.mul
      ((Complex.continuous_exp.measurable.comp
        ((measurable_const.mul (Complex.continuous_ofReal.measurable.comp measurable_fst)).mul
          ((process_measurable z hz t).comp measurable_snd))).aestronglyMeasurable)
  apply hd.mono' hm
  have hp : MeasurePreserving (Prod.fst : ℝ × Sample A → ℝ)
    ((band R).prod (probability μ)) (band R) := measurePreserving_fst
  filter_upwards [hp.quasiMeasurePreserving.ae (frequency_bound R)] with p hξ
  change ‖φ p.1*Complex.exp (Complex.I*(p.1 : ℂ)*process z t p.2)‖ ≤
    ‖φ p.1‖*Real.exp ((R : ℝ)*‖process z t p.2‖)
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (ComplexRootExponentialDomain.phase_norm_bound p.1 (process z t p.2)).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hξ (norm_nonneg _)))

theorem extension_integrable (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (hz : Measurable z) (C : ℝ) (hC : ∀ k, ‖z k‖ ≤ C) (t : ℝ≥0)
    (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R)) :
    Integrable (fun ω => extension R φ (process z t ω)) (probability μ) :=
  (joint_integrable μ z hz C hC t R φ hφ).integral_prod_right

variable [Fintype A] [MeasurableSingletonClass A]

theorem process_mean (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (hz : Measurable z) (C : ℝ) (hC : ∀ k, ‖z k‖ ≤ C) (t : ℝ≥0)
    (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R)) :
    (∫ ω, extension R φ (process z t ω) ∂probability μ) =
      ∫ ξ, φ ξ*Complex.exp ((t : ℂ)*
        (MarkedRenewalExponentialTransform.oneStep μ z (Complex.I*(ξ : ℂ))-1)) ∂band R := by
  unfold extension
  rw [← integral_integral_swap (joint_integrable μ z hz C hC t R φ hφ)]
  simp_rw [integral_const_mul,
    MarkedRenewalExponentialTransform.process_transform μ z hz C hC t]

end OperatorDerivativeRewrite.Foundation.MarkedRenewalFourierTests
