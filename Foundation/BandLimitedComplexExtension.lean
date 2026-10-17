import Foundation.ComplexRootExponentialDomain
import Mathlib.MeasureTheory.Integral.Prod

/-! Compact-frequency Fourier extensions form an actual integrable complex-process test domain. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BandLimitedComplexExtension

def band (R : ℝ≥0) : Measure ℝ := volume.restrict (Icc (-(R : ℝ)) R)

instance band_finite (R : ℝ≥0) : IsFiniteMeasure (band R) := by unfold band; infer_instance

theorem frequency_bound (R : ℝ≥0) : ∀ᵐ ξ : ℝ ∂band R, |ξ| ≤ (R : ℝ) := by
  filter_upwards [ae_restrict_mem measurableSet_Icc] with ξ hξ
  exact abs_le.mpr hξ

def extension (R : ℝ≥0) (φ : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ ξ, φ ξ*Complex.exp (Complex.I*(ξ : ℂ)*z) ∂band R

theorem extension_zero (R : ℝ≥0) (φ : ℝ → ℂ) : extension R φ 0 = ∫ ξ, φ ξ ∂band R := by
  simp [extension]

theorem integrand_integrable (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R)) (z : ℂ) :
    Integrable (fun ξ => φ ξ*Complex.exp (Complex.I*(ξ : ℂ)*z)) (band R) := by
  apply hφ.mul_bdd (c := Real.exp ((R : ℝ)*‖z‖)) (by fun_prop : Measurable (fun ξ : ℝ =>
    Complex.exp (Complex.I*(ξ : ℂ)*z))).aestronglyMeasurable
  filter_upwards [frequency_bound R] with ξ hξ
  exact (ComplexRootExponentialDomain.phase_norm_bound ξ z).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hξ (norm_nonneg z)))

theorem norm_bound (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R)) (z : ℂ) :
    ‖extension R φ z‖ ≤ (∫ ξ, ‖φ ξ‖ ∂band R)*Real.exp ((R : ℝ)*‖z‖) := by
  unfold extension
  calc
    _ ≤ ∫ ξ, ‖φ ξ*Complex.exp (Complex.I*(ξ : ℂ)*z)‖ ∂band R :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ ξ, ‖φ ξ‖*Real.exp ((R : ℝ)*‖z‖) ∂band R := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
        (hφ.norm.mul_const _)
      filter_upwards [frequency_bound R] with ξ hξ
      change ‖φ ξ*Complex.exp (Complex.I*(ξ : ℂ)*z)‖ ≤ ‖φ ξ‖*Real.exp ((R : ℝ)*‖z‖)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left ((ComplexRootExponentialDomain.phase_norm_bound ξ z).trans
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hξ (norm_nonneg z)))) (norm_nonneg _)
    _ = _ := integral_mul_const _ _

theorem extension_continuous (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R)) :
    Continuous (extension R φ) := by
  apply continuous_iff_continuousAt.mpr
  intro z₀
  have hz : ∀ᶠ z : ℂ in 𝓝 z₀, ‖z‖ ≤ ‖z₀‖+1 := by
    have ht := (continuous_norm : Continuous (fun z : ℂ => ‖z‖)).continuousAt.tendsto (x := z₀)
    exact (ht.eventually (Iio_mem_nhds (by linarith : ‖z₀‖ < ‖z₀‖+1))).mono fun _ h => h.le
  change Tendsto (fun z : ℂ => ∫ ξ, φ ξ*Complex.exp (Complex.I*(ξ : ℂ)*z) ∂band R)
    (𝓝 z₀) (𝓝 (∫ ξ, φ ξ*Complex.exp (Complex.I*(ξ : ℂ)*z₀) ∂band R))
  refine tendsto_integral_filter_of_dominated_convergence
    (fun ξ => ‖φ ξ‖*Real.exp ((R : ℝ)*(‖z₀‖+1))) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun z => hφ.aestronglyMeasurable.mul
      (by fun_prop : Measurable (fun ξ : ℝ =>
        Complex.exp (Complex.I*(ξ : ℂ)*z))).aestronglyMeasurable
  · filter_upwards [hz] with z hzn
    filter_upwards [frequency_bound R] with ξ hξ
    change ‖φ ξ*Complex.exp (Complex.I*(ξ : ℂ)*z)‖ ≤
      ‖φ ξ‖*Real.exp ((R : ℝ)*(‖z₀‖+1))
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (ComplexRootExponentialDomain.phase_norm_bound ξ z).trans
      (Real.exp_le_exp.mpr (mul_le_mul hξ hzn (norm_nonneg _) R.coe_nonneg))
  · exact hφ.norm.mul_const _
  · exact Eventually.of_forall fun ξ => by
      have hc : Continuous (fun z : ℂ => φ ξ*Complex.exp (Complex.I*(ξ : ℂ)*z)) := by fun_prop
      exact hc.continuousAt.tendsto

theorem law_integrable (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R))
    (t : ℝ≥0) (a : ℝ) : Integrable (extension R φ) (ComplexRootPoissonLaw.law t a) :=
  ComplexRootExponentialDomain.integrable_of_exp_bound t a _
    (extension_continuous R φ hφ).measurable _ R R.coe_nonneg (norm_bound R φ hφ)

theorem process_integrable (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R))
    (t : ℝ≥0) (a : ℝ) : Integrable (fun ω : MarkedRootRenewalProcess.StateSample =>
      extension R φ (MarkedRenewalMartingale.process a t ω)) MarkedRootRenewalProcess.probability :=
  ComplexRootExponentialDomain.process_integrable t a _ (extension_continuous R φ hφ).measurable
    _ R R.coe_nonneg (norm_bound R φ hφ)

theorem tilted_integrable (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R))
    (t : ℝ≥0) (a ξ : ℝ) : (ComplexRootTiltedLaw.law a ξ t).Integrable (extension R φ) :=
  ComplexRootExponentialDomain.tilted_integrable t a ξ _ (extension_continuous R φ hφ).measurable
    _ R R.coe_nonneg (norm_bound R φ hφ)

end OperatorDerivativeRewrite.Foundation.BandLimitedComplexExtension
