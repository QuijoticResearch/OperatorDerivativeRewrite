import Foundation.SU2LoopEquilibrium

/-! Explicit stationary-reference minorization for the interacting SU(2) loop kernel. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open OperatorDerivativeRewrite.Foundation.QuaternionSU2Representation
open OperatorDerivativeRewrite.Foundation.MeasurableExponentialKernel
open OperatorDerivativeRewrite.Foundation.BoundedExponentialTiltResponse
open OperatorDerivativeRewrite.Foundation.SU2CoupledLoopResponse
open OperatorDerivativeRewrite.Foundation.SU2InteractingLoopKernel
open OperatorDerivativeRewrite.Foundation.SU2LoopEquilibrium

namespace OperatorDerivativeRewrite.Foundation.SU2StationaryMinorization

private theorem X_measurable : Measurable X :=
  (halfTrace_measurable.comp measurable_fst).mul
    (halfTrace_measurable.comp measurable_snd)

private theorem X_bound (p : SU2 × SU2) : |X p| ≤ 1 := by
  rw [X, abs_mul]
  calc
    |F p| * |G p| ≤ 1 * 1 :=
      mul_le_mul (halfTrace_bound _) (halfTrace_bound _) (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem globalPartition_lower (r : ℝ) :
    Real.exp (-|r|) ≤ globalPartition r := by
  have hi : Integrable (fun p => Real.exp (r * X p)) μ :=
    BoundedExponentialTiltResponse.exponential_integrable μ X X_measurable X_bound r
  have h := integral_mono (integrable_const (Real.exp (-|r|))) hi (fun p =>
    Real.exp_le_exp.mpr (by
      have hb := interaction_bound r p.1 p.2
      have he : interaction r p.1 p.2 = r * X p := by
        simp only [interaction, X, F, G]
        ring
      rw [he] at hb
      exact (neg_le_neg hb).trans (neg_abs_le _)))
  simpa [globalPartition, BoundedExponentialTiltResponse.partition,
    BoundedExponentialTiltResponse.weighted] using h

theorem equilibriumDensity_upper (r : ℝ) (C : SU2) :
    equilibriumDensity r C ≤ Real.exp (2*|r|) := by
  have hG := globalPartition_lower r
  have hp := globalPartition_pos r
  apply (div_le_iff₀ hp).2
  calc
    MeasurableExponentialKernel.partition law (interaction r) C ≤ Real.exp (|r|) :=
      partition_upper r C
    _ = Real.exp (2*|r|) * Real.exp (-|r|) := by
      rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (2*|r|) * globalPartition r :=
      mul_le_mul_of_nonneg_left hG (Real.exp_pos _).le

theorem stationary_density_minorization (r : ℝ) (C D : SU2) :
    Real.exp (-(4*|r|)) * equilibriumDensity r D ≤
      MeasurableExponentialKernel.density law (interaction r) C D := by
  calc
    Real.exp (-(4*|r|)) * equilibriumDensity r D ≤
        Real.exp (-(4*|r|)) * Real.exp (2*|r|) :=
      mul_le_mul_of_nonneg_left (equilibriumDensity_upper r D) (Real.exp_pos _).le
    _ = Real.exp (-(2*|r|)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := density_lower r C D

theorem loopKernel_minorizes_equilibrium (r : ℝ) (C : SU2) :
    ENNReal.ofReal (Real.exp (-(4*|r|))) • equilibriumLaw r ≤ loopKernel r C := by
  rw [equilibriumLaw, loopKernel,
    MeasurableExponentialKernel.kernel_apply law _ (interaction_measurable r)]
  rw [← withDensity_smul' (ENNReal.ofReal (Real.exp (-(4*|r|))))
    (fun D : SU2 => ENNReal.ofReal (equilibriumDensity r D)) ENNReal.ofReal_ne_top]
  apply withDensity_mono
  filter_upwards with D
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal (stationary_density_minorization r C D)

end OperatorDerivativeRewrite.Foundation.SU2StationaryMinorization
