import Foundation.SU2WeakCouplingNormalization
import Foundation.MeasurableExponentialKernel
import Foundation.SU2OneWordBoundaryInfluence
import Foundation.SU2GaugeCovariantTransfer
import Foundation.SU2OneWordLargeCoupling
/-! A gauge-covariant correlated SU(2) closed-loop Markov kernel and its scale limits. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open OperatorDerivativeRewrite.Foundation.QuaternionSU2Representation
open OperatorDerivativeRewrite.Foundation.MeasurableExponentialKernel
namespace OperatorDerivativeRewrite.Foundation.SU2InteractingLoopKernel

def interaction (r : ℝ) (C D : SU2) : ℝ := r * halfTrace C * halfTrace D

theorem interaction_measurable (r : ℝ) : Measurable (Function.uncurry (interaction r)) := by
  change Measurable (fun p : SU2 × SU2 => r * halfTrace p.1 * halfTrace p.2)
  exact (measurable_const.mul (halfTrace_measurable.comp measurable_fst)).mul
    (halfTrace_measurable.comp measurable_snd)

theorem interaction_bound (r : ℝ) (C D : SU2) : |interaction r C D| ≤ |r| := by
  rw [interaction, abs_mul, abs_mul]
  have h := mul_le_mul (halfTrace_bound C) (halfTrace_bound D)
    (abs_nonneg _) (by norm_num)
  calc
    |r| * |halfTrace C| * |halfTrace D| = |r| * (|halfTrace C| * |halfTrace D|) := by ring
    _ ≤ |r| * 1 := mul_le_mul_of_nonneg_left (by simpa using h) (abs_nonneg _)
    _ = |r| := by ring

theorem interaction_exp_integrable (r : ℝ) (C : SU2) :
    Integrable (fun D => Real.exp (interaction r C D)) law := by
  have hm : Measurable (interaction r C) := (interaction_measurable r).of_uncurry_left
  apply Integrable.mono' (integrable_const (Real.exp (|r|)))
    hm.exp.aestronglyMeasurable
  filter_upwards with D
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans (interaction_bound r C D))

def loopKernel (r : ℝ) : Kernel SU2 SU2 :=
  MeasurableExponentialKernel.kernel law (interaction r)

theorem loopKernel_markov (r : ℝ) : IsMarkovKernel (loopKernel r) :=
  MeasurableExponentialKernel.kernel_markov law (interaction r)
    (interaction_measurable r) (interaction_exp_integrable r)

theorem partition_upper (r : ℝ) (C : SU2) :
    MeasurableExponentialKernel.partition law (interaction r) C ≤ Real.exp (|r|) := by
  change (∫ D, Real.exp (interaction r C D) ∂law) ≤ Real.exp (|r|)
  have hI := interaction_exp_integrable r C
  have h := integral_mono hI (integrable_const (Real.exp (|r|)))
    (fun D => Real.exp_le_exp.mpr ((le_abs_self _).trans (interaction_bound r C D)))
  simpa using h

theorem density_lower (r : ℝ) (C D : SU2) :
    Real.exp (-(2 * |r|)) ≤ MeasurableExponentialKernel.density law (interaction r) C D := by
  have hp := MeasurableExponentialKernel.partition_positive law (interaction r) C
    (interaction_exp_integrable r C)
  have hu := partition_upper r C
  unfold MeasurableExponentialKernel.density
  apply (le_div_iff₀ hp).2
  have hnum : Real.exp (-|r|) ≤ Real.exp (interaction r C D) :=
    Real.exp_le_exp.mpr ((neg_le_neg (interaction_bound r C D)).trans (neg_abs_le _))
  calc
    Real.exp (-(2 * |r|)) * MeasurableExponentialKernel.partition law (interaction r) C ≤
      Real.exp (-(2 * |r|)) * Real.exp (|r|) :=
        mul_le_mul_of_nonneg_left hu (Real.exp_pos _).le
    _ = Real.exp (-|r|) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (interaction r C D) := hnum
theorem loopKernel_section (r : ℝ) (C : SU2) :
    loopKernel r C = BoundedExponentialTiltResponse.tiltedMeasure law halfTrace
      (r * halfTrace C) := by
  rw [loopKernel, MeasurableExponentialKernel.kernel_apply law _ (interaction_measurable r)]
  unfold BoundedExponentialTiltResponse.tiltedMeasure
  congr 1
  funext D
  simp only [MeasurableExponentialKernel.density, MeasurableExponentialKernel.partition,
    BoundedExponentialTiltResponse.density, BoundedExponentialTiltResponse.partition,
    BoundedExponentialTiltResponse.weighted, one_mul]
  simp [interaction, mul_assoc]
theorem plus_section (r : ℝ) :
    loopKernel r (1 : SU2) = SU2OneWordTransfer.transition law r 1 := by
  rw [loopKernel_section, SU2OpenLinkGaugeObstruction.halfTrace_one, mul_one]
  exact (SU2OneWordTransfer.transition_identity_law law r).symm

theorem minus_section (r : ℝ) :
    loopKernel r SU2StapleExtremes.minusOne =
      SU2OneWordTransfer.transition law r SU2StapleExtremes.minusOne := by
  rw [loopKernel_section, SU2OpenLinkGaugeObstruction.halfTrace_minusOne, mul_neg, mul_one]
  exact (SU2OneWordBoundaryInfluence.minus_law r).symm

theorem nontrivial_state_response (ε : ℝ) (hε : 0 < ε) :
    ∃ r, 0 < r ∧ r < ε ∧
      (∫ D, halfTrace D ∂loopKernel r SU2StapleExtremes.minusOne) <
      (∫ D, halfTrace D ∂loopKernel r (1 : SU2)) := by
  obtain ⟨r, hr, hrε, hsep⟩ :=
    SU2OneWordBoundaryInfluence.boundary_mean_separation_near_zero ε hε
  exact ⟨r, hr, hrε, by simpa only [plus_section, minus_section] using hsep⟩
theorem interaction_biGauge (r : ℝ) (g h C D : SU2) :
    interaction r (g*C*g⁻¹) (h*D*h⁻¹) = interaction r C D := by
  simp [interaction, halfTrace_conjugate]

theorem loopKernel_gauge_covariant (r : ℝ) (g h C : SU2) :
    (loopKernel r C).map (fun D => h * D * h⁻¹) =
      loopKernel r (g * C * g⁻¹) := by
  rw [loopKernel_section, loopKernel_section, halfTrace_conjugate]
  exact SU2GaugeCovariantTransfer.tilt_conjugation_map h (r * halfTrace C)
theorem loopKernel_doeblin (r : ℝ) (C : SU2) :
    ENNReal.ofReal (Real.exp (-(2 * |r|))) • law ≤ loopKernel r C := by
  rw [loopKernel, MeasurableExponentialKernel.kernel_apply law _ (interaction_measurable r)]
  rw [← withDensity_const]
  apply withDensity_mono
  filter_upwards with D
  exact ENNReal.ofReal_le_ofReal (density_lower r C D)
theorem no_uniform_central_mean_contraction (q : ℝ) (hq : q < 1) :
    ∃ r : ℝ, 0 ≤ r ∧ 2*q <
      (∫ D, halfTrace D ∂loopKernel r (1 : SU2)) -
      (∫ D, halfTrace D ∂loopKernel r SU2StapleExtremes.minusOne) := by
  obtain ⟨r, hr, hsep⟩ :=
    SU2OneWordLargeCoupling.no_uniform_central_mean_contraction q hq
  exact ⟨r, hr, by simpa only [plus_section, minus_section] using hsep⟩
end OperatorDerivativeRewrite.Foundation.SU2InteractingLoopKernel
