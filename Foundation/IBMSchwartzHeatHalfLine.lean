import Foundation.IBMSchwartzHeatBoundary
import Foundation.IBMReflectedClockMean

/-! Absolutely Bochner-integrable nonlinear Schwartz heat reconstruction.
The actual random-time correction identification is separate. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzHeatHalfLine
open InfiniteGaussian GaussianNumberSectors IBMClockHeatPotential IBMClockHeatOccupation
open IBMSchwartzSpatialPrimitive IBMSchwartzPrimitiveLimit IBMSchwartzSecondProjection
open IBMSchwartzHeatBounds IBMSchwartzHeatBoundary

theorem primitive_heat_integrableOn (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    (T : ℝ≥0) (hT : 0 < T) :
    IntegrableOn (fun r => heatKernel T r • spatialPrimitive g a n r) (Ioi 0) := by
  have hi := IBMReflectedClockMean.reflected_density_integrable (spatialPrimitive g a n)
    (spatialPrimitive_continuous g a n).stronglyMeasurable T hT (terminal_integrable g a n T)
  apply hi.integrableOn.congr_fun _ measurableSet_Ioi
  intro r hr
  change heatKernel T r • spatialPrimitive g a n |r| = _
  rw [abs_of_pos hr]

theorem terminalMean_eq_halfline (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    (T : ℝ≥0) (hT : 0 < T) :
    terminalMean g a n T = (2 : ℝ) •
      ∫ r in Ioi 0, heatKernel T r • spatialPrimitive g a n r :=
  IBMReflectedClockMean.reflected_clock_integral (spatialPrimitive g a n)
    (spatialPrimitive_continuous g a n).stronglyMeasurable T hT (terminal_integrable g a n T)

theorem weighted_curvature_integrableOn (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    (T : ℝ≥0) (hT : 0 < T) :
    IntegrableOn (fun r => potential T r • projection 2 (mollifiedClass g a n r)) (Ioi 0) := by
  obtain ⟨C,hC,hc⟩ := projected_growth g a n
  have ha : 0 < Real.sqrt T := Real.sqrt_pos.mpr (NNReal.coe_pos.mpr hT)
  apply ((IBMQuarticHeatDomain.polynomial_heat_integrable T hT 2).integrableOn.const_mul
    (4*(Real.sqrt T)^2*C)).mono'
    ((IBMQuarticHeatBoundary.potential_continuous (NNReal.coe_pos.mpr hT)).smul
      (projected_continuous g a n)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  change ‖potential T r • projection 2 (mollifiedClass g a n r)‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (potential_nonneg
    (NNReal.coe_pos.mpr hT) hr.le)]
  have hb : potential T r ≤ 4*(Real.sqrt T)^2*heatKernel T r := by
    have hh := IBMHeatTailDecay.potential_le_density (T := (T : ℝ)) hr.le
    have hd : 4*(Real.sqrt T)^2*heatKernel T r =
        4*Real.sqrt T*IBMClockGaussianTail.density (r/Real.sqrt T) := by
      unfold heatKernel
      field_simp
    rwa [hd]
  have he := mul_le_mul hb (hc r) (norm_nonneg _)
    (mul_nonneg (by positivity : 0 ≤ 4*(Real.sqrt T)^2) (heatKernel_nonneg _ _))
  nlinarith

/-- The origin coefficient is the actual Tanaka mass expectation. All
half-line integrals have proved absolute Bochner domains. -/
theorem halfline_origin_cancellation (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    (T : ℝ≥0) (hT : 0 < T) :
    (∫ ω, BrownianMassLimitIdentification.coordinateClass T ω ∂gaussianProduct) •
        spatialSlope g a n 0 +
      (1/2 : ℝ) • (∫ r in Ioi 0, potential T r • projection 2 (mollifiedClass g a n r)) =
      terminalMean g a n T-spatialPrimitive g a n 0 := by
  have hi := intervalIntegral_tendsto_integral_Ioi 0
    (weighted_curvature_integrableOn g a n T hT) tendsto_id
  have hh := intervalIntegral_tendsto_integral_Ioi 0
    (primitive_heat_integrableOn g a n T hT) tendsto_id
  have hl := (hi.const_smul (1/2 : ℝ)).const_add
    ((∫ ω, BrownianMassLimitIdentification.coordinateClass T ω ∂gaussianProduct) •
      spatialSlope g a n 0)
  have hr := ((hh.const_smul (2 : ℝ)).sub_const (spatialPrimitive g a n 0)).add
    ((endpoint_tendsto_zero g a n (NNReal.coe_pos.mpr hT)).const_smul (1/2 : ℝ))
  have he : (fun R =>
      (∫ ω, BrownianMassLimitIdentification.coordinateClass T ω ∂gaussianProduct) •
          spatialSlope g a n 0 +
        (1/2 : ℝ) • (∫ r in 0..R, potential T r • projection 2 (mollifiedClass g a n r))) =
      fun R => (2 : ℝ) • (∫ r in 0..R, heatKernel T r • spatialPrimitive g a n r)-
        spatialPrimitive g a n 0+(1/2 : ℝ) • endpoint g a n T R := by
    funext R
    exact actual_origin_finite_cancellation g a n T hT R
  simp only [id_eq] at hl hr
  rw [he] at hl
  have heq := tendsto_nhds_unique hl hr
  simpa only [zero_smul, smul_zero, add_zero, ← terminalMean_eq_halfline g a n T hT] using heq

theorem halfline_origin_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n =>
      (∫ ω, BrownianMassLimitIdentification.coordinateClass T ω ∂gaussianProduct) •
          spatialSlope g a n 0 +
        (1/2 : ℝ) • (∫ r in Ioi 0, potential T r • projection 2 (mollifiedClass g a n r)))
      atTop (𝓝 (terminalLimit g a T)) := by
  simp_rw [halfline_origin_cancellation g a _ T hT]
  exact terminal_difference_tendsto g a T

end OperatorDerivativeRewrite.Foundation.IBMSchwartzHeatHalfLine
