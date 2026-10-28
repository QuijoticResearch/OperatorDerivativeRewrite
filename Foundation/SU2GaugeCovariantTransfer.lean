import Foundation.SU2ClosedLoopTransfer
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.SU2GaugeCovariantTransfer
open QuaternionSU2Representation SU2ClosedLoopTransfer

theorem transition_eq_map_tilt (A : SU2) (β : ℝ) :
    SU2OneWordTransfer.transition law β A =
      (BoundedExponentialTiltResponse.tiltedMeasure law halfTrace β).map
        (fun C => A⁻¹ * C) := by
  have h := congrArg (Measure.map (fun C : SU2 => A⁻¹ * C)) (closedLoop_law A β)
  rw [Measure.map_map (measurable_const_mul A⁻¹) (measurable_const_mul A)] at h
  simpa [Function.comp_def] using h

end OperatorDerivativeRewrite.Foundation.SU2GaugeCovariantTransfer

namespace OperatorDerivativeRewrite.Foundation.SU2GaugeCovariantTransfer
open MeasureTheory ProbabilityTheory
open QuaternionSU2Representation

theorem haar_conjugation_map (g : SU2) :
    law.map (fun C => g * C * g⁻¹) = law := by
  have he : (fun C : SU2 => g * C * g⁻¹) =
      (fun D : SU2 => g * D) ∘ (fun C : SU2 => C * g⁻¹) := by
    funext C
    simp [Function.comp_def, mul_assoc]
  rw [he, ← Measure.map_map (measurable_const_mul g) (measurable_mul_const g⁻¹)]
  have hr (h : SU2) : law.map (fun C => C * h) = law := by
    haveI : IsProbabilityMeasure (law.map (fun C => C * h)) := by infer_instance
    exact (law_eq_probability_haar (law.map (fun C => C * h))).symm
  rw [hr, map_mul_left_eq_self]

end OperatorDerivativeRewrite.Foundation.SU2GaugeCovariantTransfer

namespace OperatorDerivativeRewrite.Foundation.SU2GaugeCovariantTransfer
open MeasureTheory ProbabilityTheory
open QuaternionSU2Representation BoundedExponentialTiltResponse

theorem tilt_conjugation_map (g : SU2) (β : ℝ) :
    (tiltedMeasure law halfTrace β).map (fun C => g * C * g⁻¹) =
      tiltedMeasure law halfTrace β := by
  have hc : Measurable (fun C : SU2 => g * C * g⁻¹) :=
    (measurable_mul_const g⁻¹).comp (measurable_const_mul g)
  have hd : Measurable (fun C : SU2 => ENNReal.ofReal (density law halfTrace β C)) :=
    ((measurable_const.mul halfTrace_measurable).exp.div_const _).ennreal_ofReal
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hc hs, tiltedMeasure, withDensity_apply _ (hc hs),
    withDensity_apply _ hs]
  have he := setLIntegral_map (μ := law) hs hd hc
  rw [haar_conjugation_map] at he
  have hh : (fun C : SU2 => ENNReal.ofReal (density law halfTrace β C)) =
      (fun C => ENNReal.ofReal (density law halfTrace β (g*C*g⁻¹))) := by
    funext C
    simp [density, halfTrace_conjugate]
  conv_lhs => rw [hh]
  exact he.symm

end OperatorDerivativeRewrite.Foundation.SU2GaugeCovariantTransfer

namespace OperatorDerivativeRewrite.Foundation.SU2GaugeCovariantTransfer
open MeasureTheory ProbabilityTheory
open QuaternionSU2Representation BoundedExponentialTiltResponse

theorem transition_gauge_covariant (g h A : SU2) (β : ℝ) :
    (SU2OneWordTransfer.transition law β A).map (fun B => h * B * g⁻¹) =
      SU2OneWordTransfer.transition law β (g * A * h⁻¹) := by
  rw [transition_eq_map_tilt A β, transition_eq_map_tilt (g*A*h⁻¹) β]
  let μ := tiltedMeasure law halfTrace β
  calc
    (μ.map (fun C => A⁻¹ * C)).map (fun B => h * B * g⁻¹) =
        μ.map (fun C => h * (A⁻¹ * C) * g⁻¹) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = μ.map (fun C => (g*A*h⁻¹)⁻¹ * (g*C*g⁻¹)) := by
      congr 1
      funext C
      group
    _ = (μ.map (fun C => g*C*g⁻¹)).map (fun C => (g*A*h⁻¹)⁻¹*C) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = μ.map (fun C => (g*A*h⁻¹)⁻¹*C) := by
      rw [tilt_conjugation_map]

end OperatorDerivativeRewrite.Foundation.SU2GaugeCovariantTransfer
