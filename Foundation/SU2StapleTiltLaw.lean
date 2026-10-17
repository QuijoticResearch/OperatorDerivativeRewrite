import Foundation.SU2StaplePolar
import Mathlib.MeasureTheory.Group.Integral

/-! Exact probability-law reduction of a finite SU(2) staple tilt to the half-trace tilt. -/
noncomputable section
open MeasureTheory
open scoped Quaternion Matrix
namespace OperatorDerivativeRewrite.Foundation.SU2StapleTiltLaw
open QuaternionSU2Representation SU2TraceHessianModel SU2StaplePolar
open BoundedExponentialTiltResponse
set_option backward.isDefEq.respectTransparency false

def axis (V A : SU2) : ℝ := halfTrace (V * A)

theorem axis_measurable (V : SU2) : Measurable (axis V) :=
  halfTrace_measurable.comp (measurable_const_mul V)

theorem axis_bound (V A : SU2) : |axis V A| ≤ 1 := halfTrace_bound _

variable (ν : Measure SU2) [IsProbabilityMeasure ν] [ν.IsHaarMeasure]

omit [IsProbabilityMeasure ν] in
theorem partition_axis (V : SU2) (t : ℝ) :
    partition ν (axis V) t = partition ν halfTrace t := by
  simp only [partition, weighted, one_mul, axis]
  exact integral_mul_left_eq_self (fun A => Real.exp (t * halfTrace A)) V

omit [IsProbabilityMeasure ν] in
theorem tilt_map (V : SU2) (t : ℝ) :
    (tiltedMeasure ν (axis V) t).map (fun A => V * A) =
      tiltedMeasure ν halfTrace t := by
  have hrot : Measurable (fun A : SU2 => V * A) := measurable_const_mul V
  have hd : Measurable (fun A : SU2 => ENNReal.ofReal (density ν halfTrace t A)) :=
    ((measurable_const.mul halfTrace_measurable).exp.div_const _).ennreal_ofReal
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hrot hs, tiltedMeasure, withDensity_apply _ (hrot hs),
    tiltedMeasure, withDensity_apply _ hs]
  have he := setLIntegral_map (μ := ν) hs hd hrot
  rw [map_mul_left_eq_self] at he
  have hh : (fun A => ENNReal.ofReal (density ν (axis V) t A)) =
      fun A => ENNReal.ofReal (density ν halfTrace t (V * A)) := by
    funext A
    simp only [density, partition_axis, axis]
  rw [hh]
  exact he.symm

variable {ι : Type*}

def concentration (s : Finset ι) (U : ι → SU2) (β : ℝ) : ℝ :=
  β * ‖quaternionSum s U‖

def stapleLaw (s : Finset ι) (U : ι → SU2) (β : ℝ) : Measure SU2 :=
  tiltedMeasure ν (axis (orientation (quaternionSum s U))) (concentration s U β)

omit [ν.IsHaarMeasure] in
theorem stapleLaw_probability (s : Finset ι) (U : ι → SU2) (β : ℝ) :
    IsProbabilityMeasure (stapleLaw ν s U β) :=
  tiltedMeasure_probability ν _ (axis_measurable _) (axis_bound _) _

theorem concentration_bounds (s : Finset ι) (U : ι → SU2) (β : ℝ) (hβ : 0 ≤ β) :
    0 ≤ concentration s U β ∧ concentration s U β ≤ β * (s.card : ℝ) :=
  ⟨mul_nonneg hβ (norm_nonneg _), mul_le_mul_of_nonneg_left (radius_bound s U) hβ⟩

theorem wilson_exponent (s : Finset ι) (U : ι → SU2) (β : ℝ) (A : SU2) :
    (β/2) * traceReal ((A : M2) * staple s U) =
      concentration s U β * axis (orientation (quaternionSum s U)) A := by
  have h := trace_tilt s U A
  dsimp only [concentration, axis]
  calc
    _ = β * (traceReal ((A : M2) * staple s U) / 2) := by ring
    _ = _ := by rw [h]; ring

omit [IsProbabilityMeasure ν] in
theorem stapleLaw_density (s : Finset ι) (U : ι → SU2) (β : ℝ) :
    stapleLaw ν s U β = ν.withDensity (fun A =>
      ENNReal.ofReal (Real.exp ((β/2) * traceReal ((A : M2) * staple s U)) /
        partition ν halfTrace (concentration s U β))) := by
  unfold stapleLaw tiltedMeasure
  congr 1
  funext A
  rw [density, partition_axis, wilson_exponent]

omit [IsProbabilityMeasure ν] in
theorem stapleLaw_map (s : Finset ι) (U : ι → SU2) (β : ℝ) :
    (stapleLaw ν s U β).map (fun A => orientation (quaternionSum s U) * A) =
      tiltedMeasure ν halfTrace (concentration s U β) :=
  tilt_map ν _ _

end OperatorDerivativeRewrite.Foundation.SU2StapleTiltLaw
