import Foundation.IBMRightGermContinuity
import Mathlib.MeasureTheory.Measure.Stieltjes

/-! A countably additive expected-increment energy measure for the actual
right-germ martingale. This is a deterministic time measure. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRightGermEnergyMeasure
open IBMTimeAveragedObservable IBMIntrinsicRightGerm
open IBMIntrinsicRightApproach IBMRightGermFiltration IBMRightGermContinuity
set_option backward.isDefEq.respectTransparency false

def energy (t : ℝ≥0) : ℝ := ‖rightLimitClass t‖ ^ 2

theorem energy_mono : Monotone energy := by
  intro s t hst
  have hn := (rightPast s).norm_starProjection_apply_le (rightLimitClass t)
  rw [project_rightLimit hst] at hn
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

theorem energy_right_continuous (t : ℝ≥0) : ContinuousWithinAt energy (Ici t) t :=
  (rightLimitClass_right_continuous t).norm.pow 2

def cumulative : StieltjesFunction ℝ≥0 :=
  ⟨energy, energy_mono, energy_right_continuous⟩

def energyMeasure : Measure ℝ≥0 := cumulative.measure

theorem increment_energy {s t : ℝ≥0} (hst : s ≤ t) :
    energy t - energy s = ‖rightLimitClass t - rightLimitClass s‖ ^ 2 := by
  have ho := (rightPast s).sub_starProjection_mem_orthogonal (rightLimitClass t)
  rw [project_rightLimit hst] at ho
  have hi := Submodule.inner_right_of_mem_orthogonal (rightLimitClass_mem s) ho
  have he : rightLimitClass t = rightLimitClass s +
      (rightLimitClass t - rightLimitClass s) := by abel
  have hn : ‖rightLimitClass t‖ ^ 2 = ‖rightLimitClass s‖ ^ 2 +
      ‖rightLimitClass t - rightLimitClass s‖ ^ 2 := by
    conv_lhs => rw [he, norm_add_sq_real, hi]
    ring
  unfold energy
  linarith

theorem energyMeasure_Ioc (s t : ℝ≥0) :
    energyMeasure (Ioc s t) = ENNReal.ofReal (energy t - energy s) :=
  cumulative.measure_Ioc s t

theorem energyMeasure_increment {s t : ℝ≥0} (hst : s ≤ t) :
    energyMeasure (Ioc s t) =
      ENNReal.ofReal (‖rightLimitClass t - rightLimitClass s‖ ^ 2) := by
  rw [energyMeasure_Ioc, increment_energy hst]

theorem actual_increment_energy (s t : ℝ≥0) :
    ‖rightLimitClass t - rightLimitClass s‖ ^ 2 =
      ∫ ω, (rightValue t ω - rightValue s ω) ^ 2 ∂IBMSourceLaws.jointMeasure := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (rightLimitClass t) (rightLimitClass s)] with ω hω
  rw [hω, Real.inner_apply]
  change (rightValue t ω - rightValue s ω) * (rightValue t ω - rightValue s ω) = _
  ring

theorem energyMeasure_actual_increment {s t : ℝ≥0} (hst : s ≤ t) :
    energyMeasure (Ioc s t) = ENNReal.ofReal
      (∫ ω, (rightValue t ω - rightValue s ω) ^ 2 ∂IBMSourceLaws.jointMeasure) := by
  rw [energyMeasure_increment hst, actual_increment_energy]

theorem energy_zero : energy 0 = 0 := by
  simp only [energy, rightLimitClass_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]

theorem energyMeasure_bound (T : ℝ≥0) :
    energyMeasure (Ioc 0 T) ≤ ENNReal.ofReal (2 * (T : ℝ) ^ 2) := by
  rw [energyMeasure_Ioc, energy_zero, sub_zero]
  exact ENNReal.ofReal_le_ofReal (rightLimitClass_bound T)

theorem energyMeasure_Ioc_finite (s t : ℝ≥0) : energyMeasure (Ioc s t) < ⊤ := by
  rw [energyMeasure_Ioc]
  exact ENNReal.ofReal_lt_top

theorem energyMeasure_positive {T : ℝ≥0} (hT : 0 < T) :
    0 < energyMeasure (Ioc 0 T) := by
  rw [energyMeasure_Ioc, energy_zero, sub_zero]
  exact ENNReal.ofReal_pos.mpr (pow_pos (norm_pos_iff.mpr (rightLimitClass_ne_zero hT)) 2)

theorem energyMeasure_origin : energyMeasure {0} = 0 := by
  rw [energyMeasure, StieltjesFunction.measure_singleton,
    leftLim_eq_of_isBot (a := (0 : ℝ≥0)) (fun _ => zero_le)]
  simp only [sub_self, ENNReal.ofReal_zero]

theorem locally_finite : IsLocallyFiniteMeasure energyMeasure := by
  unfold energyMeasure
  infer_instance

end OperatorDerivativeRewrite.Foundation.IBMRightGermEnergyMeasure
