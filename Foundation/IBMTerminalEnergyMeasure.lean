import Foundation.IBMObservedTerminalMartingale
import Mathlib.MeasureTheory.Measure.Stieltjes

/-! Finite countably additive time energy for every actual germ-terminal channel.
The initial germ projection is retained explicitly. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMTerminalEnergyMeasure
open IBMTimeAveragedObservable IBMIntrinsicRightGerm IBMObservedTerminalMartingale
set_option backward.isDefEq.respectTransparency false

def energy (F : JointL2) (t : ℝ≥0) : ℝ := ‖channelClass F t‖ ^ 2

theorem energy_mono (F : JointL2) : Monotone (energy F) := by
  intro s t hst
  have hn := (rightPast s).norm_starProjection_apply_le (channelClass F t)
  rw [project_channel F hst] at hn
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

theorem energy_right_continuous (F : JointL2) (t : ℝ≥0) :
    ContinuousWithinAt (energy F) (Ici t) t := (channel_right_continuous F t).norm.pow 2

def cumulative (F : JointL2) : StieltjesFunction ℝ≥0 :=
  ⟨energy F, energy_mono F, energy_right_continuous F⟩

def energyMeasure (F : JointL2) : Measure ℝ≥0 := (cumulative F).measure

theorem increment_energy (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t) :
    energy F t - energy F s = ‖channelClass F t - channelClass F s‖ ^ 2 := by
  have ho := (rightPast s).sub_starProjection_mem_orthogonal (channelClass F t)
  rw [project_channel F hst] at ho
  have hi := Submodule.inner_right_of_mem_orthogonal
    ((rightPast s).starProjection_apply_mem F) ho
  change inner ℝ (channelClass F s) (channelClass F t - channelClass F s) = 0 at hi
  have he : channelClass F t = channelClass F s + (channelClass F t - channelClass F s) := by abel
  have hn : ‖channelClass F t‖ ^ 2 = ‖channelClass F s‖ ^ 2 +
      ‖channelClass F t - channelClass F s‖ ^ 2 := by
    conv_lhs => rw [he, norm_add_sq_real, hi]
    ring
  unfold energy
  linarith

theorem energyMeasure_Ioc (F : JointL2) (s t : ℝ≥0) :
    energyMeasure F (Ioc s t) = ENNReal.ofReal (energy F t - energy F s) :=
  (cumulative F).measure_Ioc s t

theorem energyMeasure_increment (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t) :
    energyMeasure F (Ioc s t) = ENNReal.ofReal (‖channelClass F t - channelClass F s‖ ^ 2) := by
  rw [energyMeasure_Ioc, increment_energy F hst]

theorem actual_increment_energy (F : JointL2) (s t : ℝ≥0) :
    ‖channelClass F t - channelClass F s‖ ^ 2 =
      ∫ ω, (channel F t ω - channel F s ω) ^ 2 ∂IBMSourceLaws.jointMeasure := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (channelClass F t) (channelClass F s)] with ω hω
  rw [hω, Real.inner_apply]
  change (channel F t ω - channel F s ω) * (channel F t ω - channel F s ω) = _
  ring

theorem energyMeasure_actual_increment (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t) :
    energyMeasure F (Ioc s t) = ENNReal.ofReal
      (∫ ω, (channel F t ω - channel F s ω) ^ 2 ∂IBMSourceLaws.jointMeasure) := by
  rw [energyMeasure_increment F hst, actual_increment_energy]

theorem energyMeasure_origin (F : JointL2) : energyMeasure F {0} = 0 := by
  rw [energyMeasure, StieltjesFunction.measure_singleton,
    leftLim_eq_of_isBot (a := (0 : ℝ≥0)) (fun _ => zero_le)]
  simp only [sub_self, ENNReal.ofReal_zero]

theorem finite_measure (F : JointL2) : IsFiniteMeasure (energyMeasure F) := by
  apply (cumulative F).isFiniteMeasure_of_forall_abs_le (C := ‖F‖ ^ 2)
  intro t
  change |‖channelClass F t‖ ^ 2| ≤ ‖F‖ ^ 2
  rw [abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (channel_norm_bound F t) 2

theorem interval_bound (F : JointL2) (s t : ℝ≥0) :
    energyMeasure F (Ioc s t) ≤ ENNReal.ofReal (‖F‖ ^ 2) := by
  rw [energyMeasure_Ioc]
  apply ENNReal.ofReal_le_ofReal
  have hn := pow_le_pow_left₀ (norm_nonneg _) (channel_norm_bound F t) 2
  change ‖channelClass F t‖ ^ 2 - ‖channelClass F s‖ ^ 2 ≤ ‖F‖ ^ 2
  nlinarith [sq_nonneg ‖channelClass F s‖]

theorem terminal_mass (F : JointL2) {T : ℝ≥0}
    (hF : F ∈ IBMNaturalFiltrationObstruction.past T) :
    energyMeasure F (Ioc 0 T) = ENNReal.ofReal (‖F‖ ^ 2 - ‖channelClass F 0‖ ^ 2) := by
  rw [energyMeasure_Ioc]
  simp only [energy, terminal_class F hF le_rfl]

end OperatorDerivativeRewrite.Foundation.IBMTerminalEnergyMeasure
