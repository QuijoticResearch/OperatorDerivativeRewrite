import Foundation.IBMSpatialJointFourth
import Foundation.ProbabilityTailBound

/-! Positive uniform lower tails for the ACTUAL joint mollified IBM integral.
The existing pseudoprocess probability-tail theorem is reused unchanged. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialIntegralTail
open InfiniteGaussian IBMSpatialPointClockObstruction

abbrev value (r : ℕ) (T : ℝ≥0) := realize (IBMSpatialPointClockEnergy.integralValue r T)

theorem second (r : ℕ) (T : ℝ≥0) :
    (∫ w, ‖value r T w‖^2 ∂IBMSourceLaws.jointMeasure) =
      (T : ℝ)*‖IBMPhysicalWhiteNoiseObstruction.profile r‖^2 := by
  rw [← BochnerL2Dominated.norm_sq_integral, realize.norm_map,
    IBMSpatialPointClockEnergy.integral_energy]

theorem second_pos (r : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    0 < ∫ w, ‖value r T w‖^2 ∂IBMSourceLaws.jointMeasure := by
  have hp : IBMPhysicalWhiteNoiseObstruction.profile r ≠ 0 := by
    intro hz
    have h := IBMPhysicalWhiteNoiseObstruction.probe_profile_pairing r
    rw [hz, inner_zero_right] at h
    norm_num at h
  rw [second]
  exact mul_pos hT (sq_pos_of_pos (norm_pos_iff.mpr hp))

theorem square_memLp (r : ℕ) (T : ℝ≥0) :
    MemLp (fun w => ‖value r T w‖^2) 2 IBMSourceLaws.jointMeasure := by
  apply (integrable_norm_rpow_iff (p := 2) (f := fun w => ‖value r T w‖^2)
    (by fun_prop) (by norm_num) (by norm_num)).mp
  convert (IBMSpatialJointFourth.realize_memLp_four _
    (IBMSpatialIntegralFourth.integral_memLp_four r T)).integrable_norm_pow' using 1
  funext w
  change ‖‖value r T w‖^2‖^(2 : ℝ) = ‖value r T w‖^4
  rw [Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _)]
  ring

theorem fourth_bound (r : ℕ) (T : ℝ≥0) :
    (∫ w, ‖value r T w‖^4 ∂IBMSourceLaws.jointMeasure) ≤
      9*(∫ w, ‖value r T w‖^2 ∂IBMSourceLaws.jointMeasure)^2 := by
  have h := (IBMSpatialJointFourth.integral_joint_fourth r T).2
  have he : (∫ w, ‖value r T w‖^4 ∂IBMSourceLaws.jointMeasure) =
      ∫ w, (value r T w)^4 ∂IBMSourceLaws.jointMeasure := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun w => by
      change ‖value r T w‖^4 = (value r T w)^4
      rw [← norm_pow, Real.norm_of_nonneg (by positivity)])
  rw [he, second]
  nlinarith [h]

theorem tail_mass_lower (r : ℕ) (T : ℝ≥0) (hT : 0 < T) (b : ℝ) (hb : 0 ≤ b)
    (hbm : 2*b ≤ ∫ w, ‖value r T w‖^2 ∂IBMSourceLaws.jointMeasure) :
    1/36 ≤ IBMSourceLaws.jointMeasure.real {w | b < ‖value r T w‖^2} := by
  let μ := IBMSourceLaws.jointMeasure
  let m : ℝ := ∫ w, ‖value r T w‖^2 ∂μ
  let p : ℝ := μ.real {w | b < ‖value r T w‖^2}
  have hm : 0 ≤ m := integral_nonneg (fun _ => sq_nonneg _)
  have hp : 0 ≤ p := ENNReal.toReal_nonneg
  have hms : 0 < m^2 := sq_pos_of_pos (second_pos r T hT)
  have hs := ProbabilityTailBound.mean_tail_square μ (fun w => ‖value r T w‖^2)
    (by fun_prop) (fun _ => sq_nonneg _) (square_memLp r T) b hb
    (by change b ≤ m; change 2*b ≤ m at hbm; linarith)
  simp only [← pow_mul, show 2*2=4 from rfl] at hs
  change (m-b)^2 ≤ (∫ w, ‖value r T w‖^4 ∂μ)*p at hs
  have hl : (m/2)^2 ≤ (m-b)^2 :=
    pow_le_pow_left₀ (by positivity) (by change 2*b ≤ m at hbm; linarith) 2
  have hu := mul_le_mul_of_nonneg_right (fourth_bound r T) hp
  change (∫ w, ‖value r T w‖^4 ∂μ)*p ≤ 9*m^2*p at hu
  have he : m^2*(1/36) ≤ m^2*p := by nlinarith
  exact le_of_mul_le_mul_left he hms

theorem second_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun r => ∫ w, ‖value r T w‖^2 ∂IBMSourceLaws.jointMeasure) atTop atTop := by
  have h := (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
    (integral_joint_norm_escape T hT)
  simpa only [Function.comp_def, BochnerL2Dominated.norm_sq_integral] using h

end OperatorDerivativeRewrite.Foundation.IBMSpatialIntegralTail
