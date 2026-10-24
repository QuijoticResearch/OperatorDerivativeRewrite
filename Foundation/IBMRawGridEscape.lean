import Foundation.IBMRawGridCompensation

/-! The actual OBSERVABLE clock compensation escapes in original L2 on
uniform refinements. This does not decide convergence of compensated fields. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRawGridEscape
open IBMTimeAveragedObservable IBMUniformClockGridEnergy IBMRawGridCompensation
open GaussianAbsoluteMoments

def uniformCorrection (T : ℝ≥0) (n : ℕ) : IntrinsicSpace :=
  correctionSum (T/(n+1)) (n+1)

private theorem sqrt_scale (T : ℝ≥0) (n : ℕ) :
    (n+1:ℝ) * Real.sqrt ((T/(n+1):ℝ≥0):ℝ) = Real.sqrt T * Real.sqrt (n+1:ℝ) := by
  have hn : Real.sqrt (n+1:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hs := Real.sq_sqrt (by positivity : (0:ℝ) ≤ (n+1:ℝ))
  have he : ((T/(n+1):ℝ≥0):ℝ) = (T:ℝ)/(n+1:ℝ) := by push_cast; rfl
  have hd : Real.sqrt ((T:ℝ)/(n+1:ℝ)) = Real.sqrt T / Real.sqrt (n+1:ℝ) :=
    Real.sqrt_div T.property _
  calc
    _ = (n+1:ℝ) * Real.sqrt ((T:ℝ)/(n+1:ℝ)) := congrArg
      (fun z => (n+1:ℝ)*Real.sqrt z) he
    _ = (n+1:ℝ) * (Real.sqrt T / Real.sqrt (n+1:ℝ)) := congrArg (fun z => (n+1:ℝ)*z) hd
    _ = (Real.sqrt (n+1:ℝ))^2 * (Real.sqrt T / Real.sqrt (n+1:ℝ)) := congrArg
      (fun z => z * (Real.sqrt T / Real.sqrt (n+1:ℝ))) hs.symm
    _ = _ := by field_simp

theorem norm_lower_bound (T : ℝ≥0) (n : ℕ) :
    (standardMoment 1 * Real.sqrt T / 2) * Real.sqrt (n+1:ℝ) -
      standardMoment 1 * Real.sqrt T ≤ ‖uniformCorrection T n‖ := by
  have hb := grid_mean_bound (T/(n+1)) (n+1)
  have he : grid (T/(n+1)) (n+1) = T := by
    unfold grid
    have hp : (0:ℝ≥0) < (n:ℝ≥0)+1 := by positivity
    simpa only [Nat.cast_add, Nat.cast_one] using div_mul_cancel₀ T (ne_of_gt hp)
  rw [he] at hb
  have hs := sqrt_scale T n
  have hn := neg_expectation_le_norm (uniformCorrection T n)
  change -expectation (correctionSum (T/(n+1)) (n+1)) ≤ _ at hn
  push_cast at hb hs
  have hm := congrArg (fun x => standardMoment 1 * x / 2) hs
  nlinarith

theorem norm_escape (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => ‖uniformCorrection T n‖) atTop atTop := by
  have hn : Tendsto (fun n : ℕ => (n+1:ℝ)) atTop atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hs := Real.tendsto_sqrt_atTop.comp hn
  have hc : 0 < standardMoment 1 * Real.sqrt T / 2 :=
    div_pos (mul_pos IBMPhysicalL2Obstruction.first_absolute_moment_pos
      (Real.sqrt_pos.mpr (show (0:ℝ) < T from hT))) (by norm_num)
  have hl := hs.const_mul_atTop hc
  have ht := Filter.tendsto_atTop_add_const_right _
    (-(standardMoment 1 * Real.sqrt T)) hl
  apply tendsto_atTop_mono (fun n => norm_lower_bound T n)
  simpa only [sub_eq_add_neg, Function.comp_def] using ht

theorem no_L2_limit (T : ℝ≥0) (hT : 0 < T) (v : IntrinsicSpace) :
    ¬ Tendsto (uniformCorrection T) atTop (𝓝 v) := by
  intro hv
  exact not_tendsto_nhds_of_tendsto_atTop (norm_escape T hT) _ hv.norm

end OperatorDerivativeRewrite.Foundation.IBMRawGridEscape
