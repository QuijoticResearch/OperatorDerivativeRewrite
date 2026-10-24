import Foundation.IBMFoldedHeatEnergy
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-! The folded heat candidate has finite time energy for every measurable
clock path. Predictable identification with the canonical IBM input is separate. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMFoldedHeatTimeEnergy
open IBMFoldedHeatEnergy

def energy (T : ℝ) (B : ℝ → ℝ) (s : ℝ) : ℝ :=
  (1-Real.exp (-(B s)^2/(T-s)))/(2*Real.sqrt (Real.pi*(T-s)))

theorem energy_measurable (T : ℝ) {B : ℝ → ℝ} (hB : Measurable B) :
    Measurable (energy T B) := by
  unfold energy
  fun_prop

theorem energy_nonneg (T : ℝ) (B : ℝ → ℝ) {s : ℝ} (hs : s ≤ T) :
    0 ≤ energy T B s := by
  apply div_nonneg _ (by positivity)
  apply sub_nonneg.mpr
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (sub_nonneg.mpr hs)

theorem energy_bound (T : ℝ) (B : ℝ → ℝ) {s : ℝ} (hs : s ≤ T) :
    energy T B s ≤ (2*Real.sqrt Real.pi)⁻¹*(T-s)^(-(1/2 : ℝ)) := by
  have h : energy T B s ≤ (2*Real.sqrt (Real.pi*(T-s)))⁻¹ := by
    unfold energy
    exact (div_le_div_of_nonneg_right
      (sub_le_self _ (Real.exp_nonneg _)) (by positivity)).trans_eq (one_div _)
  rw [Real.sqrt_mul Real.pi_nonneg, ← mul_assoc, mul_inv_rev] at h
  rw [Real.rpow_neg (sub_nonneg.mpr hs), ← Real.sqrt_eq_rpow]
  simpa only [mul_comm] using h

theorem energy_intervalIntegrable {T : ℝ} (hT : 0 ≤ T) {B : ℝ → ℝ}
    (hB : Measurable B) : IntervalIntegrable (energy T B) volume 0 T := by
  have hi := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := T)
    (by norm_num : -1 < -(1/2 : ℝ))).comp_sub_left T
  have hi' : IntervalIntegrable (fun s => (2*Real.sqrt Real.pi)⁻¹*(T-s)^(-(1/2 : ℝ)))
      volume 0 T := by
    simpa only [sub_zero, sub_self] using (hi.const_mul (2*Real.sqrt Real.pi)⁻¹).symm
  apply hi'.mono_fun' (energy_measurable T hB).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
  rw [uIoc_of_le hT] at hs
  rw [Real.norm_eq_abs, abs_of_nonneg (energy_nonneg T B hs.2)]
  exact energy_bound T B hs.2

theorem envelope_intervalIntegrable (T : ℝ) :
    IntervalIntegrable (fun s => (2*Real.sqrt Real.pi)⁻¹*(T-s)^(-(1/2 : ℝ)))
      volume 0 T := by
  have hi := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := T)
    (by norm_num : -1 < -(1/2 : ℝ))).comp_sub_left T
  simpa only [sub_zero, sub_self] using (hi.const_mul (2*Real.sqrt Real.pi)⁻¹).symm

theorem actual_spatial_energy (T : ℝ) (B : ℝ → ℝ) {s : ℝ} (hs : s < T) :
    ‖spatial (B s) (Real.toNNReal (T-s)) (by
      exact_mod_cast Real.toNNReal_pos.mpr (sub_pos.mpr hs))‖^2 = energy T B s := by
  rw [spatial_energy]
  simp only [Real.coe_toNNReal (T-s) (sub_nonneg.mpr hs.le), energy]

end OperatorDerivativeRewrite.Foundation.IBMFoldedHeatTimeEnergy
