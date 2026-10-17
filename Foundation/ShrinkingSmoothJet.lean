import Foundation.SmoothAtomicJet
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecificLimits.Basic

/-! Shrinking smooth compact jets: values vanish, derivatives retain the atomic jet. -/
noncomputable section
open Filter Set
open scoped ContDiff Topology
namespace OperatorDerivativeRewrite.Foundation.ShrinkingSmoothJet
open SmoothAtomicJet
set_option backward.isDefEq.respectTransparency false

def scale (n : ℕ) : ℝ := (n : ℝ) + 1

theorem scale_pos (n : ℕ) : 0 < scale n := by unfold scale; positivity

theorem scale_one_le (n : ℕ) : 1 ≤ scale n := by
  unfold scale
  have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

def jet (n : ℕ) (x : ℝ) : ℝ := (scale n)⁻¹ * witness (scale n * x)

def atom (x : ℝ) : ℝ := if x = 0 then 1 else 0

theorem jet_smooth (n : ℕ) : ContDiff ℝ ∞ (jet n) :=
  contDiff_const.mul (witness_smooth.comp (contDiff_const.mul contDiff_id))

theorem jet_compact (n : ℕ) : HasCompactSupport (jet n) := by
  have hs := witness_compact.comp_smul (ne_of_gt (scale_pos n))
  have hc : HasCompactSupport (fun x : ℝ => witness (scale n * x)) := by
    simpa only [smul_eq_mul] using hs
  exact hc.mul_left

theorem hasDerivAt_jet (n : ℕ) (x : ℝ) :
    HasDerivAt (jet n) (deriv witness (scale n * x)) x := by
  have hw := (witness_smooth.differentiable (by norm_num) (scale n * x)).hasDerivAt
  have hs : HasDerivAt (fun y : ℝ => scale n * y) (scale n) x :=
    hasDerivAt_const_mul (scale n)
  have h := (hw.comp x hs).const_mul (scale n)⁻¹
  convert h using 1
  · funext y
    simp [jet]
  · field_simp [ne_of_gt (scale_pos n)]

theorem deriv_jet (n : ℕ) (x : ℝ) :
    deriv (jet n) x = deriv witness (scale n * x) := (hasDerivAt_jet n x).deriv

theorem jet_zero (n : ℕ) : jet n 0 = 0 := by simp [jet, witness_zero]

theorem deriv_jet_zero (n : ℕ) : deriv (jet n) 0 = 1 := by
  rw [deriv_jet, mul_zero, witness_deriv]

theorem base_bounds : ∃ C : ℝ, 1 ≤ C ∧
    (∀ x, |witness x| ≤ C) ∧ (∀ x, |deriv witness x| ≤ C) := by
  obtain ⟨A,hA⟩ := witness_smooth.continuous.abs.bddAbove_range_of_hasCompactSupport
    witness_compact.abs
  have hd : Continuous (deriv witness) := witness_smooth.continuous_deriv (by norm_num)
  obtain ⟨B,hB⟩ := hd.abs.bddAbove_range_of_hasCompactSupport witness_compact.deriv.abs
  refine ⟨max A (max B 1), (le_max_right B 1).trans (le_max_right _ _), ?_, ?_⟩
  · intro x
    exact (hA (mem_range_self x)).trans (le_max_left _ _)
  · intro x
    exact (hB (mem_range_self x)).trans ((le_max_left _ _).trans (le_max_right _ _))

theorem jet_bound {C : ℝ} (hC : ∀ x, |witness x| ≤ C) (n : ℕ) (x : ℝ) :
    |jet n x| ≤ C / scale n := by
  rw [jet, abs_mul, abs_inv, abs_of_pos (scale_pos n)]
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left (hC (scale n * x)) (inv_nonneg.mpr (scale_pos n).le)

theorem uniform_bounds : ∃ C : ℝ, 1 ≤ C ∧
    ∀ n x, ‖jet n x‖ ≤ C ∧ ‖deriv (jet n) x‖ ≤ C := by
  obtain ⟨C,hC,hv,hd⟩ := base_bounds
  refine ⟨C,hC,fun n x => ?_⟩
  constructor
  · rw [Real.norm_eq_abs]
    exact (jet_bound hv n x).trans (div_le_self (le_trans (by norm_num) hC) (scale_one_le n))
  · rw [deriv_jet, Real.norm_eq_abs]
    exact hd _

theorem jet_tendsto_zero (x : ℝ) : Tendsto (fun n => jet n x) atTop (nhds 0) := by
  obtain ⟨C,hC,hv,_⟩ := base_bounds
  have ht : Tendsto (fun n : ℕ => C / scale n) atTop (nhds 0) := by
    simpa only [scale, div_eq_mul_inv, one_div, one_mul, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) :
        Tendsto (fun n : ℕ => C * (1 / ((n : ℝ) + 1))) atTop (nhds (C * 0)))
  have hn : Tendsto (fun n => ‖jet n x‖) atTop (nhds 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun n => by
      rw [Real.norm_eq_abs]; exact jet_bound hv n x) ht
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero] using hn

theorem scale_escape (x : ℝ) (hx : x ≠ 0) :
    Tendsto (fun n => scale n * x) atTop (cocompact ℝ) := by
  have ht : Tendsto (fun n : ℕ => scale n) atTop atTop := by
    exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hn : Tendsto (fun n => ‖scale n * x‖) atTop atTop := by
    have he : (fun n : ℕ => ‖scale n * x‖) = fun n => scale n * |x| := by
      funext n
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (scale_pos n)]
    rw [he]
    exact (tendsto_mul_const_atTop_of_pos (abs_pos.mpr hx)).mpr ht
  have h := tendsto_norm_atTop_iff_cobounded.mp hn
  rwa [Metric.cobounded_eq_cocompact] at h

theorem derivative_tendsto_atom (x : ℝ) :
    Tendsto (fun n => deriv (jet n) x) atTop (nhds (atom x)) := by
  by_cases hx : x = 0
  · subst x
    simp [deriv_jet_zero, atom]
  · have h := witness_compact.deriv.is_zero_at_infty.comp (scale_escape x hx)
    simpa [Function.comp_def, deriv_jet, atom, hx] using h

end OperatorDerivativeRewrite.Foundation.ShrinkingSmoothJet
