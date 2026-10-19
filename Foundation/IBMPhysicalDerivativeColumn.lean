import Foundation.IBMPhysicalNoiseCalculus
import Foundation.BochnerL2Fubini
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Scalar column calculation for the physical first-derivative kernel.
Compact support fixes both boundary terms; the orientation sign is explicit. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalDerivativeColumn

def step (r w : ℝ) : ℝ := (if w ≤ r then 1 else 0)-(if w ≤ 0 then 1 else 0)

def column (ρ : ℝ → ℝ) (x : ℝ) (p : ℝ × ℝ) : ℝ := deriv ρ (x-p.1)*step p.1 p.2

theorem shifted_derivative_integrable {ρ : ℝ → ℝ} (hf : ContDiff ℝ 1 ρ)
    (hs : HasCompactSupport ρ) (x : ℝ) : Integrable (fun r => deriv ρ (x-r)) volume :=
  ((hf.continuous_deriv le_rfl).comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
    (hs.deriv.comp_homeomorph (Homeomorph.subLeft x))

theorem shifted_derivative_integrals {ρ : ℝ → ℝ} (hf : ContDiff ℝ 1 ρ)
    (hs : HasCompactSupport ρ) (x : ℝ) :
    (∫ r, deriv ρ (x-r)) = 0 ∧ ∀ w, (∫ r in Ici w, deriv ρ (x-r)) = ρ (x-w) := by
  let F : ℝ → ℝ := fun r => -ρ (x-r)
  have hF : ContDiff ℝ 1 F := (hf.comp (contDiff_const.sub contDiff_id)).neg
  have hS : HasCompactSupport F := (hs.comp_homeomorph (Homeomorph.subLeft x)).neg
  have hd : deriv F = fun r => deriv ρ (x-r) := by
    funext r
    have he := ((hf.differentiable one_ne_zero (x-r)).hasDerivAt.comp r
      ((hasDerivAt_id r).const_sub x)).neg
    have he' : HasDerivAt F (deriv ρ (x-r)) r := by
      convert he using 1
      · rfl
      · ring
    exact he'.deriv
  have hi := shifted_derivative_integrable hf hs x
  have ht (w : ℝ) : (∫ r in Ioi w, deriv ρ (x-r)) = ρ (x-w) := by
    have he := HasCompactSupport.integral_Ioi_deriv_eq hF hS w
    rw [hd] at he
    simpa only [F, neg_neg] using he
  have hb := HasCompactSupport.integral_Iic_deriv_eq hF hS 0
  rw [hd] at hb
  constructor
  · have he := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hi
    rw [compl_Ioi, ht] at he
    simp only [F] at hb
    linarith
  · intro w
    rw [integral_Ici_eq_integral_Ioi, ht]

theorem column_integral {ρ : ℝ → ℝ} (hf : ContDiff ℝ 1 ρ)
    (hs : HasCompactSupport ρ) (x w : ℝ) :
    (∫ r, column ρ x (r,w)) = ρ (x-w) := by
  have hi := shifted_derivative_integrable hf hs x
  have he : (fun r => column ρ x (r,w)) = fun r =>
      (Ici w).indicator (fun r => deriv ρ (x-r)) r-
        (if w ≤ 0 then (1 : ℝ) else 0)*deriv ρ (x-r) := by
    funext r
    simp only [column, step, indicator, mem_Ici]
    split_ifs <;> ring
  rw [he, integral_sub (hi.indicator measurableSet_Ici) (hi.const_mul _),
    integral_indicator measurableSet_Ici, integral_const_mul,
    (shifted_derivative_integrals hf hs x).1, mul_zero, sub_zero]
  exact (shifted_derivative_integrals hf hs x).2 w

theorem column_measurable {ρ : ℝ → ℝ} (hf : ContDiff ℝ 1 ρ) (x : ℝ) :
    Measurable (column ρ x) := by
  have h1 : Measurable (fun p : ℝ × ℝ => if p.2 ≤ p.1 then (1 : ℝ) else 0) :=
    measurable_const.ite (measurableSet_le measurable_snd measurable_fst) measurable_const
  have h0 : Measurable (fun p : ℝ × ℝ => if p.2 ≤ 0 then (1 : ℝ) else 0) :=
    measurable_const.ite (measurableSet_le measurable_snd measurable_const) measurable_const
  exact ((hf.continuous_deriv le_rfl).measurable.comp (measurable_const.sub measurable_fst)).mul (h1.sub h0)

theorem step_bound (A B r w : ℝ) (hr : r ∈ Icc A B) :
    ‖step r w‖ ≤ (Icc (min 0 A) (max 0 B)).indicator (fun _ => (1 : ℝ)) w := by
  by_cases hw : w ∈ Icc (min 0 A) (max 0 B)
  · rw [indicator_of_mem hw]
    unfold step
    split_ifs <;> norm_num
  · rw [indicator_of_notMem hw]
    rcases lt_or_ge w (min 0 A) with hl | hl
    · have h0 : w ≤ 0 := hl.le.trans (min_le_left _ _)
      have h1 : w ≤ r := hl.le.trans ((min_le_right _ _).trans hr.1)
      simp [step,h0,h1]
    · have hu : max 0 B < w := lt_of_not_ge (fun h => hw ⟨hl,h⟩)
      have h0 : ¬w ≤ 0 := not_le.mpr ((le_max_left _ _).trans_lt hu)
      have h1 : ¬w ≤ r := not_le.mpr ((hr.2.trans (le_max_right _ _)).trans_lt hu)
      simp [step,h0,h1]

end OperatorDerivativeRewrite.Foundation.IBMPhysicalDerivativeColumn
