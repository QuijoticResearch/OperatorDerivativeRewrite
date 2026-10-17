import Foundation.CorridorFiniteTimeExit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Before-terminal exit needs a sufficient accumulated loss, with actual integral budgets. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.CorridorIntegratedExit
open CorridorFiniteTimeExit
set_option backward.isDefEq.respectTransparency false

theorem concentration_le_initial_sub_loss {ρ q g : ℝ → ℝ} {s t : ℝ}
    (hst : s≤t) (hc : ContinuousOn ρ (Icc s t))
    (hd : ∀ x∈Ioo s t, HasDerivWithinAt ρ (q x) (Ioi x) x)
    (hg : IntegrableOn g (Icc s t)) (hq : ∀ x∈Ioo s t, q x≤ -g x) :
    ρ t≤ρ s-(∫ x in s..t, g x) := by
  have hh := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hst hc hd hg.neg hq
  change ρ t-ρ s≤∫ y in s..t, -(g y) at hh
  rw [intervalIntegral.integral_neg] at hh
  linarith

theorem reach_threshold_from_budget {ρ q g : ℝ → ℝ} {s t a : ℝ}
    (hst : s≤t) (hc : ContinuousOn ρ (Icc s t))
    (hd : ∀ x∈Ioo s t, HasDerivWithinAt ρ (q x) (Ioi x) x)
    (hg : IntegrableOn g (Icc s t)) (hq : ∀ x∈Ioo s t, q x≤ -g x)
    (hb : ρ s-a≤∫ x in s..t, g x) : ρ t≤a := by
  have hh := concentration_le_initial_sub_loss hst hc hd hg hq
  linarith

theorem strict_exit_from_budget {ρ q g : ℝ → ℝ} {s t a : ℝ}
    (hst : s≤t) (hc : ContinuousOn ρ (Icc s t))
    (hd : ∀ x∈Ioo s t, HasDerivWithinAt ρ (q x) (Ioi x) x)
    (hg : IntegrableOn g (Icc s t)) (hq : ∀ x∈Ioo s t, q x≤ -g x)
    (hb : ρ s-a<∫ x in s..t, g x) : ρ t<a := by
  have hh := concentration_le_initial_sub_loss hst hc hd hg hq
  linarith

theorem exit_before_terminal {ρ q g : ℝ → ℝ} {s t T a : ℝ}
    (hst : s≤t) (htT : t<T) (hc : ContinuousOn ρ (Icc s t))
    (hd : ∀ x∈Ioo s t, HasDerivWithinAt ρ (q x) (Ioi x) x)
    (hg : IntegrableOn g (Icc s t)) (hq : ∀ x∈Ioo s t, q x≤ -g x)
    (hb : ρ s-a<∫ x in s..t, g x) : ∃ u∈Ico s T, ρ u<a :=
  ⟨t, ⟨hst, htT⟩, strict_exit_from_budget hst hc hd hg hq hb⟩

theorem budget_le_margin_if_concentrated {ρ q g : ℝ → ℝ} {s t a : ℝ}
    (hst : s≤t) (hc : ContinuousOn ρ (Icc s t))
    (hd : ∀ x∈Ioo s t, HasDerivWithinAt ρ (q x) (Ioi x) x)
    (hg : IntegrableOn g (Icc s t)) (hq : ∀ x∈Ioo s t, q x≤ -g x)
    (ha : a≤ρ t) : (∫ x in s..t, g x)≤ρ s-a := by
  have hh := concentration_le_initial_sub_loss hst hc hd hg hq
  linarith

def quotedLoss (ε x : ℝ) : ℝ := (1/4)*(1-concentration ε x)
def sourceLoss (ε x : ℝ) : ℝ := (frequency x)^2*(1-concentration ε x)
def actualLoss (ε _x : ℝ) : ℝ := ε/4
def initialMargin (ε : ℝ) : ℝ := concentration ε 0-(1-ε)

theorem initialMargin_eq (ε : ℝ) : initialMargin ε=ε/2 := by
  unfold initialMargin concentration
  ring

theorem quotedLoss_continuous (ε : ℝ) : Continuous (quotedLoss ε) := by
  unfold quotedLoss concentration
  fun_prop

theorem quotedLoss_polynomial (ε x : ℝ) : quotedLoss ε x=ε/8+(ε/16)*x := by
  unfold quotedLoss concentration
  ring

theorem sourceLoss_eq {ε x : ℝ} (hx : x<1) : sourceLoss ε x=quotedLoss ε x := by
  rw [sourceLoss, frequency_eq hx]
  unfold quotedLoss
  ring

theorem actualLoss_eq_negative_derivative (ε x : ℝ) :
    actualLoss ε x= -deriv (concentration ε) x := by
  rw [(concentration_hasDerivAt ε x).deriv]
  unfold actualLoss
  ring

theorem quotedLoss_integral (ε t : ℝ) :
    (∫ x in (0:ℝ)..t, quotedLoss ε x)=ε*t/8+ε*t^2/32 := by
  have he : quotedLoss ε=(fun x => ε/8+(ε/16)*x) := funext (quotedLoss_polynomial ε)
  have hi : IntervalIntegrable (fun x : ℝ => (ε/16)*x) volume 0 t :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 t
  rw [he, intervalIntegral.integral_add intervalIntegrable_const hi,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  simp only [sub_zero, zero_pow (by norm_num : (2:ℕ)≠0), smul_eq_mul]
  ring

theorem sourceLoss_intervalIntegrable (ε : ℝ) {t : ℝ} (ht0 : 0≤t) (ht1 : t≤1) :
    IntervalIntegrable (sourceLoss ε) volume 0 t := by
  apply ((quotedLoss_continuous ε).intervalIntegrable 0 t).congr_uIoo
  intro x hx
  rw [uIoo_of_le ht0] at hx
  exact (sourceLoss_eq (hx.2.trans_le ht1)).symm

theorem sourceLoss_integral (ε : ℝ) {t : ℝ} (ht0 : 0≤t) (ht1 : t≤1) :
    (∫ x in (0:ℝ)..t, sourceLoss ε x)=ε*t/8+ε*t^2/32 := by
  calc
    _ = ∫ x in (0:ℝ)..t, quotedLoss ε x := by
      apply intervalIntegral.integral_congr_uIoo
      intro x hx
      rw [uIoo_of_le ht0] at hx
      exact sourceLoss_eq (hx.2.trans_le ht1)
    _ = _ := quotedLoss_integral ε t

theorem actualLoss_integral (ε t : ℝ) :
    (∫ x in (0:ℝ)..t, actualLoss ε x)=ε*t/4 := by
  simp only [actualLoss, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  ring

theorem actualLoss_intervalIntegrable (ε s t : ℝ) :
    IntervalIntegrable (actualLoss ε) volume s t := intervalIntegrable_const

theorem exact_loss_identity (ε t : ℝ) :
    concentration ε 0-concentration ε t=∫ x in (0:ℝ)..t, actualLoss ε x := by
  rw [actualLoss_integral]
  unfold concentration
  ring

theorem source_budget_upper {ε t : ℝ} (hε : 0<ε) (ht0 : 0≤t) (ht1 : t≤1) :
    (∫ x in (0:ℝ)..t, sourceLoss ε x)≤5*ε/32 := by
  rw [sourceLoss_integral ε ht0 ht1]
  have ht2 : t^2≤1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (by linarith : (0:ℝ)≤1+t)]
  have hm1 := mul_le_mul_of_nonneg_left ht1 hε.le
  have hm2 := mul_le_mul_of_nonneg_left ht2 hε.le
  nlinarith

theorem source_budget_below_margin {ε t : ℝ} (hε : 0<ε) (ht0 : 0≤t) (ht1 : t≤1) :
    (∫ x in (0:ℝ)..t, sourceLoss ε x) < initialMargin ε := by
  rw [initialMargin_eq]
  have hh := source_budget_upper hε ht0 ht1
  linarith

theorem actual_budget_below_margin {ε t : ℝ} (hε : 0<ε) (ht1 : t≤1) :
    (∫ x in (0:ℝ)..t, actualLoss ε x) < initialMargin ε := by
  rw [actualLoss_integral, initialMargin_eq]
  have hm := mul_le_mul_of_nonneg_left ht1 hε.le
  nlinarith

theorem terminal_budgets (ε : ℝ) :
    (∫ x in (0:ℝ)..1, sourceLoss ε x)=5*ε/32 ∧
      (∫ x in (0:ℝ)..1, actualLoss ε x)=ε/4 ∧ initialMargin ε=ε/2 := by
  rw [sourceLoss_integral ε (by norm_num) le_rfl, actualLoss_integral, initialMargin_eq]
  constructor
  · ring
  · constructor <;> ring

theorem terminal_budget_order {ε : ℝ} (hε : 0<ε) :
    0<(∫ x in (0:ℝ)..1, sourceLoss ε x) ∧
      (∫ x in (0:ℝ)..1, sourceLoss ε x)<(∫ x in (0:ℝ)..1, actualLoss ε x) ∧
      (∫ x in (0:ℝ)..1, actualLoss ε x) < initialMargin ε := by
  rw [(terminal_budgets ε).1, (terminal_budgets ε).2.1, initialMargin_eq]
  constructor
  · positivity
  · constructor <;> linarith

def boundaryPath (a t : ℝ) : ℝ := a+1-t

theorem equality_budget_example (a : ℝ) :
    (∀ x, HasDerivAt (boundaryPath a) (-1) x) ∧
      ((∫ _x in (0:ℝ)..1, (1:ℝ))=boundaryPath a 0-a) ∧
      boundaryPath a 1=a ∧ ¬∃ t∈Icc (0:ℝ) 1, boundaryPath a t<a := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    exact (hasDerivAt_id x).const_sub (a+1)
  · simp [boundaryPath]
  · unfold boundaryPath; ring
  · rintro ⟨t, ht, hh⟩
    unfold boundaryPath at hh
    linarith [ht.2]

end OperatorDerivativeRewrite.Foundation.CorridorIntegratedExit
