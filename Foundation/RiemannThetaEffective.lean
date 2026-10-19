import Foundation.RiemannQuarticKernel
import Mathlib.Analysis.SpecificLimits.Basic

/-! Effective, real-arithmetic majorants for the actual theta series. -/
noncomputable section
open MeasureTheory Filter Set Real
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannThetaEffective
open RiemannQuarticKernel

def ratio (v : ℝ) : ℝ := 16*exp (-3*Real.pi*v)

theorem ratio_nonneg (v : ℝ) : 0 ≤ ratio v := by unfold ratio; positivity

theorem exp_nine_halves_ge : (32 : ℝ) ≤ exp (9/2) := by
  have h : (3/2 : ℝ) ≤ exp (1/2) := by have hh := add_one_le_exp (1/2); linarith
  calc
    (32 : ℝ) ≤ (3/2 : ℝ)^9 := by norm_num
    _ ≤ exp (1/2)^9 := pow_le_pow_left₀ (by norm_num) h 9
    _ = exp (9/2) := by rw [← exp_nat_mul]; norm_num

theorem ratio_le_half (v : ℝ) (hv : 1/2 ≤ v) : ratio v ≤ 1/2 := by
  have hx : 9/2 ≤ 3*Real.pi*v := by
    have h := mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ 3*Real.pi)
    nlinarith [Real.pi_gt_three]
  have he : (32 : ℝ) ≤ exp (3*Real.pi*v) :=
    exp_nine_halves_ge.trans (exp_le_exp.mpr hx)
  have hi : (exp (3*Real.pi*v))⁻¹ ≤ (32 : ℝ)⁻¹ :=
    (inv_le_inv₀ (exp_pos _) (by norm_num)).mpr he
  unfold ratio
  rw [show -3*Real.pi*v=-(3*Real.pi*v) by ring, exp_neg]
  nlinarith

theorem thetaTerm_order_le (k l n : ℕ) (hkl : k ≤ l) (v : ℝ) :
    thetaTerm k v n ≤ thetaTerm l v n := by
  unfold thetaTerm
  apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
  exact pow_le_pow_right₀ (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith) hkl

theorem thetaTerm_four_step (v : ℝ) (hv : 0 ≤ v) (n : ℕ) :
    thetaTerm 4 v (n+1) ≤ ratio v*thetaTerm 4 v n := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hp : ((n : ℝ)+2)^4 ≤ 16*((n : ℝ)+1)^4 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ (n : ℝ)+2)
      (by linarith : (n : ℝ)+2 ≤ 2*((n : ℝ)+1)) 4
    nlinarith
  have he : exp (-Real.pi*((n : ℝ)+2)^2*v) =
      exp (-Real.pi*((n : ℝ)+1)^2*v)*exp (-Real.pi*(2*(n : ℝ)+3)*v) := by
    rw [← exp_add]
    congr 1
    ring
  have hg : exp (-Real.pi*(2*(n : ℝ)+3)*v) ≤ exp (-3*Real.pi*v) := by
    apply exp_le_exp.mpr
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hn) hv]
  simp only [thetaTerm, Nat.cast_add, Nat.cast_one]
  rw [show (n : ℝ)+1+1=(n : ℝ)+2 by ring, he]
  calc
    _ ≤ (16*((n : ℝ)+1)^4)*
        (exp (-Real.pi*((n : ℝ)+1)^2*v)*exp (-3*Real.pi*v)) := by
      gcongr
    _ = _ := by unfold ratio; ring

theorem thetaTerm_shift_bound (v : ℝ) (hv : 0 ≤ v) (N n : ℕ) :
    thetaTerm 4 v (N+n) ≤ thetaTerm 4 v N*(ratio v)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ ≤ ratio v*thetaTerm 4 v (N+n) := by
        simpa only [Nat.add_succ] using thetaTerm_four_step v hv (N+n)
      _ ≤ ratio v*(thetaTerm 4 v N*(ratio v)^n) :=
        mul_le_mul_of_nonneg_left ih (ratio_nonneg v)
      _ = _ := by rw [pow_succ]; ring

def tail (k N : ℕ) (v : ℝ) : ℝ := ∑' n, thetaTerm k v (N+n)

theorem tail_summable (k N : ℕ) (v : ℝ) (hv : 0 < v) :
    Summable (fun n => thetaTerm k v (N+n)) :=
  (thetaTerm_summable k v hv).comp_injective
    (show Function.Injective (fun n : ℕ => N+n) by intro a b h; exact Nat.add_left_cancel h)

theorem tail_four_bound (N : ℕ) (v : ℝ) (hv : 1/2 ≤ v) :
    tail 4 N v ≤ 2*thetaTerm 4 v N := by
  have hr0 := ratio_nonneg v
  have hr := ratio_le_half v hv
  have hr1 : ratio v < 1 := by linarith
  have hs := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (thetaTerm 4 v N)
  have hh : tail 4 N v ≤ thetaTerm 4 v N*(1-ratio v)⁻¹ := by
    exact ((tail_summable 4 N v (by linarith)).tsum_le_tsum
      (thetaTerm_shift_bound v (by linarith) N) hs.summable).trans_eq hs.tsum_eq
  apply hh.trans
  rw [← div_eq_mul_inv, div_le_iff₀ (by linarith : 0 < 1-ratio v)]
  nlinarith [thetaTerm_nonneg 4 v N]

theorem tail_order_bound (k N : ℕ) (hk : k ≤ 4) (v : ℝ) (hv : 1/2 ≤ v) :
    tail k N v ≤ 2*thetaTerm 4 v N := by
  apply le_trans _ (tail_four_bound N v hv)
  exact (tail_summable k N v (by linarith)).tsum_le_tsum
    (fun n => thetaTerm_order_le k 4 (N+n) hk v) (tail_summable 4 N v (by linarith))

theorem thetaMoment_bound (k : ℕ) (hk : k ≤ 4) (v : ℝ) (hv : 1/2 ≤ v) :
    thetaMoment k v ≤ 2*exp (-Real.pi*v) := by
  have h := tail_order_bound k 0 hk v hv
  simpa [tail, thetaMoment, thetaTerm] using h

theorem kernel_effective_bound (u : ℝ) (hu : 0 ≤ u) :
    kernel u ≤ 64*exp (9*u-Real.pi*exp (4*u)) := by
  have hv : 1/2 ≤ exp (4*u) := by have h := one_le_exp (by positivity : 0 ≤ 4*u); linarith
  have ht := thetaMoment_bound 4 le_rfl (exp (4*u)) hv
  have h2 := thetaMoment_nonneg 2 (exp (4*u))
  have hp : 4*Real.pi^2 ≤ 64 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  calc
    kernel u ≤ 2*Real.pi^2*exp (9*u)*thetaMoment 4 (exp (4*u)) := by
      unfold kernel
      have h : 0 ≤ 3*Real.pi*exp (5*u)*thetaMoment 2 (exp (4*u)) := by positivity
      linarith
    _ ≤ 2*Real.pi^2*exp (9*u)*(2*exp (-Real.pi*exp (4*u))) := by gcongr
    _ = 4*Real.pi^2*exp (9*u-Real.pi*exp (4*u)) := by rw [sub_eq_add_neg, exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hp (exp_pos _).le

end OperatorDerivativeRewrite.Foundation.RiemannThetaEffective
