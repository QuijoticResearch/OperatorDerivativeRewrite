import Foundation.RiemannThetaEffective

/-! Exact finite theta truncation and an effective remainder for the literal
arithmetic kernel. -/
noncomputable section
open MeasureTheory Filter Set Real
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannThetaTruncation
open RiemannQuarticKernel RiemannThetaEffective

def thetaPrefix (k N : ℕ) (v : ℝ) : ℝ := ∑ n ∈ Finset.range N, thetaTerm k v n

theorem prefix_add_tail (k N : ℕ) (v : ℝ) (hv : 0 < v) :
    thetaPrefix k N v+tail k N v=thetaMoment k v := by
  have h := (thetaTerm_summable k v hv).sum_add_tsum_nat_add N
  simpa only [thetaPrefix, tail, thetaMoment, Nat.add_comm] using h

theorem tail_nonneg (k N : ℕ) (v : ℝ) : 0 ≤ tail k N v :=
  tsum_nonneg (fun n => thetaTerm_nonneg k v (N+n))

def partialKernel (N : ℕ) (u : ℝ) : ℝ :=
  2*Real.pi^2*exp (9*u)*thetaPrefix 4 N (exp (4*u))-
    3*Real.pi*exp (5*u)*thetaPrefix 2 N (exp (4*u))

theorem kernel_remainder (N : ℕ) (u : ℝ) :
    kernel u-partialKernel N u =
      2*Real.pi^2*exp (9*u)*tail 4 N (exp (4*u))-
        3*Real.pi*exp (5*u)*tail 2 N (exp (4*u)) := by
  have h4 := prefix_add_tail 4 N (exp (4*u)) (exp_pos _)
  have h2 := prefix_add_tail 2 N (exp (4*u)) (exp_pos _)
  rw [kernel, partialKernel, ← h4, ← h2]
  ring

theorem partialKernel_continuous (N : ℕ) : Continuous (partialKernel N) := by
  unfold partialKernel thetaPrefix thetaTerm
  fun_prop

theorem kernel_remainder_bound (N : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    |kernel u-partialKernel N u| ≤
      88*((N : ℝ)+1)^4*exp (9*u-Real.pi*((N : ℝ)+1)^2*exp (4*u)) := by
  have hv : 1/2 ≤ exp (4*u) := by have h := one_le_exp (by positivity : 0 ≤ 4*u); linarith
  have h4 := tail_four_bound N (exp (4*u)) hv
  have h2 := tail_order_bound 2 N (by norm_num) (exp (4*u)) hv
  have ht4 := tail_nonneg 4 N (exp (4*u))
  have ht2 := tail_nonneg 2 N (exp (4*u))
  have hθ := thetaTerm_nonneg 4 (exp (4*u)) N
  have he : exp (5*u) ≤ exp (9*u) := exp_le_exp.mpr (by linarith)
  have hp : 4*Real.pi^2+6*Real.pi ≤ 88 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  rw [kernel_remainder]
  calc
    _ ≤ 2*Real.pi^2*exp (9*u)*tail 4 N (exp (4*u))+
        3*Real.pi*exp (5*u)*tail 2 N (exp (4*u)) := by
      exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)])
    _ ≤ 2*Real.pi^2*exp (9*u)*(2*thetaTerm 4 (exp (4*u)) N)+
        3*Real.pi*exp (9*u)*(2*thetaTerm 4 (exp (4*u)) N) := by gcongr
    _ = (4*Real.pi^2+6*Real.pi)*exp (9*u)*thetaTerm 4 (exp (4*u)) N := by ring
    _ ≤ 88*exp (9*u)*thetaTerm 4 (exp (4*u)) N := by gcongr
    _ = _ := by
      unfold thetaTerm
      rw [sub_eq_add_neg, exp_add]
      ring

theorem tilted_remainder_exponent (N : ℕ) (hN : 1 ≤ N) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 8/5) :
    8*u^4+9*u-Real.pi*((N : ℝ)+1)^2*exp (4*u) ≤ -Real.pi*((N : ℝ)+1)^2 := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hm : 4 ≤ ((N : ℝ)+1)^2 := by nlinarith [sq_nonneg ((N : ℝ)-1)]
  have hp : 12 ≤ Real.pi*((N : ℝ)+1)^2 := by
    have h := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (sq_nonneg ((N : ℝ)+1))
    nlinarith
  have h3 := pow_le_pow_left₀ hu0 hu1 3
  have hu4 : 8*u^4 ≤ (4096/125 : ℝ)*u := by
    have h := mul_le_mul_of_nonneg_left h3 hu0
    nlinarith
  have ht := mul_le_mul_of_nonneg_left (add_one_le_exp (4*u))
    (by positivity : 0 ≤ Real.pi*((N : ℝ)+1)^2)
  have hl : ((4096/125 : ℝ)+9)*u ≤ (4*Real.pi*((N : ℝ)+1)^2)*u := by
    apply mul_le_mul_of_nonneg_right _ hu0
    linarith
  nlinarith

theorem tilted_remainder_bound (k N : ℕ) (hk : k ≤ 2) (hN : 1 ≤ N)
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 8/5) :
    |u^k*exp (8*u^4)*(kernel u-partialKernel N u)| ≤
      352*((N : ℝ)+1)^4*exp (-Real.pi*((N : ℝ)+1)^2) := by
  have hk' : u^k ≤ 4 := by interval_cases k <;> norm_num <;> nlinarith
  have he := tilted_remainder_exponent N hN u hu0 hu1
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hu0 _), abs_of_pos (exp_pos _)]
  calc
    _ ≤ 4*exp (8*u^4)*(88*((N : ℝ)+1)^4*
        exp (9*u-Real.pi*((N : ℝ)+1)^2*exp (4*u))) := by
      gcongr
      exact kernel_remainder_bound N u hu0
    _ = 352*((N : ℝ)+1)^4*
        exp (8*u^4+9*u-Real.pi*((N : ℝ)+1)^2*exp (4*u)) := by
      rw [show 8*u^4+9*u-Real.pi*((N : ℝ)+1)^2*exp (4*u)=
        8*u^4+(9*u-Real.pi*((N : ℝ)+1)^2*exp (4*u)) by ring, exp_add]
      ring
    _ ≤ _ := by gcongr

theorem fifteen_term_numeric_bound :
    352*((15 : ℝ)+1)^4*exp (-Real.pi*((15 : ℝ)+1)^2) ≤ (1/10^100 : ℝ) := by
  have he : (2 : ℝ)^768 ≤ exp 768 := by
    have h : (2 : ℝ) ≤ exp 1 := by have hh := add_one_le_exp (1 : ℝ); linarith
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h 768
    simpa only [← exp_nat_mul, Nat.cast_ofNat, mul_one] using hp
  have hi : exp (-Real.pi*((15 : ℝ)+1)^2) ≤ ((2 : ℝ)^768)⁻¹ := by
    calc
      _ ≤ exp (-(768 : ℝ)) := exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
      _ = (exp (768 : ℝ))⁻¹ := exp_neg _
      _ ≤ _ := (inv_le_inv₀ (exp_pos _) (by positivity)).mpr he
  calc
    _ ≤ 352*((15 : ℝ)+1)^4*((2 : ℝ)^768)⁻¹ :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ ≤ _ := by
      rw [show (768 : ℕ)=128*6 by decide, pow_mul]
      norm_num

theorem fifteen_term_remainder (k : ℕ) (hk : k ≤ 2) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 8/5) :
    |u^k*exp (8*u^4)*(kernel u-partialKernel 15 u)| ≤ (1/10^100 : ℝ) :=
  (tilted_remainder_bound k 15 hk (by norm_num) u hu0 hu1).trans fifteen_term_numeric_bound

end OperatorDerivativeRewrite.Foundation.RiemannThetaTruncation
