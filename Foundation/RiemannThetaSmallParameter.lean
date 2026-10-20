import Foundation.RiemannThetaHolomorphic
import Mathlib.Analysis.Complex.Exponential
/-! Arithmetic theta bounds valid for every strictly positive real parameter.
A cubic exponential estimate and finite telescoping give a coarse v^(-3)
envelope for moments through order four, including the near-strip-boundary regime. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
namespace OperatorDerivativeRewrite.Foundation.RiemannThetaSmallParameter
open RiemannQuarticKernel RiemannQuarticSaddleTheta RiemannThetaComplexKernel

private theorem inverse_square_gap (m : ℝ) (hm : 1 ≤ m) :
    (m^2)⁻¹ ≤ 2*(1/m-1/(m+1)) := by
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m+1 := by linarith
  have hid : 2*(1/m-1/(m+1))=2/(m*(m+1)) := by field_simp; ring
  rw [hid,← one_div]
  apply (div_le_div_iff₀ (sq_pos_of_pos hm0) (mul_pos hm0 hm1)).mpr
  nlinarith

theorem thetaTerm_four_polynomial_bound (v : ℝ) (hv : 0 < v) (n : ℕ) :
    thetaTerm 4 v n ≤ (6/(Real.pi^3*v^3))*((((n+1 : ℕ) : ℝ)^2)⁻¹) := by
  let m : ℝ := (n+1 : ℕ)
  have hm : 0 < m := by dsimp [m]; positivity
  let a := Real.pi*v*m^2
  have ha : 0 < a := by dsimp [a]; positivity
  have he := Real.pow_div_factorial_le_exp a ha.le 3
  norm_num at he
  have hmul := mul_le_mul_of_nonneg_right he (Real.exp_pos (-a)).le
  rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at hmul
  have hid : thetaTerm 4 v n=m^4*Real.exp (-a) := by
    unfold thetaTerm
    dsimp [m,a]
    push_cast
    congr 2 <;> ring
  rw [hid]
  change m^4*Real.exp (-a) ≤ (6/(Real.pi^3*v^3))*(m^2)⁻¹
  have hright : (6/(Real.pi^3*v^3))*(m^2)⁻¹=6/(Real.pi^3*v^3*m^2) := by ring
  rw [hright]
  apply (le_div_iff₀ (by positivity : 0 < Real.pi^3*v^3*m^2)).mpr
  have hprod : m^4*Real.exp (-a)*(Real.pi^3*v^3*m^2)=a^3*Real.exp (-a) := by dsimp [a]; ring
  rw [hprod]
  nlinarith

theorem thetaMoment_polynomial_bound (k : ℕ) (hk : k ≤ 4) (v : ℝ) (hv : 0 < v) :
    thetaMoment k v ≤ 12/(Real.pi^3*v^3) := by
  have hC : 0 ≤ (6 : ℝ)/(Real.pi^3*v^3) := by positivity
  have hpoint (n : ℕ) : thetaTerm k v n ≤
      (12/(Real.pi^3*v^3))*(1/((n+1 : ℕ) : ℝ)-1/((n+2 : ℕ) : ℝ)) := by
    have hn : (1 : ℝ) ≤ (n+1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hpow := pow_le_pow_right₀ hn hk
    have hterm : thetaTerm k v n ≤ thetaTerm 4 v n := by
      unfold thetaTerm
      simpa only [Nat.cast_add,Nat.cast_one] using mul_le_mul_of_nonneg_right hpow (Real.exp_pos (-Real.pi*((n : ℝ)+1)^2*v)).le
    have hgap := inverse_square_gap ((n+1 : ℕ) : ℝ) hn
    have hm := mul_le_mul_of_nonneg_left hgap hC
    apply hterm.trans ((thetaTerm_four_polynomial_bound v hv n).trans _)
    convert hm using 1 <;> push_cast <;> ring
  have htel (N : ℕ) :
      (∑ n ∈ Finset.range N, (1/((n+1 : ℕ) : ℝ)-1/((n+2 : ℕ) : ℝ)))=1-1/((N+1 : ℕ) : ℝ) := by
    induction N with
    | zero => norm_num
    | succ N ih =>
      rw [Finset.sum_range_succ,ih]
      push_cast
      ring
  apply Real.tsum_le_of_sum_range_le (fun n => thetaTerm_nonneg k v n)
  intro N
  calc
    _ ≤ ∑ n ∈ Finset.range N,
        (12/(Real.pi^3*v^3))*(1/((n+1 : ℕ) : ℝ)-1/((n+2 : ℕ) : ℝ)) :=
      Finset.sum_le_sum (fun n _ => hpoint n)
    _ = (12/(Real.pi^3*v^3))*(1-1/((N+1 : ℕ) : ℝ)) := by rw [← Finset.mul_sum,htel]
    _ ≤ _ := by
      have hc : 0 ≤ (12 : ℝ)/(Real.pi^3*v^3) := by positivity
      have hm := mul_le_mul_of_nonneg_left (by positivity : 0 ≤ 1/((N+1 : ℕ) : ℝ)) hc
      nlinarith

theorem moment_norm_polynomial_bound (k : ℕ) (hk : k ≤ 4) (v : ℂ) (hv : 0 < v.re) :
    ‖moment k v‖ ≤ 12/(Real.pi^3*v.re^3) := by
  have hs : Summable (fun n => ‖complexThetaTerm k v n‖) := by
    simp_rw [norm_complexThetaTerm]
    exact thetaTerm_summable k v.re hv
  calc
    _ ≤ ∑' n, ‖complexThetaTerm k v n‖ := norm_tsum_le_tsum_norm hs
    _ = thetaMoment k v.re := by simp only [norm_complexThetaTerm,thetaMoment]
    _ ≤ _ := thetaMoment_polynomial_bound k hk v.re hv

theorem kernel_positive_parameter_bound (q : ℂ) (hq : 0 ≤ q.re)
    (hE : 0 < (Complex.exp (4*q)).re) :
    ‖kernelComplex q‖ ≤ 528*Real.exp (9*q.re)/((Complex.exp (4*q)).re^3) := by
  have h4 := moment_norm_polynomial_bound 4 le_rfl (Complex.exp (4*q)) hE
  have h2 := moment_norm_polynomial_bound 2 (by norm_num) (Complex.exp (4*q)) hE
  have htri := norm_sub_le (2*(Real.pi : ℂ)^2*Complex.exp (9*q)*moment 4 (Complex.exp (4*q)))
    (3*(Real.pi : ℂ)*Complex.exp (5*q)*moment 2 (Complex.exp (4*q)))
  change ‖kernelComplex q‖ ≤ _ at htri
  simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos Real.pi_pos] at htri
  have h9 : ‖Complex.exp (9*q)‖=Real.exp (9*q.re) := by simpa using norm_exp_scaled 9 q
  have h5 : ‖Complex.exp (5*q)‖=Real.exp (5*q.re) := by simpa using norm_exp_scaled 5 q
  rw [h9,h5] at htri
  have h59 : Real.exp (5*q.re) ≤ Real.exp (9*q.re) := Real.exp_le_exp.mpr (by linarith)
  have hpi : 1 ≤ Real.pi^3 := by
    have hsq : 1 ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
    nlinarith [mul_le_mul_of_nonneg_right hsq Real.pi_pos.le,Real.pi_gt_three]
  have hsmall : 12/(Real.pi^3*(Complex.exp (4*q)).re^3) ≤ 12/((Complex.exp (4*q)).re^3) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (by nlinarith [pow_pos hE 3])
  have hpoly : 2*Real.pi^2+3*Real.pi ≤ 44 := by nlinarith [Real.pi_lt_four,Real.pi_gt_three]
  calc
    _ ≤ (2*Real.pi^2*Real.exp (9*q.re)+3*Real.pi*Real.exp (9*q.re))*
        (12/((Complex.exp (4*q)).re^3)) := by
      apply htri.trans
      rw [add_mul]
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (h4.trans hsmall) (by positivity)
      · exact mul_le_mul (mul_le_mul_of_nonneg_left h59 (by positivity : 0 ≤ 3*Real.pi))
          (h2.trans hsmall) (norm_nonneg _) (by positivity)
    _ = (2*Real.pi^2+3*Real.pi)*Real.exp (9*q.re)*(12/((Complex.exp (4*q)).re^3)) := by ring
    _ ≤ 44*Real.exp (9*q.re)*(12/((Complex.exp (4*q)).re^3)) := by gcongr
    _ = _ := by ring

theorem kernel_horizontal_margin_bound (a h : ℝ) (ha : 0 ≤ a) (hh : 0 < Real.cos (4*h)) :
    ‖kernelComplex ((a : ℂ)+(h : ℂ)*Complex.I)‖ ≤
      (528/(Real.cos (4*h))^3)*Real.exp (-3*a) := by
  let q := (a : ℂ)+(h : ℂ)*Complex.I
  have hq : q.re=a := by simp [q]
  have hE : (Complex.exp (4*q)).re=Real.exp (4*a)*Real.cos (4*h) := by
    simp [q,Complex.exp_re,Complex.mul_re,Complex.mul_im]
  have hpos : 0 < (Complex.exp (4*q)).re := by rw [hE]; positivity
  have hbound := kernel_positive_parameter_bound q (by rw [hq]; exact ha) hpos
  rw [hq,hE] at hbound
  apply hbound.trans_eq
  have he3 : (Real.exp (4*a))^3=Real.exp (12*a) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have he : Real.exp (9*a)/Real.exp (12*a)=Real.exp (-3*a) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [mul_pow,he3]
  calc
    _ = (528/Real.cos (4*h)^3)*(Real.exp (9*a)/Real.exp (12*a)) := by ring
    _ = _ := by rw [he]

end OperatorDerivativeRewrite.Foundation.RiemannThetaSmallParameter
