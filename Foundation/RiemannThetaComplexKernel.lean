import Foundation.RiemannQuarticSaddleTheta
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-! An explicit complex-series extension of the arithmetic integration kernel.
Real agreement and the stated half-plane tail estimates are proved. The
nonvanishing region concerns this kernel; zero control for its Fourier
transform and a holomorphic contour argument remain separate obligations. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.RiemannThetaComplexKernel
open RiemannQuarticSaddleTheta RiemannQuarticKernel

def moment (k : ℕ) (v : ℂ) : ℂ := ∑' n, complexThetaTerm k v n

theorem term_real (k : ℕ) (v : ℝ) (n : ℕ) :
    complexThetaTerm k (v : ℂ) n=(thetaTerm k v n : ℂ) := by
  simp only [complexThetaTerm, thetaTerm, Complex.ofReal_mul, Complex.ofReal_exp,
    Complex.ofReal_pow, Complex.ofReal_neg, Nat.cast_add, Nat.cast_one]

theorem moment_real (k : ℕ) (v : ℝ) (hv : 0 < v) :
    moment k (v : ℂ)=(thetaMoment k v : ℂ) := by
  have h := Complex.ofRealCLM.map_tsum (thetaTerm_summable k v hv)
  change (thetaMoment k v : ℂ)=∑' n, (thetaTerm k v n : ℂ) at h
  rw [h]
  apply tsum_congr
  intro n
  exact term_real k v n

theorem moment_split (k : ℕ) (v : ℂ) (hv : 0 < v.re) :
    moment k v=complexThetaTerm k v 0+complexThetaTail k 1 v := by
  have hs : Summable (complexThetaTerm k v) := by
    simpa only [Nat.zero_add] using complexThetaTail_summable k 0 v hv
  have h := hs.sum_add_tsum_nat_add 1
  simpa only [moment, complexThetaTail, Finset.sum_range_one, Nat.add_comm] using h.symm

def kernelComplex (u : ℂ) : ℂ :=
  2*(Real.pi : ℂ)^2*Complex.exp (9*u)*moment 4 (Complex.exp (4*u))-
    3*(Real.pi : ℂ)*Complex.exp (5*u)*moment 2 (Complex.exp (4*u))

def leading (u : ℂ) : ℂ :=
  (2*(Real.pi : ℂ)^2*Complex.exp (9*u)-3*(Real.pi : ℂ)*Complex.exp (5*u))*
    Complex.exp (-(Real.pi : ℂ)*Complex.exp (4*u))

theorem kernelComplex_real (u : ℝ) : kernelComplex (u : ℂ)=(kernel u : ℂ) := by
  have h4 := moment_real 4 (Real.exp (4*u)) (Real.exp_pos _)
  have h2 := moment_real 2 (Real.exp (4*u)) (Real.exp_pos _)
  simp only [kernelComplex, kernel, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_pow, Complex.ofReal_exp, Complex.ofReal_ofNat] at h4 h2 ⊢
  rw [h4,h2]

theorem leading_theta_norm (k : ℕ) (v : ℂ) :
    ‖complexThetaTerm k v 0‖=Real.exp (-Real.pi*v.re) := by
  rw [norm_complexThetaTerm]
  simp [thetaTerm]

theorem remainder (u : ℂ) (hu : 0 < (Complex.exp (4*u)).re) :
    kernelComplex u-leading u=
      2*(Real.pi : ℂ)^2*Complex.exp (9*u)*complexThetaTail 4 1 (Complex.exp (4*u))-
        3*(Real.pi : ℂ)*Complex.exp (5*u)*complexThetaTail 2 1 (Complex.exp (4*u)) := by
  unfold kernelComplex leading
  rw [moment_split 4 _ hu, moment_split 2 _ hu]
  simp only [complexThetaTerm, Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add, one_pow, one_mul, Complex.ofReal_neg, Complex.ofReal_one, neg_mul]
  ring

theorem leading_factor (u : ℂ) :
    leading u=(Real.pi : ℂ)*Complex.exp (5*u)*
      (2*(Real.pi : ℂ)*Complex.exp (4*u)-3)*
        Complex.exp (-(Real.pi : ℂ)*Complex.exp (4*u)) := by
  have he : Complex.exp (9*u)=Complex.exp (5*u)*Complex.exp (4*u) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  unfold leading
  rw [he]
  ring

theorem prefactor_lower (u : ℂ) (ha : 0 ≤ u.re) :
    3*Real.exp (4*u.re) ≤ ‖2*(Real.pi : ℂ)*Complex.exp (4*u)-3‖ := by
  have he : 1 ≤ Real.exp (4*u.re) := Real.one_le_exp (by positivity)
  have hn := norm_sub_norm_le (2*(Real.pi : ℂ)*Complex.exp (4*u)) (3 : ℂ)
  have heq : ‖2*(Real.pi : ℂ)*Complex.exp (4*u)‖=2*Real.pi*Real.exp (4*u.re) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_exp]
    norm_num [Complex.mul_re]
  rw [heq] at hn
  norm_num at hn
  nlinarith [Real.pi_gt_three]

theorem norm_pi : ‖(Real.pi : ℂ)‖=Real.pi := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

theorem norm_exp_scaled (a : ℝ) (u : ℂ) :
    ‖Complex.exp ((a : ℂ)*u)‖=Real.exp (a*u.re) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

theorem leading_norm_lower (u : ℂ) (ha : 0 ≤ u.re) :
    3*Real.pi*Real.exp (9*u.re)*Real.exp (-Real.pi*(Complex.exp (4*u)).re) ≤
      ‖leading u‖ := by
  have h5 : ‖Complex.exp (5*u)‖=Real.exp (5*u.re) := by
    simpa using norm_exp_scaled 5 u
  have he : ‖Complex.exp (-(Real.pi : ℂ)*Complex.exp (4*u))‖=
      Real.exp (-Real.pi*(Complex.exp (4*u)).re) := by
    simpa only [Complex.ofReal_neg] using norm_exp_scaled (-Real.pi) (Complex.exp (4*u))
  have h9 : Real.exp (9*u.re)=Real.exp (5*u.re)*Real.exp (4*u.re) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [leading_factor, norm_mul, norm_mul, norm_mul, norm_pi, h5, he]
  have hp := prefactor_lower u ha
  calc
    _ = Real.pi*Real.exp (5*u.re)*(3*Real.exp (4*u.re))*
        Real.exp (-Real.pi*(Complex.exp (4*u)).re) := by rw [h9]; ring
    _ ≤ _ := by gcongr

theorem relative_of_tail_bounds (u : ℂ) (ha : 0 ≤ u.re)
    (hu : 0 < (Complex.exp (4*u)).re) (rho : ℝ) (hrho : 0 ≤ rho)
    (h4 : ‖complexThetaTail 4 1 (Complex.exp (4*u))‖ ≤
      rho*Real.exp (-Real.pi*(Complex.exp (4*u)).re))
    (h2 : ‖complexThetaTail 2 1 (Complex.exp (4*u))‖ ≤
      rho*Real.exp (-Real.pi*(Complex.exp (4*u)).re)) :
    ‖kernelComplex u-leading u‖ ≤ 4*rho*‖leading u‖ := by
  have h9 : ‖Complex.exp (9*u)‖=Real.exp (9*u.re) := by simpa using norm_exp_scaled 9 u
  have h5 : ‖Complex.exp (5*u)‖=Real.exp (5*u.re) := by simpa using norm_exp_scaled 5 u
  have hc9 : ‖2*(Real.pi : ℂ)^2*Complex.exp (9*u)‖=2*Real.pi^2*Real.exp (9*u.re) := by
    simp only [norm_mul, norm_pow, norm_pi, h9]
    norm_num
  have hc5 : ‖3*(Real.pi : ℂ)*Complex.exp (5*u)‖=3*Real.pi*Real.exp (5*u.re) := by
    simp only [norm_mul, norm_pi, h5]
    norm_num
  have h59 : Real.exp (5*u.re) ≤ Real.exp (9*u.re) := Real.exp_le_exp.mpr (by nlinarith)
  have hp : 2*Real.pi^2+3*Real.pi ≤ 12*Real.pi := by
    nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hc : 2*Real.pi^2*Real.exp (9*u.re)+3*Real.pi*Real.exp (5*u.re) ≤
      12*Real.pi*Real.exp (9*u.re) := by
    calc
      _ ≤ 2*Real.pi^2*Real.exp (9*u.re)+3*Real.pi*Real.exp (9*u.re) := by gcongr
      _ = (2*Real.pi^2+3*Real.pi)*Real.exp (9*u.re) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
  rw [remainder u hu]
  calc
    _ ≤ ‖2*(Real.pi : ℂ)^2*Complex.exp (9*u)*complexThetaTail 4 1 (Complex.exp (4*u))‖+
        ‖3*(Real.pi : ℂ)*Complex.exp (5*u)*complexThetaTail 2 1 (Complex.exp (4*u))‖ :=
      norm_sub_le _ _
    _ = (2*Real.pi^2*Real.exp (9*u.re))*‖complexThetaTail 4 1 (Complex.exp (4*u))‖+
        (3*Real.pi*Real.exp (5*u.re))*‖complexThetaTail 2 1 (Complex.exp (4*u))‖ := by
      rw [norm_mul, hc9, norm_mul, hc5]
    _ ≤ (2*Real.pi^2*Real.exp (9*u.re))*(rho*Real.exp (-Real.pi*(Complex.exp (4*u)).re))+
        (3*Real.pi*Real.exp (5*u.re))*(rho*Real.exp (-Real.pi*(Complex.exp (4*u)).re)) := by gcongr
    _ = (2*Real.pi^2*Real.exp (9*u.re)+3*Real.pi*Real.exp (5*u.re))*
        (rho*Real.exp (-Real.pi*(Complex.exp (4*u)).re)) := by ring
    _ ≤ (12*Real.pi*Real.exp (9*u.re))*(rho*Real.exp (-Real.pi*(Complex.exp (4*u)).re)) := by gcongr
    _ = 4*rho*(3*Real.pi*Real.exp (9*u.re)*Real.exp (-Real.pi*(Complex.exp (4*u)).re)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (leading_norm_lower u ha) (by positivity)

theorem relative_bound (u : ℂ) (ha : 0 ≤ u.re) (hu : 1/2 ≤ (Complex.exp (4*u)).re) :
    ‖kernelComplex u-leading u‖ ≤
      128*Real.exp (-3*Real.pi*(Complex.exp (4*u)).re)*‖leading u‖ := by
  have h4 := complexThetaTail_relative 4 le_rfl (Complex.exp (4*u)) hu
  have h2 := complexThetaTail_relative 2 (by norm_num) (Complex.exp (4*u)) hu
  rw [leading_theta_norm] at h4 h2
  have h := relative_of_tail_bounds u ha (by linarith) _ (by positivity) h4 h2
  exact h.trans_eq (by ring)

theorem kernel_ne_zero (u : ℂ) (ha : 0 ≤ u.re) (hu : 1 ≤ (Complex.exp (4*u)).re) :
    kernelComplex u≠0 := by
  have h32 := RiemannThetaEffective.exp_nine_halves_ge
  have h9 : (1024 : ℝ) ≤ Real.exp 9 := by
    calc
      (1024 : ℝ) = 32*32 := by norm_num
      _ ≤ Real.exp (9/2)*Real.exp (9/2) := mul_le_mul h32 h32 (by norm_num) (Real.exp_pos _).le
      _ = Real.exp 9 := by rw [← Real.exp_add]; congr 1; ring
  have hR : 9 ≤ 3*Real.pi*(Complex.exp (4*u)).re := by
    have h := mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ 3*Real.pi)
    nlinarith [Real.pi_gt_three]
  have hE : (1024 : ℝ) ≤ Real.exp (3*Real.pi*(Complex.exp (4*u)).re) :=
    h9.trans (Real.exp_le_exp.mpr hR)
  have hrho : 128*Real.exp (-3*Real.pi*(Complex.exp (4*u)).re) ≤ (1/8 : ℝ) := by
    rw [show -3*Real.pi*(Complex.exp (4*u)).re=-(3*Real.pi*(Complex.exp (4*u)).re) by ring,
      Real.exp_neg, ← div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    nlinarith
  have hl : 0 < ‖leading u‖ :=
    (by positivity : 0 < 3*Real.pi*Real.exp (9*u.re)*
      Real.exp (-Real.pi*(Complex.exp (4*u)).re)).trans_le (leading_norm_lower u ha)
  have h := relative_bound u ha (by linarith)
  intro hz
  rw [hz, zero_sub, norm_neg] at h
  have hm := mul_le_mul_of_nonneg_right hrho (norm_nonneg (leading u))
  nlinarith

theorem kernel_ne_zero_at_model_saddle (t x : ℝ) (u : ℂ) (ht : 0 ≤ t)
    (ha : 1 ≤ u.re) (hb : |u.im| ≤ 1/2)
    (hs : modelDerivative t u=-(Complex.I*(x : ℂ))) (hscale : 7 ≤ t*u.re^3) :
    kernelComplex u≠0 := by
  apply kernel_ne_zero u (by linarith)
  have h := saddle_real_lower t x u ht ha hb hs
  have hR : (16/(4*Real.pi) : ℝ) ≤ (Complex.exp (4*u)).re := by
    apply (div_le_iff₀ (by positivity : 0 < 4*Real.pi)).mpr
    nlinarith
  have h1 : (1 : ℝ) ≤ 16/(4*Real.pi) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*Real.pi)).mpr
    nlinarith [Real.pi_lt_four]
  exact h1.trans hR

end OperatorDerivativeRewrite.Foundation.RiemannThetaComplexKernel
