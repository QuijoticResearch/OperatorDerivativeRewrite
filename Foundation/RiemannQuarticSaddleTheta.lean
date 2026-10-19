import Foundation.RiemannThetaEffective
import Mathlib.Analysis.Complex.RealDeriv

/-! Complex theta tails near conditional saddles of the leading exponential
phase t*u^4 + 9*u - pi*exp(4*u). The model is not the full log(theta kernel).
Saddle existence, contour deformation and a bound for the full Fourier
remainder remain separate obligations. Every saddle estimate states its
stationarity and geometric hypotheses explicitly. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticSaddleTheta

def modelDerivative (t : ℝ) (z : ℂ) : ℂ :=
  4*(t : ℂ)*z^3+9-4*(Real.pi : ℂ)*Complex.exp (4*z)

def modelPhase (t : ℝ) (z : ℂ) : ℂ :=
  (t : ℂ)*z^4+9*z-(Real.pi : ℂ)*Complex.exp (4*z)

theorem modelPhase_hasDerivAt (t : ℝ) (z : ℂ) :
    HasDerivAt (modelPhase t) (modelDerivative t z) z := by
  have h := ((((hasDerivAt_id z).pow 4).const_mul (t : ℂ)).add
    ((hasDerivAt_id z).const_mul (9 : ℂ))).sub
    ((((hasDerivAt_id z).const_mul (4 : ℂ)).cexp).const_mul (Real.pi : ℂ))
  convert h using 1
  · funext w
    rfl
  · change 4*(t : ℂ)*z^3+9-4*(Real.pi : ℂ)*Complex.exp (4*z)=
      (t : ℂ)*(4*z^3*1)+9*1-(Real.pi : ℂ)*(Complex.exp (4*z)*(4*1))
    ring

theorem cube_re (z : ℂ) : (z^3).re=z.re^3-3*z.re*z.im^2 := by
  simp only [pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.mul_im]
  ring

theorem saddle_real_identity (t x : ℝ) (z : ℂ)
    (hs : modelDerivative t z=-(Complex.I*(x : ℂ))) :
    4*Real.pi*(Complex.exp (4*z)).re=4*t*(z.re^3-3*z.re*z.im^2)+9 := by
  have h := congrArg Complex.re hs
  norm_num [modelDerivative, Complex.mul_re, cube_re] at h
  linarith

theorem saddle_real_lower (t x : ℝ) (z : ℂ) (ht : 0 ≤ t)
    (ha : 1 ≤ z.re) (hb : |z.im| ≤ 1/2)
    (hs : modelDerivative t z=-(Complex.I*(x : ℂ))) :
    t*z.re^3+9 ≤ 4*Real.pi*(Complex.exp (4*z)).re := by
  have ha0 : 0 ≤ z.re := by linarith
  have ha2 : 1 ≤ z.re^2 := by nlinarith
  have ha3 : z.re ≤ z.re^3 := by
    have h := mul_le_mul_of_nonneg_left ha2 ha0
    nlinarith
  have hb2 : z.im^2 ≤ 1/4 := by
    rcases abs_le.mp hb with ⟨hlo,hhi⟩
    nlinarith [sq_nonneg z.im]
  have hp := mul_le_mul_of_nonneg_left hb2 ha0
  have hc : z.re^3 ≤ 4*(z.re^3-3*z.re*z.im^2) := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hc ht
  rw [saddle_real_identity t x z hs]
  nlinarith

open RiemannQuarticKernel

def complexThetaTerm (k : ℕ) (v : ℂ) (n : ℕ) : ℂ :=
  (((n+1 : ℕ) : ℝ)^k : ℂ)*
    Complex.exp (((-Real.pi*((n+1 : ℕ) : ℝ)^2 : ℝ) : ℂ)*v)

theorem norm_complexThetaTerm (k : ℕ) (v : ℂ) (n : ℕ) :
    ‖complexThetaTerm k v n‖=thetaTerm k v.re n := by
  unfold complexThetaTerm thetaTerm
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), Complex.norm_exp]
  congr 1 <;> simp [Complex.mul_re, pow_two]

def complexThetaTail (k N : ℕ) (v : ℂ) : ℂ :=
  ∑' n, complexThetaTerm k v (N+n)

theorem complexThetaTail_summable (k N : ℕ) (v : ℂ) (hv : 0 < v.re) :
    Summable (fun n => complexThetaTerm k v (N+n)) :=
  (RiemannThetaEffective.tail_summable k N v.re hv).of_norm_bounded
    (fun n => (norm_complexThetaTerm k v (N+n)).le)

theorem complexThetaTail_bound (k N : ℕ) (hk : k ≤ 4) (v : ℂ) (hv : 1/2 ≤ v.re) :
    ‖complexThetaTail k N v‖ ≤ 2*thetaTerm 4 v.re N := by
  have hs : Summable (fun n => ‖complexThetaTerm k v (N+n)‖) := by
    simp_rw [norm_complexThetaTerm]
    exact RiemannThetaEffective.tail_summable k N v.re (by linarith)
  calc
    _ ≤ ∑' n, ‖complexThetaTerm k v (N+n)‖ := norm_tsum_le_tsum_norm hs
    _ = RiemannThetaEffective.tail k N v.re := by simp only [norm_complexThetaTerm, RiemannThetaEffective.tail]
    _ ≤ _ := RiemannThetaEffective.tail_order_bound k N hk v.re hv

theorem complexThetaTail_relative (k : ℕ) (hk : k ≤ 4) (v : ℂ) (hv : 1/2 ≤ v.re) :
    ‖complexThetaTail k 1 v‖ ≤
      32*Real.exp (-3*Real.pi*v.re)*‖complexThetaTerm k v 0‖ := by
  have h := complexThetaTail_bound k 1 hk v hv
  have he : 2*thetaTerm 4 v.re 1=
      32*Real.exp (-3*Real.pi*v.re)*‖complexThetaTerm k v 0‖ := by
    rw [norm_complexThetaTerm]
    norm_num [thetaTerm]
    have he : Real.exp (-(Real.pi*4*v.re))=
        Real.exp (-(3*Real.pi*v.re))*Real.exp (-(Real.pi*v.re)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    ring
  exact h.trans_eq he

theorem saddle_theta_relative (t x : ℝ) (z : ℂ) (ht : 0 ≤ t)
    (ha : 1 ≤ z.re) (hb : |z.im| ≤ 1/2)
    (hs : modelDerivative t z=-(Complex.I*(x : ℂ))) (k : ℕ) (hk : k ≤ 4) :
    ‖complexThetaTail k 1 (Complex.exp (4*z))‖ ≤
      32*Real.exp (-(3/4 : ℝ)*(t*z.re^3+9))*
        ‖complexThetaTerm k (Complex.exp (4*z)) 0‖ := by
  have h := saddle_real_lower t x z ht ha hb hs
  have hpow : 0 ≤ t*z.re^3 := by positivity
  have hR : (9/(4*Real.pi) : ℝ) ≤ (Complex.exp (4*z)).re := by
    apply (div_le_iff₀ (by positivity : 0 < 4*Real.pi)).mpr
    nlinarith
  have hhalf : (1/2 : ℝ) ≤ 9/(4*Real.pi) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*Real.pi)).mpr
    nlinarith [Real.pi_lt_four]
  have hexp : Real.exp (-3*Real.pi*(Complex.exp (4*z)).re) ≤
      Real.exp (-(3/4 : ℝ)*(t*z.re^3+9)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact (complexThetaTail_relative k hk (Complex.exp (4*z)) (hhalf.trans hR)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (by norm_num)) (norm_nonneg _))

end OperatorDerivativeRewrite.Foundation.RiemannQuarticSaddleTheta
