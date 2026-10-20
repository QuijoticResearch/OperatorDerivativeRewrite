import Foundation.RiemannEvenComplexWeight
import Foundation.RiemannEvenModelPhase
import Foundation.RiemannQuarticFarRightTail
/-! Common arithmetic-kernel envelopes for every integer-even tilt.
The model phase increment and frequency scale are kept explicit. -/
noncomputable section
open Set Metric Complex
namespace OperatorDerivativeRewrite.Foundation.RiemannEvenWeightEnvelope
open RiemannEvenComplexWeight RiemannEvenModelPhase RiemannThetaComplexKernel
open RiemannQuarticNaturalContour (kernel_norm_bound)
open RiemannThetaDerivativeBounds (kernel_norm_lower)

theorem actual_weight_model_envelope (m : ℕ) (t : ℝ) (z v u : ℂ)
    (hv : 0 ≤ v.re) (hEv : 1 ≤ (Complex.exp (4*v)).re)
    (hq : 0 ≤ (v+u).re) (hEq : 1/2 ≤ (Complex.exp (4*(v+u))).re) :
    ‖weight m t z (v+u)‖ ≤
      1000*‖weight m t z v‖*Real.exp (modelPhase m t (v+u)-modelPhase m t v+Complex.I*z*u).re := by
  let P := fun q : ℂ => (t : ℂ)*q^(2*m)+Complex.I*z*q+9*q-(Real.pi : ℂ)*Complex.exp (4*q)
  have hP (q : ℂ) : Real.exp (P q).re=
      Real.exp ((t : ℂ)*q^(2*m)+Complex.I*z*q).re *
        Real.exp (9*q.re)*Real.exp (-Real.pi*(Complex.exp (4*q)).re) := by
    have hid : (P q).re=((t : ℂ)*q^(2*m)+Complex.I*z*q).re+9*q.re+
        (-Real.pi*(Complex.exp (4*q)).re) := by
      dsimp [P]
      norm_num [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im]
      <;> ring
    rw [hid,Real.exp_add,Real.exp_add]
  have hupp := mul_le_mul_of_nonneg_left (kernel_norm_bound (v+u) hq hEq)
    (Real.exp_pos ((t : ℂ)*(v+u)^(2*m)+Complex.I*z*(v+u)).re).le
  have hlow := mul_le_mul_of_nonneg_left (kernel_norm_lower v hv hEv)
    (Real.exp_pos ((t : ℂ)*v^(2*m)+Complex.I*z*v).re).le
  have hnorm (q : ℂ) : ‖weight m t z q‖=
      Real.exp ((t : ℂ)*q^(2*m)+Complex.I*z*q).re*‖kernelComplex q‖ := by
    rw [weight,norm_mul,Complex.norm_exp]
  rw [← hnorm (v+u)] at hupp
  rw [← hnorm v] at hlow
  have hupp' : ‖weight m t z (v+u)‖ ≤ 5676*Real.exp (P (v+u)).re := by
    rw [hP]
    nlinarith
  have hlow' : (21/8 : ℝ)*Real.pi*Real.exp (P v).re ≤ ‖weight m t z v‖ := by
    rw [hP]
    nlinarith
  have hratio : 5676*Real.exp (P v).re ≤ 1000*‖weight m t z v‖ := by
    have hm := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (Real.exp_pos (P v).re).le
    nlinarith [Real.exp_pos (P v).re]
  have hid : P (v+u)=P v+(modelPhase m t (v+u)-modelPhase m t v+Complex.I*z*u) := by dsimp [P,modelPhase]; ring
  rw [hid,Complex.add_re,Real.exp_add] at hupp'
  have hm := mul_le_mul_of_nonneg_right hratio
    (Real.exp_pos (modelPhase m t (v+u)-modelPhase m t v+Complex.I*z*u).re).le
  nlinarith

theorem horizontal_exp_real_identity (v : ℂ) (s : ℝ) :
    (Complex.exp (4*(v+(s : ℂ)))).re=Real.exp (4*s)*(Complex.exp (4*v)).re := by
  have hid : Complex.exp (4*(v+(s : ℂ)))=(Real.exp (4*s) : ℂ)*Complex.exp (4*v) := by
    rw [Complex.ofReal_exp,← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hid]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

theorem model_frequency_exp_bound_complex (m : ℕ) (t : ℝ) (c : ℂ) (ht : 0 ≤ t) (hx : 0 < ‖c‖)
    (w : ℂ) (hp : (2*m : ℝ)*t*‖w‖^(2*m-1)+9 ≤ ‖c‖/2)
    (hs : modelDerivative m t w= -(Complex.I*c)) :
    ‖c‖ ≤ 32*Real.exp (4*w.re) := by
  have hn : ‖modelDerivative m t w‖=‖c‖ := by
    rw [hs]
    simp only [norm_neg,norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,one_mul]
  have htri := norm_sub_le (((2*m : ℕ) : ℂ)*(t : ℂ)*w^(2*m-1)+9)
    (4*(Real.pi : ℂ)*Complex.exp (4*w))
  have hadd := norm_add_le (((2*m : ℕ) : ℂ)*(t : ℂ)*w^(2*m-1)) (9 : ℂ)
  change ‖modelDerivative m t w‖ ≤ _ at htri
  rw [hn] at htri
  simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ht,abs_of_pos Real.pi_pos] at htri hadd
  have hnat : ‖((2*m : ℕ) : ℂ)‖ = (2*m : ℝ) := by simp
  rw [hnat] at hadd
  have hpi := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (norm_nonneg (Complex.exp (4*w)))
  have hE : ‖Complex.exp (4*w)‖=Real.exp (4*w.re) := by rw [Complex.norm_exp]; simp [Complex.mul_re]
  rw [hE] at htri hpi
  nlinarith

theorem model_frequency_exp_bound (m : ℕ) (t x : ℝ) (ht : 0 ≤ t) (hx : 0 < x)
    (w : ℂ) (hp : (2*m : ℝ)*t*‖w‖^(2*m-1)+9 ≤ x/2)
    (hs : modelDerivative m t w= -(Complex.I*(x : ℂ))) :
    x ≤ 32*Real.exp (4*w.re) := by
  have hn : ‖(x : ℂ)‖=x := by simp [abs_of_pos hx]
  simpa only [hn] using model_frequency_exp_bound_complex m t (x : ℂ) ht
    (by simpa only [hn] using hx) w (by simpa only [hn] using hp) hs

end OperatorDerivativeRewrite.Foundation.RiemannEvenWeightEnvelope
