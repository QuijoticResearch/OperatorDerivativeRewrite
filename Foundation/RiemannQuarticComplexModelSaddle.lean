import Foundation.RiemannQuarticWeightedSlope
import Foundation.RiemannQuarticFarModelSaddle
/-! Complex-frequency model saddles for the quartic Xi transform.
These are constructed leading-model roots, not zeros of the Fourier transform.
In the lower frequency half-plane the real theta parameter gains -Im(z).
Actual saddle correction and dominant-channel estimates remain separate. -/
noncomputable section
open Set Metric Complex Filter
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticComplexModelSaddle
open RiemannQuarticSaddleTheta RiemannQuarticQuantitativeSaddle
open RiemannQuarticFarModelSaddle

theorem anchored_complex_saddle (t M : ℝ) (z : ℂ) (ht : 0 ≤ t) (hM : 1 ≤ M)
    (hx : 10000*(t+1)*M^3 ≤ ‖z‖) (b : ℂ) (hb : ‖b‖ ≤ M-1)
    (hanchor : 4*(Real.pi : ℂ)*Complex.exp (4*b)=Complex.I*z) :
    ∃! w, w ∈ closedBall b (1/1024) ∧ modelDerivative t w= -(Complex.I*z) := by
  have hM0 : 0 ≤ M := by linarith
  have hM3 : 1 ≤ M^3 := one_le_pow₀ hM
  have hM23 : M^2 ≤ M^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hM) (sq_nonneg M)]
  have htm : 0 ≤ t*M^3 := by positivity
  have hx0 : 0 < ‖z‖ := by nlinarith
  have hpoly : 12*t*M^2 ≤ ‖z‖ := by
    have h := mul_le_mul_of_nonneg_left hM23 ht
    nlinarith
  have hres : 4*t*M^3+9 ≤ ‖z‖/512 := by nlinarith
  let A := -(4 : ℂ)*Complex.I*z
  have hA : ‖A‖=4*‖z‖ := by
    simp only [A,norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_I,mul_one]
  have hAn : A ≠ 0 := norm_pos_iff.mp (by rw [hA]; positivity)
  have hdiff : ∀ w ∈ closedBall b (1/1024), DifferentiableAt ℂ (modelDerivative t) w :=
    fun w _ => (modelDerivative_hasDerivAt t w).differentiableAt
  have hbound : ∀ w ∈ closedBall b (1/1024), ‖deriv (modelDerivative t) w-A‖ ≤ ‖A‖/2 := by
    intro w hw
    have hd : ‖w-b‖ ≤ (1/1024 : ℝ) := by simpa only [mem_closedBall,dist_eq_norm] using hw
    have hnorm : ‖w‖ ≤ M := by
      have h := norm_add_le (w-b) b
      simp only [sub_add_cancel] at h
      linarith
    have he := Complex.norm_exp_sub_one_le (x := 4*(w-b)) (by
      rw [norm_mul,Complex.norm_ofNat]
      linarith : ‖4*(w-b)‖ ≤ 1)
    have hexp : ‖Complex.exp (4*(w-b))-1‖ ≤ (1/128 : ℝ) := by
      rw [norm_mul,Complex.norm_ofNat] at he
      linarith
    have heW : Complex.exp (4*w)=Complex.exp (4*b)*Complex.exp (4*(w-b)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have h16 : 16*(Real.pi : ℂ)*Complex.exp (4*w)=
        (4*Complex.I*z)*Complex.exp (4*(w-b)) := by
      calc
        _ = 4*(4*(Real.pi : ℂ)*Complex.exp (4*b))*Complex.exp (4*(w-b)) := by rw [heW]; ring
        _ = _ := by rw [hanchor]; ring
    have hid : deriv (modelDerivative t) w-A=
        12*(t : ℂ)*w^2-(4*Complex.I*z)*(Complex.exp (4*(w-b))-1) := by
      rw [(modelDerivative_hasDerivAt t w).deriv,h16]
      dsimp [A]
      ring
    rw [hid,hA]
    have hn := norm_sub_le (12*(t : ℂ)*w^2) ((4*Complex.I*z)*(Complex.exp (4*(w-b))-1))
    simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg ht,Complex.norm_I,mul_one] at hn
    have hp := pow_le_pow_left₀ (norm_nonneg w) hnorm 2
    have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 12*t)
    have hg := mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ 4*‖z‖)
    nlinarith
  have hc : modelDerivative t b=4*(t : ℂ)*b^3+9-Complex.I*z := by
    unfold modelDerivative
    rw [hanchor]
  have htarget : -(Complex.I*z) ∈ closedBall (modelDerivative t b) (‖A‖*(1/1024)/2) := by
    rw [mem_closedBall,dist_eq_norm,hc,hA]
    have he : -(Complex.I*z)-(4*(t : ℂ)*b^3+9-Complex.I*z)= -(4*(t : ℂ)*b^3+9) := by ring
    rw [he,norm_neg]
    have hn := norm_add_le (4*(t : ℂ)*b^3) (9 : ℂ)
    simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht] at hn
    have hp := pow_le_pow_left₀ (norm_nonneg b) (le_trans hb (by linarith : M-1 ≤ M)) 3
    have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 4*t)
    nlinarith
  obtain ⟨w,hw,hroot⟩ := scalar_ball_surj (modelDerivative t) b A (1/1024) (by norm_num) hAn hdiff hbound htarget
  refine ⟨w,⟨hw,hroot⟩,?_⟩
  intro v hv
  exact scalar_ball_injective (modelDerivative t) b A (1/1024) hAn hdiff hbound hv.1 hw (hv.2.trans hroot.symm)


theorem real_identity (t : ℝ) (z w : ℂ)
    (hs : modelDerivative t w = -(Complex.I*z)) :
    4*Real.pi*(Complex.exp (4*w)).re =
      4*t*(w.re^3-3*w.re*w.im^2)+9-z.im := by
  have h := congrArg Complex.re hs
  norm_num [modelDerivative, Complex.mul_re, cube_re] at h
  linarith

theorem real_margin (t : ℝ) (z w : ℂ) (ht : 0 ≤ t)
    (ha : 1 ≤ w.re) (hb : |w.im| ≤ 1/2)
    (hs : modelDerivative t w = -(Complex.I*z)) :
    t*w.re^3+9-z.im ≤ 4*Real.pi*(Complex.exp (4*w)).re := by
  have ha0 : 0 ≤ w.re := by linarith
  have ha2 : 1 ≤ w.re^2 := by nlinarith
  have ha3 : w.re ≤ w.re^3 := by
    have h := mul_le_mul_of_nonneg_left ha2 ha0
    nlinarith
  have hb2 : w.im^2 ≤ 1/4 := by
    rcases abs_le.mp hb with ⟨hlo,hhi⟩
    nlinarith [sq_nonneg w.im]
  have hp := mul_le_mul_of_nonneg_left hb2 ha0
  have hc : w.re^3 ≤ 4*(w.re^3-3*w.re*w.im^2) := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hc ht
  rw [real_identity t z w hs]
  nlinarith

theorem lower_half_plane_strip (t : ℝ) (z w : ℂ) (ht : 0 ≤ t)
    (hz : z.im ≤ 0) (ha : 1 ≤ w.re) (hb : |w.im| ≤ 1/2)
    (hs : modelDerivative t w = -(Complex.I*z)) :
    |w.im| < Real.pi/8 := by
  have hR := real_margin t z w ht ha hb hs
  have hpow : 0 ≤ t*w.re^3 := by positivity
  have hE : 0 < (Complex.exp (4*w)).re := by nlinarith [Real.pi_pos]
  have heq : (Complex.exp (4*w)).re=Real.exp (4*w.re)*Real.cos (4*w.im) := by
    simp [Complex.exp_re,Complex.mul_re,Complex.mul_im]
  rw [heq] at hE
  have hc : 0 < Real.cos (4*w.im) :=
    (mul_pos_iff_of_pos_left (Real.exp_pos (4*w.re))).mp hE
  have him : |4*w.im| ≤ 2 := by
    rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<4)]
    linarith
  have hlt : |4*w.im| < Real.pi/2 := by
    by_contra hn
    have hh := Real.cos_nonpos_of_pi_div_two_le_of_le (le_of_not_gt hn)
      (by linarith [Real.pi_gt_three] : |4*w.im| ≤ Real.pi+Real.pi/2)
    rw [Real.cos_abs] at hh
    linarith
  rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<4)] at hlt
  linarith

theorem kernel_ne_zero (t : ℝ) (z w : ℂ) (ht : 0 ≤ t)
    (ha : 1 ≤ w.re) (hb : |w.im| ≤ 1/2)
    (hs : modelDerivative t w = -(Complex.I*z))
    (hscale : 7 ≤ t*w.re^3-z.im) :
    RiemannThetaComplexKernel.kernelComplex w ≠ 0 := by
  apply RiemannThetaComplexKernel.kernel_ne_zero w (by linarith)
  have h := real_margin t z w ht ha hb hs
  have hR : (16/(4*Real.pi) : ℝ) ≤ (Complex.exp (4*w)).re := by
    apply (div_le_iff₀ (by positivity : 0 < 4*Real.pi)).mpr
    nlinarith
  have h1 : (1 : ℝ) ≤ 16/(4*Real.pi) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*Real.pi)).mpr
    nlinarith [Real.pi_lt_four]
  exact h1.trans hR

theorem theta_tail (t : ℝ) (z w : ℂ) (ht : 0 ≤ t)
    (hz : z.im ≤ 0) (ha : 1 ≤ w.re) (hb : |w.im| ≤ 1/2)
    (hs : modelDerivative t w = -(Complex.I*z)) (k : ℕ) (hk : k ≤ 4) :
    ‖complexThetaTail k 1 (Complex.exp (4*w))‖ ≤
      32*Real.exp (-(3/4 : ℝ)*(t*w.re^3+9-z.im))*
        ‖complexThetaTerm k (Complex.exp (4*w)) 0‖ := by
  have h := real_margin t z w ht ha hb hs
  have hpow : 0 ≤ t*w.re^3 := by positivity
  have hR : (9/(4*Real.pi) : ℝ) ≤ (Complex.exp (4*w)).re := by
    apply (div_le_iff₀ (by positivity : 0 < 4*Real.pi)).mpr
    nlinarith
  have hhalf : (1/2 : ℝ) ≤ 9/(4*Real.pi) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*Real.pi)).mpr
    nlinarith [Real.pi_lt_four]
  have hexp : Real.exp (-3*Real.pi*(Complex.exp (4*w)).re) ≤
      Real.exp (-(3/4 : ℝ)*(t*w.re^3+9-z.im)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact (complexThetaTail_relative k hk (Complex.exp (4*w)) (hhalf.trans hR)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (by norm_num)) (norm_nonneg _))

def complexAnchor (z : ℂ) : ℂ := Complex.log (Complex.I*z/(4*(Real.pi : ℂ)))/4

theorem complexAnchor_spec (z : ℂ) (hz : z ≠ 0) :
    4*(Real.pi : ℂ)*Complex.exp (4*complexAnchor z) = Complex.I*z := by
  have hp : (4*(Real.pi : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  have hq : Complex.I*z/(4*(Real.pi : ℂ)) ≠ 0 := div_ne_zero (mul_ne_zero Complex.I_ne_zero hz) hp
  rw [complexAnchor, show (4 : ℂ)*(Complex.log (Complex.I*z/(4*(Real.pi : ℂ)))/4) =
    Complex.log (Complex.I*z/(4*(Real.pi : ℂ))) by ring, Complex.exp_log hq]
  field_simp

theorem complexAnchor_geometry (a : ℝ) (ha : 0 ≤ a) (z : ℂ) (hz : z.im ≤ 0)
    (hn : ‖z‖ = 4*Real.pi*Real.exp (4*a)) :
    (complexAnchor z).re = a ∧ |(complexAnchor z).im| ≤ Real.pi/8 ∧
      ‖complexAnchor z‖ ≤ (a+2)-1 := by
  let q := Complex.I*z/(4*(Real.pi : ℂ))
  have hqn : ‖q‖ = Real.exp (4*a) := by
    simp only [q,norm_div,norm_mul,Complex.norm_I,one_mul,
      Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,hn]
    field_simp
  have hqre : 0 ≤ q.re := by
    dsimp [q]
    simp only [show (4 : ℂ)*(Real.pi : ℂ) = ((4*Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.div_ofReal_re,Complex.mul_re,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub]
    exact div_nonneg (neg_nonneg.mpr hz) (by positivity)
  have hi := Complex.abs_arg_le_pi_div_two_iff.mpr hqre
  have hr : (complexAnchor z).re = a := by
    simp only [complexAnchor,Complex.div_ofNat_re,Complex.log_re]
    change Real.log ‖q‖ / 4 = a
    rw [hqn,Real.log_exp]
    ring
  have him : |(complexAnchor z).im| ≤ Real.pi/8 := by
    simp only [complexAnchor,Complex.div_ofNat_im,Complex.log_im,abs_div,abs_of_pos (by norm_num : (0 : ℝ)<4)]
    change |q.arg|/4 ≤ Real.pi/8
    linarith
  refine ⟨hr,him,?_⟩
  have hb := Complex.norm_le_abs_re_add_abs_im (complexAnchor z)
  rw [hr,abs_of_nonneg ha] at hb
  linarith [Real.pi_lt_four]

theorem lower_half_circle_saddle (t a : ℝ) (ht : 0 ≤ t) (ha : 4 ≤ a)
    (hscale : 10000*(t+1)*(a+2)^3 ≤ 4*Real.pi*Real.exp (4*a))
    (z : ℂ) (hz : z.im ≤ 0) (hn : ‖z‖ = 4*Real.pi*Real.exp (4*a)) :
    ∃ w, w ∈ closedBall (complexAnchor z) (1/1024) ∧
      modelDerivative t w = -(Complex.I*z) ∧
      2 ≤ w.re ∧ |w.im| < Real.pi/8 ∧
      t*w.re^3+9-z.im ≤ 4*Real.pi*(Complex.exp (4*w)).re := by
  have hg := complexAnchor_geometry a (by linarith) z hz hn
  have hzn : z ≠ 0 := norm_pos_iff.mp (by rw [hn]; positivity)
  obtain ⟨w,hw,_⟩ := anchored_complex_saddle t (a+2) z ht (by linarith)
    (by rw [hn]; exact hscale) _ hg.2.2 (complexAnchor_spec z hzn)
  have hd : ‖w-complexAnchor z‖ ≤ (1/1024 : ℝ) := by
    simpa only [mem_closedBall,dist_eq_norm] using hw.1
  have hr := (Complex.abs_re_le_norm (w-complexAnchor z)).trans hd
  have hi := (Complex.abs_im_le_norm (w-complexAnchor z)).trans hd
  simp only [Complex.sub_re,Complex.sub_im] at hr hi
  have hwr : 2 ≤ w.re := by rw [hg.1] at hr; linarith [(abs_le.mp hr).1]
  have hwi : |w.im| ≤ 1/2 := by
    have hh := abs_add_le (w.im-(complexAnchor z).im) (complexAnchor z).im
    simp only [sub_add_cancel] at hh
    linarith [hg.2.1,Real.pi_lt_d2]
  exact ⟨w,hw.1,hw.2,hwr,lower_half_plane_strip t z w ht hz (by linarith) hwi hw.2,
    real_margin t z w ht (by linarith) hwi hw.2⟩

theorem eventually_lower_half_circles (t : ℝ) (ht : 0 ≤ t) :
    ∀ᶠ a : ℝ in atTop, ∀ z : ℂ, z.im ≤ 0 →
      ‖z‖ = 4*Real.pi*Real.exp (4*a) →
      ∃ w, w ∈ closedBall (complexAnchor z) (1/1024) ∧
        modelDerivative t w = -(Complex.I*z) ∧
        2 ≤ w.re ∧ |w.im| < Real.pi/8 ∧
        t*w.re^3+9-z.im ≤ 4*Real.pi*(Complex.exp (4*w)).re := by
  filter_upwards [RiemannQuarticDomain.quartic_exponent_dominated (80000*(t+1)) 0,
    eventually_ge_atTop (4 : ℝ)] with a hdom ha
  have ha0 : 0 ≤ a := by linarith
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ a+2) (by linarith : a+2 ≤ 2*a) 3
  have h34 : a^3 ≤ a^4 := by nlinarith [mul_nonneg (by linarith : 0 ≤ a-1) (pow_nonneg ha0 3)]
  have hM : (a+2)^3 ≤ 8*a^4 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ 10000*(t+1))
  simp only [zero_mul,add_zero] at hdom
  have hs : 10000*(t+1)*(a+2)^3 ≤ 4*Real.pi*Real.exp (4*a) := by
    nlinarith [Real.pi_gt_three,Real.exp_pos (4*a)]
  exact fun z hz hn => lower_half_circle_saddle t a ht ha hs z hz hn

theorem far_lower_half_plane (t : ℝ) (ht : 1 ≤ t) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R ≤ ‖z‖ → z.im ≤ 0 →
      ∃ w : ℂ, modelDerivative t w = -(Complex.I*z) ∧
        2 ≤ w.re ∧ |w.im| < Real.pi/8 ∧
        t*w.re^3+9-z.im ≤ 4*Real.pi*(Complex.exp (4*w)).re ∧
        RiemannThetaComplexKernel.kernelComplex w ≠ 0 ∧
        ∀ k : ℕ, k ≤ 4 → ‖complexThetaTail k 1 (Complex.exp (4*w))‖ ≤
          32*Real.exp (-(3/4 : ℝ)*(t*w.re^3+9-z.im))*
            ‖complexThetaTerm k (Complex.exp (4*w)) 0‖ := by
  have ht0 : 0 ≤ t := by linarith
  obtain ⟨A,hA⟩ := eventually_atTop.mp (eventually_lower_half_circles t ht0)
  let R := 4*Real.pi*Real.exp (4*A)
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨R,hR,?_⟩
  intro z hz him
  have hn0 : 0 < ‖z‖ := hR.trans_le hz
  let a := Real.log (‖z‖/(4*Real.pi))/4
  have hq : 0 < ‖z‖/(4*Real.pi) := by positivity
  have hn : ‖z‖ = 4*Real.pi*Real.exp (4*a) := by
    rw [show 4*a = Real.log (‖z‖/(4*Real.pi)) by dsimp [a]; ring,Real.exp_log hq]
    field_simp
  have hAa : A ≤ a := by
    have he : Real.exp (4*A) ≤ Real.exp (4*a) := by
      rw [hn] at hz
      change 4*Real.pi*Real.exp (4*A) ≤ 4*Real.pi*Real.exp (4*a) at hz
      exact (mul_le_mul_iff_right₀ (by positivity : 0 < 4*Real.pi)).mp hz
    have hh := Real.exp_le_exp.mp he
    linarith
  obtain ⟨w,hw,hs,hr,hi,hm⟩ := hA a hAa z him hn
  have hi' : |w.im| ≤ 1/2 := by linarith [Real.pi_lt_four]
  have hscale : 7 ≤ t*w.re^3-z.im := by
    have hc : (8 : ℝ) ≤ w.re^3 := by nlinarith [sq_nonneg (w.re-2),sq_nonneg w.re]
    have hm := mul_le_mul_of_nonneg_right ht (by positivity : 0 ≤ w.re^3)
    nlinarith
  exact ⟨w,hs,hr,hi,hm,kernel_ne_zero t z w ht0 (by linarith) hi' hs hscale,
    fun k hk => theta_tail t z w ht0 him (by linarith) hi' hs k hk⟩

end OperatorDerivativeRewrite.Foundation.RiemannQuarticComplexModelSaddle
