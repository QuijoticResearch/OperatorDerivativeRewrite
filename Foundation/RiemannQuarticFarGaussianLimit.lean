import Foundation.RiemannQuarticFarGaussianLocal
import Foundation.RiemannQuarticErrorLimits
/-! Relative local Gaussian error budgets for actual far-frequency Xi saddles.
The established radius x^(-7/16) and its verified power limits are reused.
This does not bound actual complementary contour pieces or prove global zeros. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticFarGaussianLimit
open RiemannQuarticFarGaussianLocal RiemannQuarticFarCorrection RiemannQuarticFarRemainder
open RiemannQuarticFarModelSaddle RiemannQuarticSaddleTheta RiemannQuarticSaddleBranch
open RiemannQuarticFrequencyBranch RiemannQuarticErrorLimits

private theorem polynomial_half (t x : ℝ) (ht : 0 ≤ t) (w : ℂ)
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ x) : 4*t*‖w‖^3+9 ≤ x/2 := by
  have hpw := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hm := mul_le_mul_of_nonneg_left hpw ht
  nlinarith [mul_nonneg ht (pow_nonneg (norm_nonneg w) 3)]

theorem arithmetic_error_frequency_bound (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x) (w : ℂ)
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ x)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ))) :
    30005*Real.exp (-4*w.re+4) ≤ 100000000/x := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 < x := by linarith
  have hpoly := polynomial_half t x ht0 w hp
  have hn : ‖modelDerivative t w‖=x := by
    rw [hs]
    simp only [norm_neg,norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx0,one_mul]
  have htri := norm_sub_le (4*(t : ℂ)*w^3+9) (4*(Real.pi : ℂ)*Complex.exp (4*w))
  have hadd := norm_add_le (4*(t : ℂ)*w^3) (9 : ℂ)
  change ‖modelDerivative t w‖ ≤ _ at htri
  rw [hn] at htri
  simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ht0,abs_of_pos Real.pi_pos] at htri hadd
  have hpi := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (norm_nonneg (Complex.exp (4*w)))
  have hfreq : x ≤ 32*‖Complex.exp (4*w)‖ := by nlinarith
  have hE : ‖Complex.exp (4*w)‖=Real.exp (4*w.re) := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  rw [hE] at hfreq
  have hm := mul_le_mul_of_nonneg_right hfreq (Real.exp_pos (-4*w.re+4)).le
  have heq : Real.exp (4*w.re)*Real.exp (-4*w.re+4)=Real.exp 4 := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hpow := pow_le_pow_left₀ (Real.exp_pos (1 : ℝ)).le Real.exp_one_lt_three.le 4
  have hexp : Real.exp (4 : ℝ) ≤ 81 := by
    calc
      _ = (Real.exp (1 : ℝ))^4 := by simpa using Real.exp_nat_mul (1 : ℝ) 4
      _ ≤ 81 := hpow.trans (by norm_num)
  have heps : (30005*Real.exp (-4*w.re+4))*x ≤ 100000000 := by
    have hm' : x*Real.exp (-4*w.re+4) ≤ 32*Real.exp 4 := by nlinarith [heq]
    nlinarith
  exact (le_div_iff₀ hx0).mpr heps

theorem gaussian_coefficient_norm_bounds (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x) (w v : ℂ)
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ x)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ))) (hv : ‖v-w‖ ≤ 1/x) :
    x ≤ ‖-(deriv (modelDerivative t) v)/2‖ ∧ ‖-(deriv (modelDerivative t) v)/2‖ ≤ 4*x := by
  have hx0 : 0 < x := by linarith
  let A := -(4 : ℂ)*Complex.I*(x : ℂ)
  have hA : ‖A‖=4*x := by
    simp only [A,norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_I,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx0,mul_one]
  have hnear := model_deriv_near_far_saddle t x ht hx w v hp hs hv
  change ‖deriv (modelDerivative t) v-A‖ ≤ x at hnear
  have hu := norm_add_le (deriv (modelDerivative t) v-A) A
  rw [sub_add_cancel,hA] at hu
  have hl := norm_sub_le (deriv (modelDerivative t) v) (deriv (modelDerivative t) v-A)
  rw [sub_sub_cancel,hA] at hl
  rw [norm_div,norm_neg,Complex.norm_ofNat]
  constructor <;> linarith

theorem gaussian_normalization_lower (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ x)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ))) (hv : ‖v-w‖ ≤ 1/x) :
    1 ≤ 2*Real.sqrt x*‖∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)‖ := by
  have hx0 : 0 < x := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hp0 : 4*t*‖w‖^3+9 ≤ x := (polynomial_half t x ht0 w hp).trans (by linarith)
  let b := -(deriv (modelDerivative t) v)/2
  have hb : 0 < b.re := model_gaussian_coefficient_pos t x ht (by linarith) w v hr hi hs hp0 hv
  have hn := (gaussian_coefficient_norm_bounds t x ht hx w v hp hs hv).2
  have hbne : b ≠ 0 := by intro h; simp [h] at hb
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hbne
  have hg := integral_gaussian_sq_complex hb
  have hfun : (fun s : ℝ => Complex.exp (-b*(s : ℂ)^2))=
      (fun s : ℝ => Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)) := by
    funext s
    congr 1
    dsimp [b]
    ring
  rw [hfun] at hg
  have hnorm := congrArg norm hg
  simp only [norm_pow,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos] at hnorm
  let g := ‖∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)‖
  have hid : g^2*‖b‖=Real.pi := (eq_div_iff hbn.ne').mp hnorm
  have hm := mul_le_mul_of_nonneg_left hn (sq_nonneg g)
  have hroot := Real.sq_sqrt hx0.le
  have hprod : 0 ≤ 2*Real.sqrt x*g := by positivity
  have hsquare : 1 ≤ (2*Real.sqrt x*g)^2 := by
    calc
      _ ≤ Real.pi := by linarith [Real.pi_gt_three]
      _ ≤ g^2*(4*x) := by nlinarith [hid,hm]
      _ = _ := by rw [mul_pow,mul_pow,hroot]; ring
  change 1 ≤ 2*Real.sqrt x*g
  nlinarith


theorem relative_local_error_bound (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ x)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ))) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hstat : complexSlope t v= -(Complex.I*z)) (r : ℝ) (hr0 : 0 < r) (hrr : r < 1/16)
    (hsmall : (30005*Real.exp (-4*w.re+4))*r+2048*x*r^3 ≤ 1) :
    ‖(∫ s : ℝ in -r..r, saddleWeight t z (v+(s : ℂ)))/
      (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))-1‖ ≤
      2*Real.sqrt x*(16*(30005*Real.exp (-4*w.re+4))*r^2+8192*x*r^4+2/(x*r)) := by
  have hx0 : 0 < x := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hp0 : 4*t*‖w‖^3+9 ≤ x := (polynomial_half t x ht0 w hp).trans (by linarith)
  have he := actual_local_full_gaussian_error t x ht (by linarith) w v hr hi hs hp0 hv z hstat r hr0 hrr hsmall
  have hnormb := (gaussian_coefficient_norm_bounds t x ht hx w v hp hs hv).1
  have htail : 2/(‖-(deriv (modelDerivative t) v)/2‖*r) ≤ 2/(x*r) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos hx0 hr0)
      (mul_le_mul_of_nonneg_right hnormb hr0.le)
  let W := saddleWeight t z v
  let G := ∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)
  let L := ∫ s : ℝ in -r..r, saddleWeight t z (v+(s : ℂ))
  let B := 16*(30005*Real.exp (-4*w.re+4))*r^2+8192*x*r^4+2/(x*r)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hnum : ‖L-W*G‖ ≤ ‖W‖*B := by
    apply he.trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg W)
    dsimp [B]
    linarith
  have hnormal := gaussian_normalization_lower t x ht hx w v hr hi hp hs hv
  change 1 ≤ 2*Real.sqrt x*‖G‖ at hnormal
  have hG : G ≠ 0 := by intro h; norm_num [h] at hnormal
  have hd := horizontal_neighbor_domain t x ht (by linarith) w v (by linarith) hi hs hp0 hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hd
  have hW : W ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _)
    (RiemannThetaComplexKernel.kernel_ne_zero v hd.1 hd.2.1)
  have hden : W*G ≠ 0 := mul_ne_zero hW hG
  have hfrac : L/(W*G)-1=(L-W*G)/(W*G) := by field_simp
  change ‖L/(W*G)-1‖ ≤ _
  rw [hfrac,norm_div,norm_mul]
  apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hW) (norm_pos_iff.mpr hG))).mpr
  have hm := mul_le_mul_of_nonneg_left hnormal (mul_nonneg (norm_nonneg W) hB)
  change ‖L-W*G‖ ≤ (2*Real.sqrt x*B)*(‖W‖*‖G‖)
  nlinarith


def relativeBudget (x : ℝ) : ℝ :=
  3200000000*x^(-11/8 : ℝ)+16384*x^(-1/4 : ℝ)+4*x^(-1/16 : ℝ)

def smallBudget (x : ℝ) : ℝ :=
  (100000000/x)*centralRadius x+2048*x*centralRadius x^3

theorem arithmetic_scaled_radius (x : ℝ) (hx : 0 < x) :
    Real.sqrt x/x*centralRadius x^2=x^(-11/8 : ℝ) := by
  calc
    _ = x^(1/2 : ℝ)/x^(1 : ℝ)*x^((-7/16 : ℝ)*2) := by
      rw [Real.sqrt_eq_rpow,Real.rpow_one,centralRadius_pow x hx 2]
      norm_num
    _ = x^((1/2 : ℝ)-1)*x^((-7/16 : ℝ)*2) := by rw [Real.rpow_sub hx]
    _ = x^((1/2 : ℝ)-1+(-7/16)*2) := (Real.rpow_add hx _ _).symm
    _ = _ := by norm_num

theorem relativeBudget_tendsto_zero : Tendsto relativeBudget atTop (nhds 0) := by
  change Tendsto (fun x : ℝ => 3200000000*x^(-11/8 : ℝ)+16384*x^(-1/4 : ℝ)+4*x^(-1/16 : ℝ)) atTop (nhds 0)
  have h1 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<11/8)).const_mul (3200000000 : ℝ)
  have h2 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/4)).const_mul (16384 : ℝ)
  have h3 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/16)).const_mul (4 : ℝ)
  simpa only [relativeBudget,mul_zero,zero_add,neg_div] using (h1.add h2).add h3

theorem smallBudget_tendsto_zero : Tendsto smallBudget atTop (nhds 0) := by
  change Tendsto (fun x : ℝ => (100000000/x)*centralRadius x+2048*x*centralRadius x^3) atTop (nhds 0)
  have h1 : Tendsto (fun x : ℝ => (100000000/x)*centralRadius x) atTop (nhds 0) := by
    simpa only [zero_mul,id_eq] using (tendsto_const_nhds.div_atTop tendsto_id).mul centralRadius_tendsto_zero
  have h2 : Tendsto (fun x : ℝ => 2048*x*centralRadius x^3) atTop (nhds 0) := by
    have hp := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<5/16)).const_mul (2048 : ℝ)
    have hp0 : Tendsto (fun x : ℝ => 2048*x^(-5/16 : ℝ)) atTop (nhds 0) := by
      simpa only [mul_zero,neg_div] using hp
    apply hp0.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [mul_assoc,central_small_error x hx]
  simpa only [smallBudget,zero_add] using h1.add h2

theorem central_relative_budget (x : ℝ) (hx : 0 < x) :
    2*Real.sqrt x*(16*(100000000/x)*centralRadius x^2+8192*x*centralRadius x^4+
      2/(x*centralRadius x))=relativeBudget x := by
  have h1 := arithmetic_scaled_radius x hx
  have h2 := central_scaled_error x hx
  have h3 := gaussian_scaled_prefactor x hx
  dsimp [relativeBudget]
  calc
    _ = 3200000000*(Real.sqrt x/x*centralRadius x^2)+
        16384*(Real.sqrt x*x*centralRadius x^4)+4*(Real.sqrt x/(x*centralRadius x)) := by ring
    _ = _ := by rw [h1,h2,h3]


theorem central_relative_error_bound (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ x)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ))) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hstat : complexSlope t v= -(Complex.I*z))
    (hrr : centralRadius x < 1/16) (hsmall : smallBudget x ≤ 1) :
    ‖(∫ s : ℝ in -(centralRadius x)..centralRadius x, saddleWeight t z (v+(s : ℂ)))/
      (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))-1‖ ≤
      relativeBudget x := by
  have hx0 : 0 < x := by linarith
  have hrpos : 0 < centralRadius x := Real.rpow_pos_of_pos hx0 _
  have he := arithmetic_error_frequency_bound t x ht hx w hp hs
  have hm := mul_le_mul_of_nonneg_right he hrpos.le
  have hsm : (30005*Real.exp (-4*w.re+4))*centralRadius x+2048*x*centralRadius x^3 ≤ 1 := by
    change (100000000/x)*centralRadius x+2048*x*centralRadius x^3 ≤ 1 at hsmall
    linarith
  have hc := relative_local_error_bound t x ht hx w v hr hi hp hs hv z hstat
    (centralRadius x) hrpos hrr hsm
  apply hc.trans
  rw [← central_relative_budget x hx0]
  gcongr

theorem eventually_uniform_local_gaussian_error (η : ℝ) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, 1 ≤ t → ∀ w v : ℂ,
      64 ≤ w.re → |w.im| ≤ 1/2 → 100*(t*(‖w‖+1)^3+1) ≤ x →
      modelDerivative t w= -(Complex.I*(x : ℂ)) → ‖v-w‖ ≤ 1/x →
      ∀ z : ℂ, complexSlope t v= -(Complex.I*z) →
      ‖(∫ s : ℝ in -(centralRadius x)..centralRadius x, saddleWeight t z (v+(s : ℂ)))/
        (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))-1‖ ≤ η := by
  filter_upwards [eventually_ge_atTop (10000 : ℝ),
    centralRadius_tendsto_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/16)),
    smallBudget_tendsto_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1)),
    relativeBudget_tendsto_zero.eventually (gt_mem_nhds hη)] with x hx hr hsmall hηx
  intro t ht w v hrw hi hp hs hv z hstat
  exact (central_relative_error_bound t x ht hx w v hrw hi hp hs hv z hstat hr hsmall.le).trans hηx.le

theorem eventually_controlled_far_saddles (t : ℝ) (ht : 1 ≤ t) :
    ∀ᶠ x : ℝ in atTop, 10000 ≤ x ∧ ∃ w v : ℂ,
      120020 ≤ w.re ∧ |w.im| ≤ 1/2 ∧ 100*(t*(‖w‖+1)^3+1) ≤ x ∧
      modelDerivative t w= -(Complex.I*(x : ℂ)) ∧ ‖v-w‖ ≤ 1/x ∧
      complexSlope t v= -(Complex.I*(x : ℂ)) ∧
      1 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ RiemannThetaComplexKernel.kernelComplex v ≠ 0 := by
  have hlin : Tendsto (fun x : ℝ => x/(4*Real.pi)) atTop atTop :=
    tendsto_id.atTop_div_const (by positivity)
  have hlog := Real.tendsto_log_atTop.comp hlin
  have hlim := hlog.atTop_div_const (by norm_num : (0 : ℝ)<4)
  filter_upwards [eventually_frequency_actual_saddle t ht,
    hlim.eventually (RiemannQuarticDomain.quartic_exponent_dominated (80000*(t+1)) 0),
    hlim.eventually (eventually_ge_atTop (240040 : ℝ)),
    eventually_ge_atTop (10000 : ℝ)] with x hex hdom ha hx
  obtain ⟨w,v,hw,hs,hv,hroot,hg⟩ := hex
  let a := Real.log (x/(4*Real.pi))/4
  change w ∈ closedBall (anchor a) (1/1024) at hw
  change 240040 ≤ a at ha
  change 80000*(t+1)*a^4+0*a ≤ Real.pi*Real.exp (4*a)/2 at hdom
  have ha0 : 0 ≤ a := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hid : 4*Real.pi*Real.exp (4*a)=x := by
    dsimp [a]
    rw [show 4*(Real.log (x/(4*Real.pi))/4)=Real.log (x/(4*Real.pi)) by ring,
      Real.exp_log (by positivity : (0 : ℝ)<x/(4*Real.pi))]
    field_simp
  have hp3 := pow_le_pow_left₀ (by linarith : 0 ≤ a+3) (by linarith : a+3 ≤ 2*a) 3
  have hp34 : a^3 ≤ a^4 := by nlinarith [mul_nonneg (by linarith : 0 ≤ a-1) (pow_nonneg ha0 3)]
  have hM : (a+3)^3 ≤ 8*a^4 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ 10000*(t+1))
  simp only [zero_mul,add_zero] at hdom
  have hscale : 10000*(t+1)*(a+3)^3 ≤ x := by
    rw [← hid]
    nlinarith [Real.pi_gt_three,Real.exp_pos (4*a)]
  have hd : ‖w-anchor a‖ ≤ (1/1024 : ℝ) := by simpa only [mem_closedBall,dist_eq_norm] using hw
  have hreal := (Complex.abs_re_le_norm (w-anchor a)).trans hd
  have hbr : (anchor a).re=a := by simp [anchor]
  simp only [Complex.sub_re,hbr] at hreal
  have hr : 120020 ≤ w.re := by linarith [(abs_le.mp hreal).1]
  have hnorm : ‖w‖+1 ≤ a+3 := by
    have hn := norm_add_le (w-anchor a) (anchor a)
    rw [sub_add_cancel] at hn
    have hb := anchor_norm a ha0
    linarith
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ ‖w‖+1) hnorm 3
  have hps : 100*(t*(‖w‖+1)^3+1) ≤ x := by
    have hmul := mul_le_mul_of_nonneg_left hpow ht0
    nlinarith [pow_nonneg (by linarith : 0 ≤ a+3) 3]
  have hi := (far_saddle_geometry a (by linarith) w hw).2
  exact ⟨hx,w,v,hr,hi,hps,hs,(by simpa only [mem_closedBall,dist_eq_norm] using hv),hroot,hg⟩

theorem eventually_actual_local_gaussian (t : ℝ) (ht : 1 ≤ t) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∃ w v : ℂ,
      modelDerivative t w= -(Complex.I*(x : ℂ)) ∧ complexSlope t v= -(Complex.I*(x : ℂ)) ∧
      1 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ RiemannThetaComplexKernel.kernelComplex v ≠ 0 ∧
      ‖(∫ s : ℝ in -(centralRadius x)..centralRadius x, saddleWeight t (x : ℂ) (v+(s : ℂ)))/
        (saddleWeight t (x : ℂ) v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))-1‖ ≤ η := by
  filter_upwards [eventually_controlled_far_saddles t ht,eventually_uniform_local_gaussian_error η hη]
    with x hdata herror
  obtain ⟨hx,w,v,hr,hi,hp,hs,hv,hstat,hvre,hvim,hkn⟩ := hdata
  exact ⟨w,v,hs,hstat,hvre,hvim,hkn,herror t ht w v (by linarith) hi hp hs hv (x : ℂ) hstat⟩


theorem relative_limit_for_saddle_family (t : ℝ) (ht : 1 ≤ t) (w v z : ℝ → ℂ)
    (hdata : ∀ᶠ x : ℝ in atTop, 64 ≤ (w x).re ∧ |(w x).im| ≤ 1/2 ∧
      100*(t*(‖w x‖+1)^3+1) ≤ x ∧ modelDerivative t (w x)= -(Complex.I*(x : ℂ)) ∧
      ‖v x-w x‖ ≤ 1/x ∧ complexSlope t (v x)= -(Complex.I*z x)) :
    Tendsto (fun x : ℝ =>
      (∫ s : ℝ in -(centralRadius x)..centralRadius x, saddleWeight t (z x) (v x+(s : ℂ)))/
        (saddleWeight t (z x) (v x)*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) (v x)*(s : ℂ)^2/2))))
      atTop (nhds (1 : ℂ)) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  filter_upwards [eventually_uniform_local_gaussian_error (η/2) (by positivity),hdata]
    with x herror hdatax
  obtain ⟨hr,hi,hp,hs,hv,hstat⟩ := hdatax
  have h := herror t ht (w x) (v x) hr hi hp hs hv (z x) hstat
  have hlt := lt_of_le_of_lt h (by linarith : η/2 < η)
  simpa only [dist_eq_norm] using hlt

end OperatorDerivativeRewrite.Foundation.RiemannQuarticFarGaussianLimit
