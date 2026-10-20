import Foundation.RiemannSixthFarGaussianLocal
import Foundation.RiemannQuarticFarGaussianLimit
import Foundation.RiemannSixthFarAnalyticBranch
import Foundation.RiemannSixthUniformFarSaddles
/-! Uniform relative central Gaussian errors for actual A6 saddles.
The existing order-independent radius and numerical error budgets are reused. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthFarGaussianLimit
open RiemannSixthFarGaussianLocal RiemannSixthFarCorrection RiemannSixthFarRemainder
open RiemannEvenModelPhase RiemannEvenSaddleBranch RiemannEvenComplexWeight
open RiemannQuarticErrorLimits
open RiemannQuarticFarGaussianLimit (relativeBudget smallBudget central_relative_budget
  relativeBudget_tendsto_zero smallBudget_tendsto_zero)

private theorem polynomial_half (t x : ℝ) (ht : 0 ≤ t) (w : ℂ)
    (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x) : 6*t*‖w‖^5+9 ≤ x/2 := by
  have hpw := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 5
  have hm := mul_le_mul_of_nonneg_left hpw ht
  nlinarith [mul_nonneg ht (pow_nonneg (norm_nonneg w) 5)]

theorem arithmetic_error_frequency_bound (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x) (w : ℂ)
    (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ))) :
    30005*Real.exp (-4*w.re+4) ≤ 100000000/x := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 < x := by linarith
  have hpoly := polynomial_half t x ht0 w hp
  have hn : ‖modelDerivative 3 t w‖=x := by
    rw [hs]
    simp only [norm_neg,norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx0,one_mul]
  have htri := norm_sub_le (6*(t : ℂ)*w^5+9) (4*(Real.pi : ℂ)*Complex.exp (4*w))
  have hadd := norm_add_le (6*(t : ℂ)*w^5) (9 : ℂ)
  change ‖modelDerivative 3 t w‖ ≤ _ at htri
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
    (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ))) (hv : ‖v-w‖ ≤ 1/x) :
    x ≤ ‖-(deriv (modelDerivative 3 t) v)/2‖ ∧ ‖-(deriv (modelDerivative 3 t) v)/2‖ ≤ 4*x := by
  have hx0 : 0 < x := by linarith
  let A := -(4 : ℂ)*Complex.I*(x : ℂ)
  have hA : ‖A‖=4*x := by
    simp only [A,norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_I,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx0,mul_one]
  have hnear := model_deriv_near_far_saddle t x ht hx w v hp hs hv
  change ‖deriv (modelDerivative 3 t) v-A‖ ≤ x at hnear
  have hu := norm_add_le (deriv (modelDerivative 3 t) v-A) A
  rw [sub_add_cancel,hA] at hu
  have hl := norm_sub_le (deriv (modelDerivative 3 t) v) (deriv (modelDerivative 3 t) v-A)
  rw [sub_sub_cancel,hA] at hl
  rw [norm_div,norm_neg,Complex.norm_ofNat]
  constructor <;> linarith

theorem gaussian_normalization_lower (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x) (w v : ℂ)
    (hr : 4096 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ))) (hv : ‖v-w‖ ≤ 1/x) :
    1 ≤ 2*Real.sqrt x*‖∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)‖ := by
  have hx0 : 0 < x := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hp0 : 6*t*‖w‖^5+9 ≤ x := (polynomial_half t x ht0 w hp).trans (by linarith)
  let b := -(deriv (modelDerivative 3 t) v)/2
  have hb : 0 < b.re := model_gaussian_coefficient_pos t x ht (by linarith) w v hr hi hs hp0 hv
  have hn := (gaussian_coefficient_norm_bounds t x ht hx w v hp hs hv).2
  have hbne : b ≠ 0 := by intro h; simp [h] at hb
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hbne
  have hg := integral_gaussian_sq_complex hb
  have hfun : (fun s : ℝ => Complex.exp (-b*(s : ℂ)^2))=
      (fun s : ℝ => Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)) := by
    funext s
    congr 1
    dsimp [b]
    ring
  rw [hfun] at hg
  have hnorm := congrArg norm hg
  simp only [norm_pow,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos] at hnorm
  let g := ‖∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)‖
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
    (hr : 4096 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ))) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hstat : complexSlope 3 t v= -(Complex.I*z)) (r : ℝ) (hr0 : 0 < r) (hrr : r < 1/16)
    (hsmall : (30005*Real.exp (-4*w.re+4))*r+2048*x*r^3 ≤ 1) :
    ‖(∫ s : ℝ in -r..r, weight 3 t z (v+(s : ℂ)))/
      (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))-1‖ ≤
      2*Real.sqrt x*(16*(30005*Real.exp (-4*w.re+4))*r^2+8192*x*r^4+2/(x*r)) := by
  have hx0 : 0 < x := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hp0 : 6*t*‖w‖^5+9 ≤ x := (polynomial_half t x ht0 w hp).trans (by linarith)
  have he := actual_local_full_gaussian_error t x ht (by linarith) w v hr hi hs hp0 hv z hstat r hr0 hrr hsmall
  have hnormb := (gaussian_coefficient_norm_bounds t x ht hx w v hp hs hv).1
  have htail : 2/(‖-(deriv (modelDerivative 3 t) v)/2‖*r) ≤ 2/(x*r) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos hx0 hr0)
      (mul_le_mul_of_nonneg_right hnormb hr0.le)
  let W := weight 3 t z v
  let G := ∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)
  let L := ∫ s : ℝ in -r..r, weight 3 t z (v+(s : ℂ))
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


theorem central_relative_error_bound (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x) (w v : ℂ)
    (hr : 4096 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ))) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hstat : complexSlope 3 t v= -(Complex.I*z))
    (hrr : centralRadius x < 1/16) (hsmall : smallBudget x ≤ 1) :
    ‖(∫ s : ℝ in -(centralRadius x)..centralRadius x, weight 3 t z (v+(s : ℂ)))/
      (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))-1‖ ≤
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
      4096 ≤ w.re → |w.im| ≤ 1/2 → 10000*(t*(‖w‖+1)^5+1) ≤ x →
      modelDerivative 3 t w= -(Complex.I*(x : ℂ)) → ‖v-w‖ ≤ 1/x →
      ∀ z : ℂ, complexSlope 3 t v= -(Complex.I*z) →
      ‖(∫ s : ℝ in -(centralRadius x)..centralRadius x, weight 3 t z (v+(s : ℂ)))/
        (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))-1‖ ≤ η := by
  filter_upwards [eventually_ge_atTop (10000 : ℝ),
    centralRadius_tendsto_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/16)),
    smallBudget_tendsto_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1)),
    relativeBudget_tendsto_zero.eventually (gt_mem_nhds hη)] with x hx hr hsmall hηx
  intro t ht w v hrw hi hp hs hv z hstat
  exact (central_relative_error_bound t x ht hx w v hrw hi hp hs hv z hstat hr hsmall.le).trans hηx.le

theorem relative_limit_for_saddle_family (t : ℝ) (ht : 1 ≤ t) (w v z : ℝ → ℂ)
    (hdata : ∀ᶠ x : ℝ in atTop, 4096 ≤ (w x).re ∧ |(w x).im| ≤ 1/2 ∧
      10000*(t*(‖w x‖+1)^5+1) ≤ x ∧ modelDerivative 3 t (w x)= -(Complex.I*(x : ℂ)) ∧
      ‖v x-w x‖ ≤ 1/x ∧ complexSlope 3 t (v x)= -(Complex.I*z x)) :
    Tendsto (fun x : ℝ =>
      (∫ s : ℝ in -(centralRadius x)..centralRadius x, weight 3 t (z x) (v x+(s : ℂ)))/
        (weight 3 t (z x) (v x)*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) (v x)*(s : ℂ)^2/2))))
      atTop (nhds (1 : ℂ)) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  filter_upwards [eventually_uniform_local_gaussian_error (η/2) (by positivity),hdata]
    with x herror hdatax
  obtain ⟨hr,hi,hp,hs,hv,hstat⟩ := hdatax
  have h := herror t ht (w x) (v x) hr hi hp hs hv (z x) hstat
  have hlt := lt_of_le_of_lt h (by linarith : η/2 < η)
  simpa only [dist_eq_norm] using hlt

theorem exists_uniform_actual_central_gaussian :
    ∃ K : ℝ, 0 < K ∧ ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ t u x : ℝ,
      1 ≤ t → 120021 ≤ u → RiemannEvenRealSaddle.phaseSlope 3 t u = 0 →
      max X (K*RiemannQuarticTransitionSaddle.realScale u) ≤ x →
      ∃ w : ℂ, 10000 ≤ x ∧ 120020 ≤ w.re ∧ |w.im| ≤ 1/2 ∧
        10000*(t*(‖w‖+1)^5+1) ≤ x ∧ modelDerivative 3 t w = -(Complex.I*(x : ℂ)) ∧
        ∀ z : ℂ, ‖z-(x : ℂ)‖ ≤ 1 → ∃ v : ℂ,
          v ∈ closedBall w (1/x) ∧ complexSlope 3 t v = -(Complex.I*z) ∧
          1 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ weight 3 t z v ≠ 0 ∧
          weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)) ≠ 0 ∧
          ‖(∫ s : ℝ in -(centralRadius x)..centralRadius x, weight 3 t z (v+(s : ℂ)))/
            (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))-1‖ ≤ η := by
  obtain ⟨K,hK,hconstruct⟩ := RiemannSixthUniformFarSaddles.exists_uniform_actual_far_frequency_disks
  refine ⟨K,hK,?_⟩
  intro η hη
  obtain ⟨X,hX⟩ := eventually_atTop.mp (eventually_uniform_local_gaussian_error η hη)
  refine ⟨X,?_⟩
  intro t u x ht hu hstat hx
  have hxK := (le_max_right X (K*RiemannQuarticTransitionSaddle.realScale u)).trans hx
  have hxX := (le_max_left X (K*RiemannQuarticTransitionSaddle.realScale u)).trans hx
  obtain ⟨w,hxlarge,hr,hi,hp,hs,hroots⟩ := hconstruct t u x ht hu hstat hxK
  refine ⟨w,hxlarge,hr,hi,hp,hs,?_⟩
  intro z hz
  obtain ⟨v,⟨hv,hvstat⟩,_⟩ := hroots z hz
  have hd := RiemannSixthFarAnalyticBranch.corrected_saddle_geometry
    t x ht hxlarge w hr hi hp hs v hv
  have hvdist : ‖v-w‖ ≤ 1/x := by simpa only [mem_closedBall,dist_eq_norm] using hv
  have hn := gaussian_normalization_lower t x ht hxlarge w v (by linarith) hi hp hs hvdist
  have hG : (∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)) ≠ 0 := by
    intro h
    rw [h,norm_zero,mul_zero] at hn
    norm_num at hn
  have hW : weight 3 t z v ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) hd.2.2
  exact ⟨v,hv,hvstat,hd.1,hd.2.1,hW,mul_ne_zero hW hG,
    hX x hxX t ht w v (by linarith) hi hp hs hvdist z hvstat⟩

end OperatorDerivativeRewrite.Foundation.RiemannSixthFarGaussianLimit
