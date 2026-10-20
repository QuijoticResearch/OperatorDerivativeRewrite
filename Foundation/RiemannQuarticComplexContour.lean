import Foundation.RiemannQuarticComplexCompactTail
import Foundation.RiemannQuarticFarHalfline
import Foundation.RiemannQuarticFarPairing
/-! Complementary actual horizontal contours at complex quartic saddles.
The stationary mismatch is retained. Existing generic kernel envelopes,
Gaussian tails and exact half-line splitting are reused. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticComplexContour
open RiemannQuarticSaddleTheta RiemannQuarticSaddleBranch RiemannQuarticFrequencyBranch
open RiemannThetaComplexKernel RiemannQuarticFarModelSaddle
open RiemannQuarticFarRightTail RiemannQuarticFarSignedIntegral RiemannQuarticNaturalContour
open RiemannQuarticFarHalfline RiemannQuarticComplexGaussian
open RiemannQuarticComplexAnnulus RiemannQuarticComplexCompactTail

theorem right_model_curvature (t : ℝ) (c₀ : ℂ) (hcenter : c₀.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c₀‖) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c₀))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c₀‖) (hv : ‖v-w‖ ≤ 1/‖c₀‖) (s : ℝ) (hs0 : 0 ≤ s) :
    (deriv (modelDerivative t) (v+(s : ℂ))).re ≤ -(t*w.re^3)/4 := by
  have hd := horizontal_neighbor_domain t c₀ hcenter ht hx w v (by linarith) hi hs hp hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hd
  have ht0 : 0 ≤ t := by linarith
  have hr0 : 0 ≤ w.re := by linarith
  have hv0 := hd.1
  have hvr : v.re ≤ w.re+1 := by linarith [(abs_le.mp hd.2.2.2).2]
  have he : 1+s ≤ Real.exp s := by linarith [Real.add_one_le_exp s]
  have he0 : 1 ≤ Real.exp s := Real.one_le_exp hs0
  have hq : v.re+s ≤ (w.re+1)*Real.exp s := by
    have hm := mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ w.re+1)
    nlinarith
  have hq0 : 0 ≤ v.re+s := by linarith
  have hsq := pow_le_pow_left₀ hq0 hq 2
  have he2 : (Real.exp s)^2=Real.exp (2*s) := by simpa using (Real.exp_nat_mul s 2).symm
  rw [mul_pow,he2] at hsq
  have hw2 : (w.re+1)^2 ≤ 2*w.re^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hw2 (Real.exp_pos (2*s)).le
  have hq2 : (v.re+s)^2 ≤ 2*w.re^2*Real.exp (2*s) := hsq.trans hm
  have hpow : 64*w.re^2 ≤ w.re^3 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ w.re-64) (sq_nonneg w.re)]
  have hpoly : 12*t*(v.re+s)^2 ≤ (3/8 : ℝ)*t*w.re^3*Real.exp (2*s) := by
    have hm1 := mul_le_mul_of_nonneg_left hq2 (by positivity : 0 ≤ 12*t)
    have hm2 := mul_le_mul_of_nonneg_right hpow (by positivity : 0 ≤ t*Real.exp (2*s))
    nlinarith
  have hEid : (Complex.exp (4*(v+(s : ℂ)))).re=Real.exp (4*s)*(Complex.exp (4*v)).re := by
    have hid : Complex.exp (4*(v+(s : ℂ)))=(Real.exp (4*s) : ℂ)*Complex.exp (4*v) := by
      rw [Complex.ofReal_exp,← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hid]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hElow := mul_le_mul_of_nonneg_left hd.2.2.1 (Real.exp_pos (4*s)).le
  rw [← hEid] at hElow
  have hE0 : 0 ≤ (Complex.exp (4*(v+(s : ℂ)))).re := by
    rw [hEid]
    exact mul_nonneg (Real.exp_pos _).le (by linarith [hd.2.1])
  have hpi := mul_le_mul_of_nonneg_right Real.pi_gt_three.le hE0
  have hexp : Real.exp (2*s) ≤ Real.exp (4*s) := Real.exp_le_exp.mpr (by linarith)
  have hexp1 : 1 ≤ Real.exp (4*s) := Real.one_le_exp (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ (3/8 : ℝ)*t*w.re^3)
  have hmul1 := mul_le_mul_of_nonneg_left hexp1 (by positivity : 0 ≤ t*w.re^3/4)
  have hid : (deriv (modelDerivative t) (v+(s : ℂ))).re=
      12*t*((v.re+s)^2-v.im^2)-16*Real.pi*(Complex.exp (4*(v+(s : ℂ)))).re := by
    rw [(modelDerivative_hasDerivAt t _).deriv]
    simp [pow_two,Complex.sub_re,Complex.mul_re,Complex.mul_im]
  rw [hid]
  nlinarith [hEid,hd.2.2.1,mul_nonneg ht0 (sq_nonneg v.im)]




theorem right_phase_quadratic_bound (t : ℝ) (c₀ : ℂ) (hcenter : c₀.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c₀‖) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c₀))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c₀‖) (hv : ‖v-w‖ ≤ 1/‖c₀‖)
    (z : ℂ) (hz : complexSlope t v= -(Complex.I*z)) (s : ℝ) (hs0 : 0 ≤ s) :
    (leadingPhase t z v (s : ℂ)).re ≤
      (30005*Real.exp (-4*w.re+4))*s-(t*w.re^3/8)*s^2 := by
  let c := t*w.re^3/8
  let f := fun a : ℝ => (leadingPhase t z v (a : ℂ)).re+c*a^2
  let f1 := fun a : ℝ => (modelDerivative t (v+(a : ℂ))+Complex.I*z).re+2*c*a
  let f2 := fun a : ℝ => (deriv (modelDerivative t) (v+(a : ℂ))).re+2*c
  have h1 (a : ℝ) : HasDerivAt f (f1 a) a := by
    have hd := ((leadingPhase_hasDerivAt t z v (a : ℂ)).real_of_complex).add
      (((hasDerivAt_id a).pow 2).const_mul c)
    convert hd using 1
    · funext y; rfl
    · dsimp [f1]
      ring
  have h2 (a : ℝ) : HasDerivAt f1 (f2 a) a := by
    have hm := modelDerivative_hasDerivAt t (v+(a : ℂ))
    have hc := (hm.comp (a : ℂ) ((hasDerivAt_id (a : ℂ)).const_add v)).add_const (Complex.I*z)
    have hc' : HasDerivAt (fun u : ℂ => modelDerivative t (v+u)+Complex.I*z)
        (deriv (modelDerivative t) (v+(a : ℂ))) (a : ℂ) := by
      convert hc using 1 <;> first | rfl | simp only [hm.deriv,mul_one]
    have hd := hc'.real_of_complex.add ((hasDerivAt_id a).const_mul (2*c))
    convert hd using 1
    · funext y; rfl
    · dsimp [f2]
      ring
  have hf0 : f 0=0 := by simp [f,leadingPhase_zero]
  have hc : ConcaveOn ℝ (Ici (0 : ℝ)) f := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := f1) (f'' := f2)
      (convex_Ici _) (fun a _ => (h1 a).continuousAt.continuousWithinAt)
      (fun a _ => (h1 a).hasDerivWithinAt) (fun a _ => (h2 a).hasDerivWithinAt)
    intro a ha
    have ha0 : 0 ≤ a := interior_subset ha
    have h := right_model_curvature t c₀ hcenter ht hx w v hr hi hs hp hv a ha0
    dsimp [f2,c]
    linarith
  have htangent : f s ≤ f1 0*s := by
    rcases eq_or_lt_of_le hs0 with heq | hpos
    · subst s
      simp [hf0]
    · have h := hc.slope_le_of_hasDerivAt (show (0 : ℝ) ∈ Ici (0 : ℝ) from by simp) hs0 hpos (h1 0)
      rw [slope_def_field,hf0,sub_zero,sub_zero] at h
      exact (div_le_iff₀ hpos).mp h
  have he := horizontal_neighbor_error t c₀ hcenter ht hx w v (by linarith) hi hs hp hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at he
  have hid : f1 0= -(complexSlope t v-modelDerivative t v).re := by
    have hid : modelDerivative t v+Complex.I*z= -(complexSlope t v-modelDerivative t v) := by rw [hz]; ring
    simp only [f1,Complex.ofReal_zero,add_zero,mul_zero,hid,Complex.neg_re]
  have hf1 : f1 0 ≤ 30005*Real.exp (-4*w.re+4) := by
    rw [hid]
    exact (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans he)
  have hm := mul_le_mul_of_nonneg_right hf1 hs0
  dsimp [f,c] at htangent
  linarith



private theorem horizontal_exp_identity (v : ℂ) (s : ℝ) :
    (Complex.exp (4*(v+(s : ℂ)))).re=Real.exp (4*s)*(Complex.exp (4*v)).re := by
  have hid : Complex.exp (4*(v+(s : ℂ)))=(Real.exp (4*s) : ℂ)*Complex.exp (4*v) := by
    rw [Complex.ofReal_exp,← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hid]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]



theorem actual_right_gaussian_envelope (t : ℝ) (c₀ : ℂ) (hcenter : c₀.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c₀‖) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c₀))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c₀‖) (hv : ‖v-w‖ ≤ 1/‖c₀‖)
    (z : ℂ) (hz : complexSlope t v= -(Complex.I*z))
    (R : ℝ) (hR : 0 < R) (hsmall : 30005*Real.exp (-4*w.re+4) ≤ (t*w.re^3/16)*R)
    (s : ℝ) (hsR : R ≤ s) :
    ‖saddleWeight t z (v+(s : ℂ))‖ ≤
      1000*‖saddleWeight t z v‖*Real.exp (-(t*w.re^3/16)*s^2) := by
  have hs0 : 0 ≤ s := hR.le.trans hsR
  have hd := horizontal_neighbor_domain t c₀ hcenter ht hx w v (by linarith) hi hs hp hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hd
  have hE : 1 ≤ (Complex.exp (4*(v+(s : ℂ)))).re := by
    rw [horizontal_exp_identity]
    have he : 1 ≤ Real.exp (4*s) := Real.one_le_exp (by linarith)
    nlinarith [hd.2.1]
  have hratio := actual_weight_model_envelope t z v (s : ℂ) hd.1 hd.2.1
    (by simp only [Complex.add_re,Complex.ofReal_re]; linarith [hd.1]) (by linarith)
  have hphase := right_phase_quadratic_bound t c₀ hcenter ht hx w v hr hi hs hp hv z hz s hs0
  have hc : 0 ≤ t*w.re^3/16 := by positivity
  have hm := mul_le_mul_of_nonneg_left hsR hc
  have hm2 := mul_le_mul_of_nonneg_right hsmall hs0
  have hm3 := mul_le_mul_of_nonneg_right hm hs0
  have hexp : (leadingPhase t z v (s : ℂ)).re ≤ -(t*w.re^3/16)*s^2 := by nlinarith
  exact hratio.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity))




theorem actual_right_tail_bound (t : ℝ) (c₀ : ℂ) (hcenter : c₀.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c₀‖) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c₀))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c₀‖) (hv : ‖v-w‖ ≤ 1/‖c₀‖)
    (z : ℂ) (hz : complexSlope t v= -(Complex.I*z))
    (R : ℝ) (hR : 0 < R) (hsmall : 30005*Real.exp (-4*w.re+4) ≤ (t*w.re^3/16)*R) :
    IntegrableOn (fun s : ℝ => saddleWeight t z (v+(s : ℂ))) (Ioi R) ∧
    ‖∫ s : ℝ in Ioi R, saddleWeight t z (v+(s : ℂ))‖ ≤
      1000*‖saddleWeight t z v‖*Real.exp (-(t*w.re^3/16)*R^2)/(2*(t*w.re^3/16)*R) := by
  let c := t*w.re^3/16
  let A := 1000*‖saddleWeight t z v‖
  let f := fun s : ℝ => saddleWeight t z (v+(s : ℂ))
  have hc : 0 < c := by dsimp [c]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hg : IntegrableOn (fun s : ℝ => A*Real.exp (-c*s^2)) (Ioi R) :=
    ((integrable_exp_neg_mul_sq hc).const_mul A).integrableOn
  have hbound (s : ℝ) (hsR : s ∈ Ioi R) : ‖f s‖ ≤ A*Real.exp (-c*s^2) :=
    actual_right_gaussian_envelope t c₀ hcenter ht hx w v hr hi hs hp hv z hz R hR hsmall s hsR.le
  have hd := horizontal_neighbor_domain t c₀ hcenter ht hx w v (by linarith) hi hs hp hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hd
  have hfc : ContinuousOn f (Ioi R) := by
    intro s hsR
    have hE : 0 < (Complex.exp (4*(v+(s : ℂ)))).re := by
      rw [horizontal_exp_identity]
      exact mul_pos (Real.exp_pos _) (by linarith [hd.2.1])
    have hk := kernelComplex_analyticAt (v+(s : ℂ)) hE
    have hw : AnalyticAt ℂ (saddleWeight t z) (v+(s : ℂ)) := by
      unfold saddleWeight
      apply AnalyticAt.mul
      · fun_prop
      · exact hk
    have hc' : ContinuousAt f s := ContinuousAt.comp (g := saddleWeight t z)
      (f := fun a : ℝ => v+(a : ℂ)) hw.continuousAt (by fun_prop)
    exact hc'.continuousWithinAt
  have hf : IntegrableOn f (Ioi R) := by
    apply hg.mono' (hfc.aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hsR
    exact hbound s hsR
  refine ⟨hf,?_⟩
  calc
    ‖∫ s : ℝ in Ioi R, f s‖ ≤ ∫ s : ℝ in Ioi R, ‖f s‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ s : ℝ in Ioi R, A*Real.exp (-c*s^2) :=
      setIntegral_mono_on hf.norm hg measurableSet_Ioi hbound
    _ = A*(∫ s : ℝ in Ioi R, Real.exp (-c*s^2)) := integral_const_mul _ _
    _ ≤ A*(Real.exp (-c*R^2)/(2*c*R)) :=
      mul_le_mul_of_nonneg_left (RiemannQuarticGaussianTail.real_tail_bound c R hc hR) hA
    _ = _ := by dsimp [A,c]; ring



theorem relative_actual_right_tail_bound (t : ℝ) (c₀ : ℂ) (hcenter : c₀.im ≤ 0) (ht : 1 ≤ t) (hx : 10000 ≤ ‖c₀‖)
    (w v : ℂ) (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c₀))
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ ‖c₀‖) (hv : ‖v-w‖ ≤ 1/‖c₀‖)
    (z : ℂ) (hz : complexSlope t v= -(Complex.I*z))
    (R : ℝ) (hR : 0 < R) (hsmall : 30005*Real.exp (-4*w.re+4) ≤ (t*w.re^3/16)*R) :
    ‖(∫ s : ℝ in Ioi R, saddleWeight t z (v+(s : ℂ)))/
      (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤
      2000*Real.sqrt ‖c₀‖*Real.exp (-(t*w.re^3/16)*R^2)/(2*(t*w.re^3/16)*R) := by
  have ht0 : 0 ≤ t := by linarith
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hmul := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 4*t*‖w‖^3+9 ≤ ‖c₀‖ := by nlinarith [pow_nonneg (norm_nonneg w) 3]
  have he := (actual_right_tail_bound t c₀ hcenter ht (by linarith) w v hr hi hs hp0 hv z hz R hR hsmall).2
  let W := saddleWeight t z v
  let G := ∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)
  let B := 1000*Real.exp (-(t*w.re^3/16)*R^2)/(2*(t*w.re^3/16)*R)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hnormal := gaussian_normalization_lower t c₀ hcenter ht hx w v hr hi hp hs hv
  change 1 ≤ 2*Real.sqrt ‖c₀‖*‖G‖ at hnormal
  have hG : G ≠ 0 := by intro h; norm_num [h] at hnormal
  have hd := horizontal_neighbor_domain t c₀ hcenter ht (by linarith) w v (by linarith) hi hs hp0 hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hd
  have hW : W ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (kernel_ne_zero v hd.1 hd.2.1)
  have hnum : ‖∫ s : ℝ in Ioi R, saddleWeight t z (v+(s : ℂ))‖ ≤ ‖W‖*B := by
    apply he.trans_eq
    dsimp [W,B]
    ring
  have htarget : 2000*Real.sqrt ‖c₀‖*Real.exp (-(t*w.re^3/16)*R^2)/(2*(t*w.re^3/16)*R)=2*Real.sqrt ‖c₀‖*B := by
    dsimp [B]
    ring
  rw [htarget]
  change ‖(∫ s : ℝ in Ioi R, saddleWeight t z (v+(s : ℂ)))/(W*G)‖ ≤ _
  rw [norm_div,norm_mul]
  apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hW) (norm_pos_iff.mpr hG))).mpr
  have hm := mul_le_mul_of_nonneg_left hnormal (mul_nonneg (norm_nonneg W) hB)
  nlinarith




private theorem model_frequency_exp_bound (t : ℝ) (c₀ : ℂ) (hcenter : c₀.im ≤ 0) (ht : 1 ≤ t) (hx : 10000 ≤ ‖c₀‖)
    (w : ℂ) (hp : 100*(t*(‖w‖+1)^3+1) ≤ ‖c₀‖)
    (hs : modelDerivative t w= -(Complex.I*c₀)) :
    ‖c₀‖ ≤ 32*Real.exp (4*w.re) := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 < ‖c₀‖ := by linarith
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hm := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 4*t*‖w‖^3+9 ≤ ‖c₀‖/2 := by nlinarith [pow_nonneg (norm_nonneg w) 3]
  have hn : ‖modelDerivative t w‖=‖c₀‖ := by
    rw [hs]
    simp only [norm_neg,norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,one_mul]
  have htri := norm_sub_le (4*(t : ℂ)*w^3+9) (4*(Real.pi : ℂ)*Complex.exp (4*w))
  have hadd := norm_add_le (4*(t : ℂ)*w^3) (9 : ℂ)
  change ‖modelDerivative t w‖ ≤ _ at htri
  rw [hn] at htri
  simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ht0,abs_of_pos Real.pi_pos] at htri hadd
  have hpi := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (norm_nonneg (Complex.exp (4*w)))
  have hE : ‖Complex.exp (4*w)‖=Real.exp (4*w.re) := by rw [Complex.norm_exp]; simp [Complex.mul_re]
  rw [hE] at htri hpi
  nlinarith



theorem relative_right_tail_budget (t : ℝ) (c₀ : ℂ) (hcenter : c₀.im ≤ 0) (ht : 1 ≤ t) (hx : 10000 ≤ ‖c₀‖)
    (w v : ℂ) (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c₀))
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ ‖c₀‖) (hv : ‖v-w‖ ≤ 1/‖c₀‖)
    (z : ℂ) (hz : complexSlope t v= -(Complex.I*z))
    (R : ℝ) (hR : 0 < R) (hsmall : 30005*Real.exp (-4*w.re+4) ≤ (t*w.re^3/16)*R) :
    ‖(∫ s : ℝ in Ioi R, saddleWeight t z (v+(s : ℂ)))/
      (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤
      rightBudget R w.re := by
  have h := relative_actual_right_tail_bound t c₀ hcenter ht hx w v hr hi hs hp hv z hz R hR hsmall
  have hx0 : 0 < ‖c₀‖ := by linarith
  have hfreq := model_frequency_exp_bound t c₀ hcenter ht hx w hp hs
  have hsqrt : Real.sqrt ‖c₀‖ ≤ 8*Real.exp (2*w.re) := by
    have hsq := Real.sq_sqrt hx0.le
    have hE : (Real.exp (2*w.re))^2=Real.exp (4*w.re) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    nlinarith [Real.sqrt_nonneg ‖c₀‖,Real.exp_pos (2*w.re),Real.exp_pos (4*w.re)]
  have hw3 : 16 ≤ w.re^3 := by
    have hw2 : 1 ≤ w.re^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hw2 (by linarith : 0 ≤ w.re)]
  have hwt : w.re^3 ≤ t*w.re^3 := by nlinarith
  have hc : 1 ≤ t*w.re^3/16 := by linarith
  have hden : R ≤ 2*(t*w.re^3/16)*R := by nlinarith
  have hpow := mul_le_mul_of_nonneg_right hwt (sq_nonneg R)
  have he : Real.exp (-(t*w.re^3/16)*R^2) ≤ Real.exp (-(w.re^3/16)*R^2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  apply h.trans
  calc
    _ ≤ (2000*Real.sqrt ‖c₀‖*Real.exp (-(t*w.re^3/16)*R^2))/R :=
      div_le_div_of_nonneg_left (by positivity) hR hden
    _ ≤ (2000*(8*Real.exp (2*w.re))*Real.exp (-(w.re^3/16)*R^2))/R := by
      apply div_le_div_of_nonneg_right _ hR.le
      exact mul_le_mul (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) he (by positivity) (by positivity)
    _ = rightBudget R w.re := by
      dsimp [rightBudget]
      rw [show 2*w.re-(R^2/16)*w.re^3=2*w.re+(-(w.re^3/16)*R^2) by ring,Real.exp_add]
      ring



theorem left_unit_domain_curvature (t : ℝ) (c₀ : ℂ) (hcenter : c₀.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c₀‖) (w v : ℂ)
    (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c₀))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c₀‖) (hv : ‖v-w‖ ≤ 1/‖c₀‖)
    (s : ℝ) (hs1 : -1 ≤ s) (hs0 : s ≤ 0) :
    0 ≤ (v+(s : ℂ)).re ∧ 1 ≤ (Complex.exp (4*(v+(s : ℂ)))).re ∧
      (deriv (modelDerivative t) (v+(s : ℂ))).re ≤ -(t*w.re^3)/1024 := by
  have hd := horizontal_neighbor_domain t c₀ hcenter ht hx w v (by linarith) hi hs hp hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hd
  have ht0 : 0 ≤ t := by linarith
  have hw0 : 0 ≤ w.re := by linarith
  have hq0 : 0 ≤ (v+(s : ℂ)).re := by
    simp only [Complex.add_re,Complex.ofReal_re]
    linarith [(abs_le.mp hd.2.2.2).1]
  have hq : (v+(s : ℂ)).re ≤ w.re+1 := by
    simp only [Complex.add_re,Complex.ofReal_re]
    linarith [(abs_le.mp hd.2.2.2).2]
  have hsq := pow_le_pow_left₀ hq0 hq 2
  have hq2 : (v+(s : ℂ)).re^2 ≤ 2*w.re^2 := by nlinarith
  have he4 : Real.exp (4 : ℝ) ≤ 81 := by
    calc
      _ = Real.exp (1 : ℝ)^4 := by simpa using Real.exp_nat_mul (1 : ℝ) 4
      _ ≤ 3^4 := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le 4
      _ = _ := by norm_num
  have hmul := mul_le_mul_of_nonneg_right he4 (Real.exp_pos (-4 : ℝ)).le
  have heid : Real.exp (4 : ℝ)*Real.exp (-4 : ℝ)=1 := by rw [← Real.exp_add]; norm_num
  rw [heid] at hmul
  have hes : (1/81 : ℝ) ≤ Real.exp (4*s) := by
    have he := Real.exp_le_exp.mpr (by linarith : (-4 : ℝ) ≤ 4*s)
    linarith
  have hEid : (Complex.exp (4*(v+(s : ℂ)))).re=Real.exp (4*s)*(Complex.exp (4*v)).re := by
    have hid : Complex.exp (4*(v+(s : ℂ)))=(Real.exp (4*s) : ℂ)*Complex.exp (4*v) := by
      rw [Complex.ofReal_exp,← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hid]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have heprod := mul_le_mul hes hd.2.2.1 (by positivity : 0 ≤ t*w.re^3/64) (Real.exp_pos _).le
  have hElow : t*w.re^3/5184 ≤ (Complex.exp (4*(v+(s : ℂ)))).re := by rw [hEid]; nlinarith
  have hw3 : 5184 ≤ w.re^3 := by
    have hw2 : 1 ≤ w.re^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hw2 hw0]
  have hwt : w.re^3 ≤ t*w.re^3 := by nlinarith
  have hE1 : 1 ≤ (Complex.exp (4*(v+(s : ℂ)))).re := by linarith
  refine ⟨hq0,hE1,?_⟩
  have hcub : 5184*w.re^2 ≤ w.re^3 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ w.re-5184) (sq_nonneg w.re)]
  have hpoly : 12*t*(v+(s : ℂ)).re^2 ≤ t*w.re^3/216 := by
    have hm1 := mul_le_mul_of_nonneg_left hq2 (by positivity : 0 ≤ 12*t)
    have hm2 := mul_le_mul_of_nonneg_left hcub ht0
    nlinarith
  have hpi := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (by linarith : 0 ≤ (Complex.exp (4*(v+(s : ℂ)))).re)
  have hder : (deriv (modelDerivative t) (v+(s : ℂ))).re=
      12*t*((v+(s : ℂ)).re^2-(v+(s : ℂ)).im^2)-16*Real.pi*(Complex.exp (4*(v+(s : ℂ)))).re := by
    rw [(modelDerivative_hasDerivAt t _).deriv]
    simp [pow_two,Complex.sub_re,Complex.mul_re,Complex.mul_im]
  rw [hder]
  nlinarith [mul_nonneg ht0 (sq_nonneg (v+(s : ℂ)).im),mul_nonneg ht0 (pow_nonneg hw0 3)]




theorem left_phase_quadratic_bound (t : ℝ) (c₀ : ℂ) (hcenter : c₀.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c₀‖) (w v : ℂ)
    (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c₀))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c₀‖) (hv : ‖v-w‖ ≤ 1/‖c₀‖)
    (z : ℂ) (hz : complexSlope t v= -(Complex.I*z)) (s : ℝ) (hs1 : -1 ≤ s) (hs0 : s ≤ 0) :
    (leadingPhase t z v (s : ℂ)).re ≤
      (30005*Real.exp (-4*w.re+4))*|s|-(t*w.re^3/2048)*s^2 := by
  let c := t*w.re^3/2048
  let f := fun a : ℝ => (leadingPhase t z v (a : ℂ)).re+c*a^2
  let f1 := fun a : ℝ => (modelDerivative t (v+(a : ℂ))+Complex.I*z).re+2*c*a
  let f2 := fun a : ℝ => (deriv (modelDerivative t) (v+(a : ℂ))).re+2*c
  have h1 (a : ℝ) : HasDerivAt f (f1 a) a := by
    have hd := ((leadingPhase_hasDerivAt t z v (a : ℂ)).real_of_complex).add
      (((hasDerivAt_id a).pow 2).const_mul c)
    convert hd using 1
    · funext y; rfl
    · dsimp [f1]; ring
  have h2 (a : ℝ) : HasDerivAt f1 (f2 a) a := by
    have hm := modelDerivative_hasDerivAt t (v+(a : ℂ))
    have hc := (hm.comp (a : ℂ) ((hasDerivAt_id (a : ℂ)).const_add v)).add_const (Complex.I*z)
    have hc' : HasDerivAt (fun u : ℂ => modelDerivative t (v+u)+Complex.I*z)
        (deriv (modelDerivative t) (v+(a : ℂ))) (a : ℂ) := by
      convert hc using 1 <;> first | rfl | simp only [hm.deriv,mul_one]
    have hd := hc'.real_of_complex.add ((hasDerivAt_id a).const_mul (2*c))
    convert hd using 1
    · funext y; rfl
    · dsimp [f2]; ring
  have hf0 : f 0=0 := by simp [f,leadingPhase_zero]
  have hc : ConcaveOn ℝ (Icc (-1 : ℝ) 0) f := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := f1) (f'' := f2)
      (convex_Icc _ _) (fun a _ => (h1 a).continuousAt.continuousWithinAt)
      (fun a _ => (h1 a).hasDerivWithinAt) (fun a _ => (h2 a).hasDerivWithinAt)
    intro a ha
    have ha' : a ∈ Icc (-1 : ℝ) 0 := interior_subset ha
    have h := (left_unit_domain_curvature t c₀ hcenter ht hx w v hr hi hs hp hv a ha'.1 ha'.2).2.2
    dsimp [f2,c]
    linarith
  have htangent : f s ≤ f1 0*s := by
    rcases lt_or_eq_of_le hs0 with hneg | heq
    · have h := hc.le_slope_of_hasDerivAt ⟨hs1,hs0⟩ (show (0 : ℝ) ∈ Icc (-1 : ℝ) 0 by norm_num) hneg (h1 0)
      rw [slope_def_field,hf0] at h
      have hm := (le_div_iff₀ (by linarith : 0 < 0-s)).mp h
      nlinarith
    · subst s; simp [hf0]
  have he := horizontal_neighbor_error t c₀ hcenter ht hx w v (by linarith) hi hs hp hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at he
  have hid : f1 0= -(complexSlope t v-modelDerivative t v).re := by
    have hid : modelDerivative t v+Complex.I*z= -(complexSlope t v-modelDerivative t v) := by rw [hz]; ring
    simp only [f1,Complex.ofReal_zero,add_zero,mul_zero,hid,Complex.neg_re]
  have hf1 : |f1 0| ≤ 30005*Real.exp (-4*w.re+4) := by
    rw [hid,abs_neg]
    exact (Complex.abs_re_le_norm _).trans he
  have hm := mul_le_mul_of_nonneg_right hf1 (abs_nonneg s)
  have hprod : f1 0*s ≤ (30005*Real.exp (-4*w.re+4))*|s| :=
    (le_abs_self _).trans (by rw [abs_mul]; exact hm)
  dsimp [f,c] at htangent
  linarith



theorem actual_left_annulus_bound (t : ℝ) (c₀ : ℂ) (hcenter : c₀.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c₀‖) (w v : ℂ)
    (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c₀))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c₀‖) (hv : ‖v-w‖ ≤ 1/‖c₀‖)
    (z : ℂ) (hz : complexSlope t v= -(Complex.I*z))
    (R : ℝ) (hR0 : 0 < R) (hR1 : R ≤ 1)
    (hsmall : 30005*Real.exp (-4*w.re+4) ≤ (t*w.re^3/4096)*R) :
    IntervalIntegrable (fun s : ℝ => saddleWeight t z (v+(s : ℂ))) volume (-1) (-R) ∧
    ‖∫ s : ℝ in -1..-R, saddleWeight t z (v+(s : ℂ))‖ ≤
      1000*‖saddleWeight t z v‖*Real.exp (-(t*w.re^3/4096)*R^2) := by
  have hpoint (s : ℝ) (hs1 : -1 ≤ s) (hsR : s ≤ -R) :
      ‖saddleWeight t z (v+(s : ℂ))‖ ≤
        1000*‖saddleWeight t z v‖*Real.exp (-(t*w.re^3/4096)*R^2) := by
    have hs0 : s ≤ 0 := by linarith
    have hd := left_unit_domain_curvature t c₀ hcenter ht hx w v hr hi hs hp hv s hs1 hs0
    have hd0 := left_unit_domain_curvature t c₀ hcenter ht hx w v hr hi hs hp hv 0 (by norm_num) le_rfl
    simp only [Complex.ofReal_zero,add_zero] at hd0
    have he := actual_weight_model_envelope t z v (s : ℂ) hd0.1 hd0.2.1 hd.1 (by linarith [hd.2.1])
    have hphase := left_phase_quadratic_bound t c₀ hcenter ht hx w v hr hi hs hp hv z hz s hs1 hs0
    have hc : 0 ≤ t*w.re^3/4096 := by positivity
    have hab : R ≤ |s| := by rw [abs_of_nonpos hs0]; linarith
    have hm1 := mul_le_mul_of_nonneg_right hsmall (abs_nonneg s)
    have hm2 := mul_le_mul_of_nonneg_left hab hc
    have hm3 := mul_le_mul_of_nonneg_right hm2 (abs_nonneg s)
    have hsq := (sq_le_sq₀ hR0.le (abs_nonneg s)).mpr hab
    rw [sq_abs] at hsq
    have hm4 := mul_le_mul_of_nonneg_left hsq hc
    have hexp : (leadingPhase t z v (s : ℂ)).re ≤ -(t*w.re^3/4096)*R^2 := by
      nlinarith [sq_abs s]
    exact he.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity))
  have hc : ContinuousOn (fun s : ℝ => saddleWeight t z (v+(s : ℂ))) (Icc (-1 : ℝ) 0) := by
    intro s hs'
    have hd := left_unit_domain_curvature t c₀ hcenter ht hx w v hr hi hs hp hv s hs'.1 hs'.2
    have hk := kernelComplex_analyticAt (v+(s : ℂ)) (by linarith [hd.2.1])
    have hw : AnalyticAt ℂ (saddleWeight t z) (v+(s : ℂ)) := by
      unfold saddleWeight
      apply AnalyticAt.mul
      · fun_prop
      · exact hk
    exact (ContinuousAt.comp (g := saddleWeight t z) (f := fun a : ℝ => v+(a : ℂ))
      hw.continuousAt (by fun_prop)).continuousWithinAt
  have hi' : IntervalIntegrable (fun s : ℝ => saddleWeight t z (v+(s : ℂ))) volume (-1) (-R) :=
    (hc.mono (uIcc_subset_Icc (by constructor <;> norm_num)
      (by constructor <;> linarith))).intervalIntegrable
  refine ⟨hi',?_⟩
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (-1 : ℝ)) (b := -R) (f := fun s : ℝ => saddleWeight t z (v+(s : ℂ)))
    (C := 1000*‖saddleWeight t z v‖*Real.exp (-(t*w.re^3/4096)*R^2)) ?_
  · rw [abs_of_nonneg (by linarith : 0 ≤ -R-(-1))] at hb
    have hm := mul_le_mul_of_nonneg_left (by linarith : -R-(-1) ≤ 1)
      (by positivity : 0 ≤ 1000*‖saddleWeight t z v‖*Real.exp (-(t*w.re^3/4096)*R^2))
    nlinarith
  · intro s hs'
    rw [uIoc_of_le (by linarith : (-1 : ℝ) ≤ -R)] at hs'
    exact hpoint s hs'.1.le hs'.2




theorem relative_actual_left_annulus_bound (t : ℝ) (c₀ : ℂ) (hcenter : c₀.im ≤ 0) (ht : 1 ≤ t) (hx : 10000 ≤ ‖c₀‖)
    (w v : ℂ) (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c₀))
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ ‖c₀‖) (hv : ‖v-w‖ ≤ 1/‖c₀‖)
    (z : ℂ) (hz : complexSlope t v= -(Complex.I*z))
    (R : ℝ) (hR0 : 0 < R) (hR1 : R ≤ 1)
    (hsmall : 30005*Real.exp (-4*w.re+4) ≤ (t*w.re^3/4096)*R) :
    ‖(∫ s : ℝ in -1..-R, saddleWeight t z (v+(s : ℂ)))/
      (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤
      2000*Real.sqrt ‖c₀‖*Real.exp (-(t*w.re^3/4096)*R^2) := by
  have ht0 : 0 ≤ t := by linarith
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hmul := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 4*t*‖w‖^3+9 ≤ ‖c₀‖ := by nlinarith [pow_nonneg (norm_nonneg w) 3]
  have he := (actual_left_annulus_bound t c₀ hcenter ht (by linarith) w v hr hi hs hp0 hv z hz R hR0 hR1 hsmall).2
  let W := saddleWeight t z v
  let G := ∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)
  let B := 1000*Real.exp (-(t*w.re^3/4096)*R^2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hnormal := gaussian_normalization_lower t c₀ hcenter ht hx w v (by linarith) hi hp hs hv
  change 1 ≤ 2*Real.sqrt ‖c₀‖*‖G‖ at hnormal
  have hG : G ≠ 0 := by intro h; norm_num [h] at hnormal
  have hd := horizontal_neighbor_domain t c₀ hcenter ht (by linarith) w v (by linarith) hi hs hp0 hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hd
  have hW : W ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (kernel_ne_zero v hd.1 hd.2.1)
  have hnum : ‖∫ s : ℝ in -1..-R, saddleWeight t z (v+(s : ℂ))‖ ≤ ‖W‖*B := by
    apply he.trans_eq
    dsimp [W,B]
    ring
  have htarget : 2000*Real.sqrt ‖c₀‖*Real.exp (-(t*w.re^3/4096)*R^2)=2*Real.sqrt ‖c₀‖*B := by
    dsimp [B]
    ring
  rw [htarget]
  change ‖(∫ s : ℝ in -1..-R, saddleWeight t z (v+(s : ℂ)))/(W*G)‖ ≤ _
  rw [norm_div,norm_mul]
  apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hW) (norm_pos_iff.mpr hG))).mpr
  have hm := mul_le_mul_of_nonneg_left hnormal (mul_nonneg (norm_nonneg W) hB)
  nlinarith



theorem relative_left_annulus_budget (t : ℝ) (c₀ : ℂ) (hcenter : c₀.im ≤ 0) (ht : 1 ≤ t) (hx : 10000 ≤ ‖c₀‖)
    (w v : ℂ) (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c₀))
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ ‖c₀‖) (hv : ‖v-w‖ ≤ 1/‖c₀‖)
    (z : ℂ) (hz : complexSlope t v= -(Complex.I*z))
    (R : ℝ) (hR0 : 0 < R) (hR1 : R ≤ 1)
    (hsmall : 30005*Real.exp (-4*w.re+4) ≤ (t*w.re^3/4096)*R) :
    ‖(∫ s : ℝ in -1..-R, saddleWeight t z (v+(s : ℂ)))/
      (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤
      100*rightBudget (R/16) w.re := by
  have h := relative_actual_left_annulus_bound t c₀ hcenter ht hx w v hr hi hs hp hv z hz R hR0 hR1 hsmall
  have hx0 : 0 < ‖c₀‖ := by linarith
  have hfreq := frequency_exp_bound t c₀ hcenter ht hx w hp hs
  have hsqrt : Real.sqrt ‖c₀‖ ≤ 10000*Real.exp (2*w.re) := by
    have hsq := Real.sq_sqrt hx0.le
    have hE : Real.exp (2*w.re)^2=Real.exp (4*w.re) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    nlinarith [Real.sqrt_nonneg ‖c₀‖,Real.exp_pos (2*w.re),Real.exp_pos (4*w.re)]
  have hwt : w.re^3 ≤ t*w.re^3 := by nlinarith [pow_nonneg (by linarith : 0 ≤ w.re) 3]
  have hm := mul_le_mul_of_nonneg_right hwt (sq_nonneg R)
  have he : Real.exp (-(t*w.re^3/4096)*R^2) ≤ Real.exp (-(w.re^3/4096)*R^2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hcoef : (20000000 : ℝ) ≤ 25600000/R := (le_div_iff₀ hR0).mpr (by nlinarith)
  apply h.trans
  calc
    _ ≤ 2000*(10000*Real.exp (2*w.re))*Real.exp (-(w.re^3/4096)*R^2) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) he (by positivity) (by positivity)
    _ = 20000000*Real.exp (2*w.re-(R^2/4096)*w.re^3) := by
      rw [show 2*w.re-(R^2/4096)*w.re^3=2*w.re+(-(w.re^3/4096)*R^2) by ring,Real.exp_add]
      ring
    _ ≤ (25600000/R)*Real.exp (2*w.re-(R^2/4096)*w.re^3) :=
      mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
    _ = 100*rightBudget (R/16) w.re := by
      dsimp [rightBudget]
      have hid : (R/16)^2/16=R^2/4096 := by ring
      rw [hid]
      ring


theorem uniform_relative_right_tail (R η : ℝ) (hR : 0 < R) (hη : 0 < η) :
    ∃ N : ℝ, ∀ c₀ : ℂ, c₀.im ≤ 0 → N ≤ ‖c₀‖ → ∀ t : ℝ, 1 ≤ t → ∀ w v : ℂ,
      64 ≤ w.re → |w.im| ≤ 1/2 → 100*(t*(‖w‖+1)^3+1) ≤ ‖c₀‖ →
      modelDerivative t w = -(Complex.I*c₀) → ‖v-w‖ ≤ 1/‖c₀‖ →
      ∀ z : ℂ, complexSlope t v = -(Complex.I*z) →
      ‖(∫ s : ℝ in Ioi R, saddleWeight t z (v+(s : ℂ)))/
        (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤ η := by
  obtain ⟨A,hA⟩ := eventually_atTop.mp ((rightBudget_tendsto_zero R hR).eventually (gt_mem_nhds hη))
  refine ⟨max (max 10000 (32*Real.exp (4*A))) (100000000/R),?_⟩
  intro c₀ hcenter hlarge t ht w v hr hi hp hs hv z hz
  have hxbase : max 10000 (32*Real.exp (4*A)) ≤ ‖c₀‖ := (le_max_left _ _).trans hlarge
  have hx : 10000 ≤ ‖c₀‖ := (le_max_left _ _).trans hxbase
  have hxA : 32*Real.exp (4*A) ≤ ‖c₀‖ := (le_max_right _ _).trans hxbase
  have hxR : 100000000/R ≤ ‖c₀‖ := (le_max_right _ _).trans hlarge
  have hfreq := model_frequency_exp_bound t c₀ hcenter ht hx w hp hs
  have hw : A ≤ w.re := by
    have he : Real.exp (4*A) ≤ Real.exp (4*w.re) := by linarith
    have he' := Real.exp_le_exp.mp he
    linarith
  have he := arithmetic_error_frequency_bound t c₀ hcenter ht hx w hp hs
  have hx0 : 0 < ‖c₀‖ := by linarith
  have heR : 100000000/‖c₀‖ ≤ R := by
    apply (div_le_iff₀ hx0).mpr
    have hm := (div_le_iff₀ hR).mp hxR
    nlinarith
  have hw3 : 16 ≤ w.re^3 := by
    have hw2 : 1 ≤ w.re^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hw2 (by linarith : 0 ≤ w.re)]
  have hwt : w.re^3 ≤ t*w.re^3 := by nlinarith
  have hsmall : 30005*Real.exp (-4*w.re+4) ≤ (t*w.re^3/16)*R := by
    have hm := mul_le_mul_of_nonneg_right (by linarith : 1 ≤ t*w.re^3/16) hR.le
    linarith
  exact (relative_right_tail_budget t c₀ hcenter ht hx w v hr hi hs hp hv z hz R hR hsmall).trans (hA w.re hw).le



theorem uniform_relative_left_annulus (R η : ℝ) (hR0 : 0 < R) (hR1 : R ≤ 1) (hη : 0 < η) :
    ∃ N : ℝ, ∀ c₀ : ℂ, c₀.im ≤ 0 → N ≤ ‖c₀‖ → ∀ t : ℝ, 1 ≤ t → ∀ w v : ℂ,
      120020 ≤ w.re → |w.im| ≤ 1/2 → 100*(t*(‖w‖+1)^3+1) ≤ ‖c₀‖ →
      modelDerivative t w = -(Complex.I*c₀) → ‖v-w‖ ≤ 1/‖c₀‖ →
      ∀ z : ℂ, complexSlope t v = -(Complex.I*z) →
      ‖(∫ s : ℝ in -1..-R, saddleWeight t z (v+(s : ℂ)))/
        (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤ η := by
  have hlim : Tendsto (fun a : ℝ => 100*rightBudget (R/16) a) atTop (nhds 0) := by
    simpa only [mul_zero] using (rightBudget_tendsto_zero (R/16) (by positivity)).const_mul (100 : ℝ)
  obtain ⟨A,hA⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hη))
  refine ⟨max (max 10000 (100000000*Real.exp (4*A))) (100000000/R),?_⟩
  intro c₀ hcenter hlarge t ht w v hr hi hp hs hv z hz
  have hxbase : max 10000 (100000000*Real.exp (4*A)) ≤ ‖c₀‖ := (le_max_left _ _).trans hlarge
  have hx : 10000 ≤ ‖c₀‖ := (le_max_left _ _).trans hxbase
  have hxA : 100000000*Real.exp (4*A) ≤ ‖c₀‖ := (le_max_right _ _).trans hxbase
  have hxR : 100000000/R ≤ ‖c₀‖ := (le_max_right _ _).trans hlarge
  have hfreq := frequency_exp_bound t c₀ hcenter ht hx w hp hs
  have hw : A ≤ w.re := by
    have he : Real.exp (4*A) ≤ Real.exp (4*w.re) := by linarith
    have he' := Real.exp_le_exp.mp he
    linarith
  have he := arithmetic_error_frequency_bound t c₀ hcenter ht hx w hp hs
  have hx0 : 0 < ‖c₀‖ := by linarith
  have heR : 100000000/‖c₀‖ ≤ R := by
    apply (div_le_iff₀ hx0).mpr
    have hm := (div_le_iff₀ hR0).mp hxR
    nlinarith
  have hw3 : 4096 ≤ w.re^3 := by
    have hw2 : 1 ≤ w.re^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hw2 (by linarith : 0 ≤ w.re)]
  have hwt : w.re^3 ≤ t*w.re^3 := by nlinarith
  have hsmall : 30005*Real.exp (-4*w.re+4) ≤ (t*w.re^3/4096)*R := by
    have hm := mul_le_mul_of_nonneg_right (by linarith : 1 ≤ t*w.re^3/4096) hR0.le
    linarith
  exact (relative_left_annulus_budget t c₀ hcenter ht hx w v hr hi hs hp hv z hz R hR0 hR1 hsmall).trans (hA w.re hw).le

theorem uniform_horizontal_gaussian_error (η : ℝ) (hη : 0 < η) :
    ∃ N : ℝ, ∀ c₀ : ℂ, c₀.im ≤ 0 → N ≤ ‖c₀‖ → ∀ t : ℝ, 1 ≤ t → ∀ w v : ℂ,
      120020 ≤ w.re → |w.im| ≤ 1/2 → 100*(t*(‖w‖+1)^3+1) ≤ ‖c₀‖ →
      modelDerivative t w = -(Complex.I*c₀) → ‖v-w‖ ≤ 1/‖c₀‖ →
      ∀ z : ℂ, complexSlope t v = -(Complex.I*z) → z.im ≤ 0 →
      IntegrableOn (fun s : ℝ => saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I)) (Ioi 0) ∧
      ‖(∫ s : ℝ in Ioi 0, saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I))/
        (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))-1‖ ≤ η := by
  let R : ℝ := 1/8192
  have hR : 0 < R := by norm_num [R]
  obtain ⟨N₁,hcompact⟩ := uniform_relative_left_compact (η/8) (by positivity)
  obtain ⟨N₂,hleft⟩ := uniform_relative_left_annulus R (η/8) hR (by norm_num [R]) (by positivity)
  obtain ⟨N₃,hfixed⟩ := uniform_fixed_gaussian_error R (η/8) hR (by norm_num [R]) (by positivity)
  obtain ⟨N₄,hright⟩ := uniform_relative_right_tail R (η/8) hR (by positivity)
  refine ⟨max (max N₁ N₂) (max (max N₃ N₄) (max 10000 (100000000/R))),?_⟩
  intro c₀ hcenter hlarge t ht w v hr hi hp hs hv z hz hzim
  have h12 : max N₁ N₂ ≤ ‖c₀‖ := (le_max_left _ _).trans hlarge
  have hrest : max (max N₃ N₄) (max 10000 (100000000/R)) ≤ ‖c₀‖ := (le_max_right _ _).trans hlarge
  have h34 : max N₃ N₄ ≤ ‖c₀‖ := (le_max_left _ _).trans hrest
  have hbase : max 10000 (100000000/R) ≤ ‖c₀‖ := (le_max_right _ _).trans hrest
  have hN₁c : N₁ ≤ ‖c₀‖ := (le_max_left _ _).trans h12
  have hN₂c : N₂ ≤ ‖c₀‖ := (le_max_right _ _).trans h12
  have hN₃c : N₃ ≤ ‖c₀‖ := (le_max_left _ _).trans h34
  have hN₄c : N₄ ≤ ‖c₀‖ := (le_max_right _ _).trans h34
  have hx : 10000 ≤ ‖c₀‖ := (le_max_left _ _).trans hbase
  have hxR : 100000000/R ≤ ‖c₀‖ := (le_max_right _ _).trans hbase
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 < ‖c₀‖ := by linarith
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hmul := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 4*t*‖w‖^3+9 ≤ ‖c₀‖ := by nlinarith [pow_nonneg (norm_nonneg w) 3]
  have hgeom := RiemannQuarticComplexCorrection.corrected_saddle_geometry t c₀ hcenter ht hx w v hr hi hp hs
    (by simpa only [mem_closedBall,dist_eq_norm] using hv)
  have he := arithmetic_error_frequency_bound t c₀ hcenter ht hx w hp hs
  have heR : 100000000/‖c₀‖ ≤ R := by
    apply (div_le_iff₀ hx0).mpr
    have hm := (div_le_iff₀ hR).mp hxR
    nlinarith
  have hw3 : 16 ≤ w.re^3 := by
    have hw2 : 1 ≤ w.re^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hw2 (by linarith : 0 ≤ w.re)]
  have hwt : w.re^3 ≤ t*w.re^3 := by nlinarith
  have hsmall : 30005*Real.exp (-4*w.re+4) ≤ (t*w.re^3/16)*R := by
    have hm := mul_le_mul_of_nonneg_right (by linarith : 1 ≤ t*w.re^3/16) hR.le
    linarith
  have htail := (actual_right_tail_bound t c₀ hcenter ht (by linarith) w v (by linarith) hi hs hp0 hv z hz R hR hsmall).1
  refine ⟨shifted_weight_integrable t z v.im hgeom.2.1,?_⟩
  have hsplit := horizontal_decomposition t z v hgeom.2.1 R htail
  have hC := hcompact c₀ hcenter hN₁c t ht w v hr hi hp hs hv z hz hzim
  have hL := hleft c₀ hcenter hN₂c t ht w v hr hi hp hs hv z hz
  have hM := hfixed c₀ hcenter hN₃c t ht w v (by linarith) hi hp hs hv z hz
  have hT := hright c₀ hcenter hN₄c t ht w v (by linarith) hi hp hs hv z hz
  let D := saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2))
  let C := ∫ s : ℝ in 0..v.re-1, saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I)
  let L := ∫ s : ℝ in -1..-R, saddleWeight t z (v+(s : ℂ))
  let M := ∫ s : ℝ in -R..R, saddleWeight t z (v+(s : ℂ))
  let T := ∫ s : ℝ in Ioi R, saddleWeight t z (v+(s : ℂ))
  change ‖C/D‖ ≤ η/8 at hC
  change ‖L/D‖ ≤ η/8 at hL
  change ‖M/D-1‖ ≤ η/8 at hM
  change ‖T/D‖ ≤ η/8 at hT
  rw [hsplit]
  change ‖(C+L+M+T)/D-1‖ ≤ η
  rw [show (C+L+M+T)/D-1=C/D+L/D+(M/D-1)+T/D by ring]
  have h1 := norm_add_le (C/D) (L/D)
  have h2 := norm_add_le (C/D+L/D) (M/D-1)
  have h3 := norm_add_le (C/D+L/D+(M/D-1)) (T/D)
  linarith

theorem eventually_actual_horizontal_gaussian (t : ℝ) (ht : 1 ≤ t) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ a : ℝ in atTop, ∀ c : ℂ, c.im ≤ 0 → ‖c‖ = 4*Real.pi*Real.exp (4*a) →
      ∃ v : ℂ, complexSlope t v = -(Complex.I*c) ∧
        1 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ kernelComplex v ≠ 0 ∧
        IntegrableOn (fun s : ℝ => saddleWeight t c ((s : ℂ)+(v.im : ℂ)*Complex.I)) (Ioi 0) ∧
        ‖(∫ s : ℝ in Ioi 0, saddleWeight t c ((s : ℂ)+(v.im : ℂ)*Complex.I))/
          (saddleWeight t c v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))-1‖ ≤ η := by
  obtain ⟨N,hN⟩ := uniform_horizontal_gaussian_error η hη
  filter_upwards [RiemannQuarticComplexCorrection.eventually_actual_half_circles t ht,
    RiemannQuarticDomain.quartic_exponent_dominated (80000*(t+1)) 0,
    eventually_ge_atTop (max N (240040 : ℝ))] with a hex hdom ha
  intro c hc hn
  have haN : N ≤ a := (le_max_left N _).trans ha
  have ha : 240040 ≤ a := (le_max_right N _).trans ha
  have ha0 : 0 ≤ a := by linarith
  have ht0 : 0 ≤ t := by linarith
  obtain ⟨w,v,hw,hs,hv,hroot,hrv,hiv,hkn,hE,hd⟩ := hex c hc hn
  have hp3 := pow_le_pow_left₀ (by linarith : 0 ≤ a+3) (by linarith : a+3 ≤ 2*a) 3
  have hp34 : a^3 ≤ a^4 := by nlinarith [mul_nonneg (by linarith : 0 ≤ a-1) (pow_nonneg ha0 3)]
  have hM : (a+3)^3 ≤ 8*a^4 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ 10000*(t+1))
  simp only [zero_mul,add_zero] at hdom
  have hscale : 10000*(t+1)*(a+3)^3 ≤ ‖c‖ := by
    rw [hn]
    nlinarith [Real.pi_gt_three,Real.exp_pos (4*a)]
  have hdist : ‖w-RiemannQuarticComplexModelSaddle.complexAnchor c‖ ≤ (1/1024 : ℝ) := by
    simpa only [mem_closedBall,dist_eq_norm] using hw
  have hreal := (Complex.abs_re_le_norm (w-RiemannQuarticComplexModelSaddle.complexAnchor c)).trans hdist
  have hg := RiemannQuarticComplexModelSaddle.complexAnchor_geometry a ha0 c hc hn
  simp only [Complex.sub_re,hg.1] at hreal
  have hr : 120020 ≤ w.re := by linarith [(abs_le.mp hreal).1]
  have hnorm : ‖w‖+1 ≤ a+3 := by
    have hb := norm_add_le (w-RiemannQuarticComplexModelSaddle.complexAnchor c)
      (RiemannQuarticComplexModelSaddle.complexAnchor c)
    rw [sub_add_cancel] at hb
    linarith [hg.2.2]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ ‖w‖+1) hnorm 3
  have hps : 100*(t*(‖w‖+1)^3+1) ≤ ‖c‖ := by
    have hmul := mul_le_mul_of_nonneg_left hpow ht0
    nlinarith [pow_nonneg (by linarith : 0 ≤ a+3) 3]
  have hi : |w.im| ≤ 1/2 := by
    have hh := abs_add_le (w.im-(RiemannQuarticComplexModelSaddle.complexAnchor c).im)
      (RiemannQuarticComplexModelSaddle.complexAnchor c).im
    simp only [sub_add_cancel] at hh
    have hdiff := (Complex.abs_im_le_norm (w-RiemannQuarticComplexModelSaddle.complexAnchor c)).trans hdist
    simp only [Complex.sub_im] at hdiff
    linarith [hg.2.1,Real.pi_lt_d2]
  have hNc : N ≤ ‖c‖ := by
    have he := Real.add_one_le_exp (4*a)
    rw [hn]
    nlinarith [Real.pi_gt_three,Real.exp_pos (4*a)]
  have hclose : ‖v-w‖ ≤ 1/‖c‖ := by simpa only [mem_closedBall,dist_eq_norm] using hv
  exact ⟨v,hroot,hrv,hiv,hkn,hN c hc hNc t ht w v hr hi hps hs hclose c hroot hc⟩

theorem far_actual_horizontal_gaussian (t : ℝ) (ht : 1 ≤ t) (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    ∃ X : ℝ, 0 < X ∧ ∀ c : ℂ, X ≤ ‖c‖ → c.im ≤ 0 → ∃ v : ℂ,
      complexSlope t v = -(Complex.I*c) ∧
      1 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ kernelComplex v ≠ 0 ∧
      IntegrableOn (fun s : ℝ => saddleWeight t c ((s : ℂ)+(v.im : ℂ)*Complex.I)) (Ioi 0) ∧
      ‖(∫ s : ℝ in Ioi 0, saddleWeight t c ((s : ℂ)+(v.im : ℂ)*Complex.I))/
        (saddleWeight t c v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))-1‖ ≤ η ∧
      (∫ s : ℝ in Ioi 0, saddleWeight t c ((s : ℂ)+(v.im : ℂ)*Complex.I)) ≠ 0 := by
  obtain ⟨A,hA⟩ := eventually_atTop.mp (eventually_actual_horizontal_gaussian t ht η hη)
  let X := 4*Real.pi*Real.exp (4*A)
  have hX : 0 < X := by dsimp [X]; positivity
  refine ⟨X,hX,?_⟩
  intro c hc him
  have hn0 : 0 < ‖c‖ := hX.trans_le hc
  let a := Real.log (‖c‖/(4*Real.pi))/4
  have hq : 0 < ‖c‖/(4*Real.pi) := by positivity
  have hn : ‖c‖ = 4*Real.pi*Real.exp (4*a) := by
    rw [show 4*a = Real.log (‖c‖/(4*Real.pi)) by dsimp [a]; ring,Real.exp_log hq]
    field_simp
  have hAa : A ≤ a := by
    have he : Real.exp (4*A) ≤ Real.exp (4*a) := by
      rw [hn] at hc
      change 4*Real.pi*Real.exp (4*A) ≤ 4*Real.pi*Real.exp (4*a) at hc
      exact (mul_le_mul_iff_right₀ (by positivity : 0 < 4*Real.pi)).mp hc
    have hh := Real.exp_le_exp.mp he
    linarith
  obtain ⟨v,hroot,hr,hi,hkn,hInt,hrel⟩ := hA a hAa c him hn
  refine ⟨v,hroot,hr,hi,hkn,hInt,hrel,?_⟩
  intro hz
  rw [hz,zero_div,zero_sub,norm_neg,norm_one] at hrel
  linarith

theorem reflected_weight_norm (t : ℝ) (z q : ℂ) :
    ‖saddleWeight t (-z) (conj q)‖ =
      ‖saddleWeight t z q‖*Real.exp (2*z.im*q.re) := by
  have hc : ‖saddleWeight t (-z) (conj q)‖ = ‖saddleWeight t (conj z) q‖ := by
    simpa using congrArg norm (RiemannQuarticFarPairing.weight_conj t (conj z) q)
  rw [hc]
  have hp : ((t : ℂ)*q^4+Complex.I*(conj z)*q).re =
      ((t : ℂ)*q^4+Complex.I*z*q).re+2*z.im*q.re := by
    simp only [Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
      zero_mul,one_mul,zero_sub,neg_mul,Complex.conj_re,Complex.conj_im]
    ring
  unfold saddleWeight
  simp only [norm_mul,Complex.norm_exp]
  rw [hp,Real.exp_add]
  ring

end OperatorDerivativeRewrite.Foundation.RiemannQuarticComplexContour
