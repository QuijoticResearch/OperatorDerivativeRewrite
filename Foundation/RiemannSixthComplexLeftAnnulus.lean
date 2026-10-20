import Foundation.RiemannSixthComplexLeftCompact
/-! Genuine sixth-order left unit-annulus bounds at complex frequency
centers, with the actual/model stationary mismatch retained. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthComplexLeftAnnulus
open RiemannSixthComplexLeftCompact RiemannSixthComplexRightTail
open RiemannSixthComplexGaussian RiemannSixthComplexCorrection RiemannSixthFarSignedIntegral
open RiemannEvenModelPhase RiemannEvenSaddleBranch RiemannEvenComplexWeight
open RiemannEvenWeightEnvelope (horizontal_exp_real_identity)
open RiemannSixthFarRightTail (actual_weight_model_envelope)
open RiemannQuarticFarRightTail (rightBudget rightBudget_tendsto_zero)
open RiemannThetaComplexKernel

theorem left_unit_domain_curvature (t : ℝ) (c₀ : ℂ) (hcenter : c₀.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c₀‖) (w v : ℂ)
    (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*c₀))
    (hp : 6*t*‖w‖^5+9 ≤ ‖c₀‖) (hv : ‖v-w‖ ≤ 1/‖c₀‖)
    (s : ℝ) (hs1 : -1 ≤ s) (hs0 : s ≤ 0) :
    0 ≤ (v+(s : ℂ)).re ∧ 1 ≤ (Complex.exp (4*(v+(s : ℂ)))).re ∧
      (deriv (modelDerivative 3 t) (v+(s : ℂ))).re ≤ -(t*w.re^5)/1024 := by
  have hd := horizontal_neighbor_domain t c₀ hcenter ht hx w v (by linarith) hi hs hp hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hd
  have ht0 : 0 ≤ t := by linarith
  have hw0 : 0 ≤ w.re := by linarith
  have hx0 : 0 < ‖c₀‖ := by linarith
  have hq0 : 0 ≤ (v+(s : ℂ)).re := by
    simp only [Complex.add_re,Complex.ofReal_re]
    linarith [(abs_le.mp hd.2.2.2).1]
  have hvsmall : ‖v-w‖ ≤ 1/8 := hv.trans ((div_le_iff₀ hx0).mpr (by linarith))
  have hwNorm := Complex.norm_le_abs_re_add_abs_im w
  rw [abs_of_nonneg hw0] at hwNorm
  have htri := norm_add_le (v-w) w
  rw [sub_add_cancel] at htri
  have hvnorm : ‖v‖+1 ≤ 2*w.re := by linarith
  have hsabs : |s| ≤ 1 := by rw [abs_of_nonpos hs0]; linarith
  have hqtri := norm_add_le v (s : ℂ)
  simp only [Complex.norm_real,Real.norm_eq_abs] at hqtri
  have hqnorm : ‖v+(s : ℂ)‖ ≤ 2*w.re := by linarith
  have hqpow := pow_le_pow_left₀ (norm_nonneg (v+(s : ℂ))) hqnorm 4
  norm_num [mul_pow] at hqpow
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
  have hEid := horizontal_exp_real_identity v s
  have heprod := mul_le_mul hes hd.2.2.1 (by positivity : 0 ≤ t*w.re^5/64) (Real.exp_pos _).le
  have hElow : t*w.re^5/5184 ≤ (Complex.exp (4*(v+(s : ℂ)))).re := by
    rw [hEid]
    nlinarith
  have hw5 : 5184 ≤ w.re^5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 6) (by linarith : 6 ≤ w.re) 5
    norm_num at h
    linarith
  have hwt : w.re^5 ≤ t*w.re^5 := by nlinarith [pow_nonneg hw0 5]
  have hE1 : 1 ≤ (Complex.exp (4*(v+(s : ℂ)))).re := by linarith
  refine ⟨hq0,hE1,?_⟩
  have hpoly : 103680*w.re^4 ≤ w.re^5 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ w.re-103680) (pow_nonneg hw0 4)]
  have hpolyT := mul_le_mul_of_nonneg_left hpoly ht0
  have hreal := Complex.re_le_norm ((v+(s : ℂ))^4)
  rw [norm_pow] at hreal
  have hrealT := mul_le_mul_of_nonneg_left (hreal.trans hqpow) (by positivity : 0 ≤ 30*t)
  have hpi := mul_le_mul_of_nonneg_right Real.pi_gt_three.le
    (by linarith : 0 ≤ (Complex.exp (4*(v+(s : ℂ)))).re)
  have hder : (deriv (modelDerivative 3 t) (v+(s : ℂ))).re =
      30*t*((v+(s : ℂ))^4).re-16*Real.pi*(Complex.exp (4*(v+(s : ℂ)))).re := by
    rw [(modelDerivative_hasDerivAt 3 t _).deriv]
    norm_num [Complex.mul_re,Complex.sub_re]
  rw [hder]
  nlinarith [mul_nonneg ht0 (pow_nonneg hw0 5)]

theorem left_phase_quadratic_bound (t : ℝ) (c₀ : ℂ) (hcenter : c₀.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c₀‖) (w v : ℂ)
    (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*c₀))
    (hp : 6*t*‖w‖^5+9 ≤ ‖c₀‖) (hv : ‖v-w‖ ≤ 1/‖c₀‖)
    (z : ℂ) (hz : complexSlope 3 t v= -(Complex.I*z)) (s : ℝ) (hs1 : -1 ≤ s) (hs0 : s ≤ 0) :
    (leadingPhase t z v (s : ℂ)).re ≤
      (30005*Real.exp (-4*w.re+4))*|s|-(t*w.re^5/2048)*s^2 := by
  let c := t*w.re^5/2048
  let f := fun a : ℝ => (leadingPhase t z v (a : ℂ)).re+c*a^2
  let f1 := fun a : ℝ => (modelDerivative 3 t (v+(a : ℂ))+Complex.I*z).re+2*c*a
  let f2 := fun a : ℝ => (deriv (modelDerivative 3 t) (v+(a : ℂ))).re+2*c
  have h1 (a : ℝ) : HasDerivAt f (f1 a) a := by
    have hd := ((leadingPhase_hasDerivAt t z v (a : ℂ)).real_of_complex).add
      (((hasDerivAt_id a).pow 2).const_mul c)
    convert hd using 1
    · funext y; rfl
    · dsimp [f1]; ring
  have h2 (a : ℝ) : HasDerivAt f1 (f2 a) a := by
    have hm := modelDerivative_hasDerivAt 3 t (v+(a : ℂ))
    have hc := (hm.comp (a : ℂ) ((hasDerivAt_id (a : ℂ)).const_add v)).add_const (Complex.I*z)
    have hc' : HasDerivAt (fun u : ℂ => modelDerivative 3 t (v+u)+Complex.I*z)
        (deriv (modelDerivative 3 t) (v+(a : ℂ))) (a : ℂ) := by
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
  have hid : f1 0= -(complexSlope 3 t v-modelDerivative 3 t v).re := by
    have hid : modelDerivative 3 t v+Complex.I*z= -(complexSlope 3 t v-modelDerivative 3 t v) := by rw [hz]; ring
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
    (hs : modelDerivative 3 t w= -(Complex.I*c₀))
    (hp : 6*t*‖w‖^5+9 ≤ ‖c₀‖) (hv : ‖v-w‖ ≤ 1/‖c₀‖)
    (z : ℂ) (hz : complexSlope 3 t v= -(Complex.I*z))
    (R : ℝ) (hR0 : 0 < R) (hR1 : R ≤ 1)
    (hsmall : 30005*Real.exp (-4*w.re+4) ≤ (t*w.re^5/4096)*R) :
    IntervalIntegrable (fun s : ℝ => weight 3 t z (v+(s : ℂ))) volume (-1) (-R) ∧
    ‖∫ s : ℝ in -1..-R, weight 3 t z (v+(s : ℂ))‖ ≤
      1000*‖weight 3 t z v‖*Real.exp (-(t*w.re^5/4096)*R^2) := by
  have hpoint (s : ℝ) (hs1 : -1 ≤ s) (hsR : s ≤ -R) :
      ‖weight 3 t z (v+(s : ℂ))‖ ≤
        1000*‖weight 3 t z v‖*Real.exp (-(t*w.re^5/4096)*R^2) := by
    have hs0 : s ≤ 0 := by linarith
    have hd := left_unit_domain_curvature t c₀ hcenter ht hx w v hr hi hs hp hv s hs1 hs0
    have hd0 := left_unit_domain_curvature t c₀ hcenter ht hx w v hr hi hs hp hv 0 (by norm_num) le_rfl
    simp only [Complex.ofReal_zero,add_zero] at hd0
    have he := actual_weight_model_envelope t z v (s : ℂ) hd0.1 hd0.2.1 hd.1 (by linarith [hd.2.1])
    have hphase := left_phase_quadratic_bound t c₀ hcenter ht hx w v hr hi hs hp hv z hz s hs1 hs0
    have hc : 0 ≤ t*w.re^5/4096 := by positivity
    have hab : R ≤ |s| := by rw [abs_of_nonpos hs0]; linarith
    have hm1 := mul_le_mul_of_nonneg_right hsmall (abs_nonneg s)
    have hm2 := mul_le_mul_of_nonneg_left hab hc
    have hm3 := mul_le_mul_of_nonneg_right hm2 (abs_nonneg s)
    have hsq := (sq_le_sq₀ hR0.le (abs_nonneg s)).mpr hab
    rw [sq_abs] at hsq
    have hm4 := mul_le_mul_of_nonneg_left hsq hc
    have hexp : (leadingPhase t z v (s : ℂ)).re ≤ -(t*w.re^5/4096)*R^2 := by
      nlinarith [sq_abs s]
    exact he.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity))
  have hc : ContinuousOn (fun s : ℝ => weight 3 t z (v+(s : ℂ))) (Icc (-1 : ℝ) 0) := by
    intro s hs'
    have hd := left_unit_domain_curvature t c₀ hcenter ht hx w v hr hi hs hp hv s hs'.1 hs'.2
    have hk := kernelComplex_analyticAt (v+(s : ℂ)) (by linarith [hd.2.1])
    have hw : AnalyticAt ℂ (weight 3 t z) (v+(s : ℂ)) := by
      unfold weight
      apply AnalyticAt.mul
      · fun_prop
      · exact hk
    exact (ContinuousAt.comp (g := weight 3 t z) (f := fun a : ℝ => v+(a : ℂ))
      hw.continuousAt (by fun_prop)).continuousWithinAt
  have hi' : IntervalIntegrable (fun s : ℝ => weight 3 t z (v+(s : ℂ))) volume (-1) (-R) :=
    (hc.mono (uIcc_subset_Icc (by constructor <;> norm_num)
      (by constructor <;> linarith))).intervalIntegrable
  refine ⟨hi',?_⟩
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (-1 : ℝ)) (b := -R) (f := fun s : ℝ => weight 3 t z (v+(s : ℂ)))
    (C := 1000*‖weight 3 t z v‖*Real.exp (-(t*w.re^5/4096)*R^2)) ?_
  · rw [abs_of_nonneg (by linarith : 0 ≤ -R-(-1))] at hb
    have hm := mul_le_mul_of_nonneg_left (by linarith : -R-(-1) ≤ 1)
      (by positivity : 0 ≤ 1000*‖weight 3 t z v‖*Real.exp (-(t*w.re^5/4096)*R^2))
    nlinarith
  · intro s hs'
    rw [uIoc_of_le (by linarith : (-1 : ℝ) ≤ -R)] at hs'
    exact hpoint s hs'.1.le hs'.2


theorem relative_actual_left_annulus_bound (t : ℝ) (c₀ : ℂ) (hcenter : c₀.im ≤ 0) (ht : 1 ≤ t) (hx : 10000 ≤ ‖c₀‖)
    (w v : ℂ) (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*c₀))
    (hp : 10000*(t*(‖w‖+1)^5+1) ≤ ‖c₀‖) (hv : ‖v-w‖ ≤ 1/‖c₀‖)
    (z : ℂ) (hz : complexSlope 3 t v= -(Complex.I*z))
    (R : ℝ) (hR0 : 0 < R) (hR1 : R ≤ 1)
    (hsmall : 30005*Real.exp (-4*w.re+4) ≤ (t*w.re^5/4096)*R) :
    ‖(∫ s : ℝ in -1..-R, weight 3 t z (v+(s : ℂ)))/
      (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))‖ ≤
      2000*Real.sqrt ‖c₀‖*Real.exp (-(t*w.re^5/4096)*R^2) := by
  have ht0 : 0 ≤ t := by linarith
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 5
  have hmul := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 6*t*‖w‖^5+9 ≤ ‖c₀‖ := by nlinarith [pow_nonneg (norm_nonneg w) 5]
  have he := (actual_left_annulus_bound t c₀ hcenter ht (by linarith) w v hr hi hs hp0 hv z hz R hR0 hR1 hsmall).2
  let W := weight 3 t z v
  let G := ∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)
  let B := 1000*Real.exp (-(t*w.re^5/4096)*R^2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hnormal := gaussian_normalization_lower t c₀ hcenter ht hx w v (by linarith) hi hp hs hv
  change 1 ≤ 2*Real.sqrt ‖c₀‖*‖G‖ at hnormal
  have hG : G ≠ 0 := by intro h; norm_num [h] at hnormal
  have hd := horizontal_neighbor_domain t c₀ hcenter ht (by linarith) w v (by linarith) hi hs hp0 hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hd
  have hW : W ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (kernel_ne_zero v hd.1 hd.2.1)
  have hnum : ‖∫ s : ℝ in -1..-R, weight 3 t z (v+(s : ℂ))‖ ≤ ‖W‖*B := by
    apply he.trans_eq
    dsimp [W,B]
    ring
  have htarget : 2000*Real.sqrt ‖c₀‖*Real.exp (-(t*w.re^5/4096)*R^2)=2*Real.sqrt ‖c₀‖*B := by
    dsimp [B]
    ring
  rw [htarget]
  change ‖(∫ s : ℝ in -1..-R, weight 3 t z (v+(s : ℂ)))/(W*G)‖ ≤ _
  rw [norm_div,norm_mul]
  apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hW) (norm_pos_iff.mpr hG))).mpr
  have hm := mul_le_mul_of_nonneg_left hnormal (mul_nonneg (norm_nonneg W) hB)
  nlinarith

theorem relative_left_annulus_budget (t : ℝ) (c₀ : ℂ) (hcenter : c₀.im ≤ 0) (ht : 1 ≤ t) (hx : 10000 ≤ ‖c₀‖)
    (w v : ℂ) (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*c₀))
    (hp : 10000*(t*(‖w‖+1)^5+1) ≤ ‖c₀‖) (hv : ‖v-w‖ ≤ 1/‖c₀‖)
    (z : ℂ) (hz : complexSlope 3 t v= -(Complex.I*z))
    (R : ℝ) (hR0 : 0 < R) (hR1 : R ≤ 1)
    (hsmall : 30005*Real.exp (-4*w.re+4) ≤ (t*w.re^5/4096)*R) :
    ‖(∫ s : ℝ in -1..-R, weight 3 t z (v+(s : ℂ)))/
      (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))‖ ≤
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
  have h35 : w.re^3 ≤ w.re^5 := pow_le_pow_right₀ (by linarith : 1 ≤ w.re) (by norm_num)
  have ht5 : w.re^5 ≤ t*w.re^5 := by nlinarith [pow_nonneg (by linarith : 0 ≤ w.re) 5]
  have hwt : w.re^3 ≤ t*w.re^5 := h35.trans ht5
  have hm := mul_le_mul_of_nonneg_right hwt (sq_nonneg R)
  have he : Real.exp (-(t*w.re^5/4096)*R^2) ≤ Real.exp (-(w.re^3/4096)*R^2) :=
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

theorem uniform_relative_left_annulus (R η : ℝ) (hR0 : 0 < R)
    (hR1 : R ≤ 1) (hη : 0 < η) :
    ∀ᶠ N : ℝ in atTop, ∀ c₀ : ℂ, c₀.im ≤ 0 → ‖c₀‖=N → ∀ t : ℝ, 1 ≤ t → ∀ w v : ℂ,
      120020 ≤ w.re → |w.im| ≤ 1/2 → 10000*(t*(‖w‖+1)^5+1) ≤ ‖c₀‖ →
      modelDerivative 3 t w= -(Complex.I*c₀) → ‖v-w‖ ≤ 1/‖c₀‖ →
      ∀ z : ℂ, complexSlope 3 t v= -(Complex.I*z) →
      ‖(∫ s : ℝ in -1..-R, weight 3 t z (v+(s : ℂ)))/
        (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))‖ ≤ η := by
  have hlim : Tendsto (fun a : ℝ => 100*rightBudget (R/16) a) atTop (nhds 0) := by
    simpa only [mul_zero] using (rightBudget_tendsto_zero (R/16) (by positivity)).const_mul (100 : ℝ)
  obtain ⟨A,hA⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hη))
  filter_upwards [eventually_ge_atTop (10000 : ℝ),
    eventually_ge_atTop (100000000*Real.exp (4*A)),eventually_ge_atTop (100000000/R)] with N hx hxA hxR
  intro c₀ hcenter hn t ht w v hr hi hp hs hv z hz
  subst N
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
  have h35 : w.re^3 ≤ w.re^5 := pow_le_pow_right₀ (by linarith : 1 ≤ w.re) (by norm_num)
  have ht5 : w.re^5 ≤ t*w.re^5 := by nlinarith [pow_nonneg (by linarith : 0 ≤ w.re) 5]
  have hwt : w.re^3 ≤ t*w.re^5 := h35.trans ht5
  have hsmall : 30005*Real.exp (-4*w.re+4) ≤ (t*w.re^5/4096)*R := by
    have hm := mul_le_mul_of_nonneg_right (by linarith : 1 ≤ t*w.re^5/4096) hR0.le
    linarith
  exact (relative_left_annulus_budget t c₀ hcenter ht hx w v hr hi hs hp hv z hz R hR0 hR1 hsmall).trans (hA w.re hw).le


end OperatorDerivativeRewrite.Foundation.RiemannSixthComplexLeftAnnulus
