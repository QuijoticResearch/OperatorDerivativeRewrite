import Foundation.RiemannSixthFarGaussianFixed
import Foundation.RiemannEvenWeightEnvelope
/-! Genuine actual A6 right horizontal tails, with fifth-power Gaussian
decay. Existing degree-independent scalar tail budgets are reused. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthFarRightTail
open RiemannSixthFarGaussianFixed RiemannSixthFarGaussianLimit RiemannSixthFarGaussianLocal
open RiemannSixthFarRemainder RiemannSixthFarCorrection RiemannSixthFarSignedIntegral
open RiemannEvenModelPhase RiemannEvenSaddleBranch RiemannEvenComplexWeight
open RiemannThetaComplexKernel
open RiemannEvenWeightEnvelope (horizontal_exp_real_identity)
open RiemannQuarticFarRightTail (rightBudget rightBudget_tendsto_zero)

theorem actual_weight_model_envelope (t : ℝ) (z v u : ℂ)
    (hv : 0 ≤ v.re) (hEv : 1 ≤ (Complex.exp (4*v)).re)
    (hq : 0 ≤ (v+u).re) (hEq : 1/2 ≤ (Complex.exp (4*(v+u))).re) :
    ‖weight 3 t z (v+u)‖ ≤ 1000*‖weight 3 t z v‖*Real.exp (leadingPhase t z v u).re := by
  have h := RiemannEvenWeightEnvelope.actual_weight_model_envelope 3 t z v u hv hEv hq hEq
  have hid : modelPhase 3 t (v+u)-modelPhase 3 t v+Complex.I*z*u = leadingPhase t z v u := by
    unfold modelPhase leadingPhase
    ring
  simpa only [hid] using h

theorem right_model_curvature (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 4096 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
    (hp : 6*t*‖w‖^5+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x) (s : ℝ) (hs0 : 0 ≤ s) :
    (deriv (modelDerivative 3 t) (v+(s : ℂ))).re ≤ -(t*w.re^5)/4 := by
  let q := v+(s : ℂ)
  have hd := horizontal_neighbor_domain t x ht hx w v (by linarith) hi hs hp hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hd
  have ht0 : 0 ≤ t := by linarith
  have hr0 : 0 ≤ w.re := by linarith
  have hx0 : 0 < x := by linarith
  have hvsmall : ‖v-w‖ ≤ 1/8 := hv.trans ((div_le_iff₀ hx0).mpr (by linarith))
  have hwNorm := Complex.norm_le_abs_re_add_abs_im w
  rw [abs_of_nonneg hr0] at hwNorm
  have htri := norm_add_le (v-w) w
  rw [sub_add_cancel] at htri
  have hvnorm : ‖v‖+1 ≤ 2*w.re := by linarith
  have he : 1+s ≤ Real.exp s := by simpa only [add_comm] using Real.add_one_le_exp s
  have hmul := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ ‖v‖+1)
  have hqtri := norm_add_le v (s : ℂ)
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs0] at hqtri
  have hvex := mul_le_mul_of_nonneg_right hvnorm (Real.exp_pos s).le
  have hq : ‖q‖ ≤ 2*w.re*Real.exp s := by
    dsimp [q]
    nlinarith [mul_nonneg (norm_nonneg v) hs0]
  have hqpow := pow_le_pow_left₀ (norm_nonneg q) hq 4
  have hexp4 : (Real.exp s)^4 = Real.exp (4*s) := by
    simpa using (Real.exp_nat_mul s 4).symm
  rw [mul_pow,mul_pow,hexp4] at hqpow
  norm_num at hqpow
  have hpower : 1920*w.re^4 ≤ w.re^5 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ w.re-1920) (pow_nonneg hr0 4)]
  have hpowert := mul_le_mul_of_nonneg_right hpower (by positivity : 0 ≤ t*Real.exp (4*s))
  have hreal := Complex.re_le_norm (q^4)
  rw [norm_pow] at hreal
  have hrealm := mul_le_mul_of_nonneg_left hreal (by positivity : 0 ≤ 30*t)
  have hnormt := mul_le_mul_of_nonneg_left hqpow (by positivity : 0 ≤ 30*t)
  have hEid := horizontal_exp_real_identity v s
  have hElow := mul_le_mul_of_nonneg_left hd.2.2.1 (Real.exp_pos (4*s)).le
  rw [← hEid] at hElow
  have hE0 : 0 ≤ (Complex.exp (4*q)).re := by
    change 0 ≤ (Complex.exp (4*(v+(s : ℂ)))).re
    rw [hEid]
    exact mul_nonneg (Real.exp_pos _).le (by linarith [hd.2.1])
  have hpi := mul_le_mul_of_nonneg_right Real.pi_gt_three.le hE0
  have hexp1 : 1 ≤ Real.exp (4*s) := Real.one_le_exp (by linarith)
  have hlast := mul_le_mul_of_nonneg_left hexp1 (by positivity : 0 ≤ t*w.re^5/4)
  have hid : (deriv (modelDerivative 3 t) q).re =
      30*t*(q^4).re-16*Real.pi*(Complex.exp (4*q)).re := by
    rw [(modelDerivative_hasDerivAt 3 t q).deriv]
    norm_num [Complex.mul_re,Complex.sub_re]
  change (deriv (modelDerivative 3 t) q).re ≤ _
  rw [hid]
  change Real.exp (4*s)*(t*w.re^5/64) ≤ (Complex.exp (4*q)).re at hElow
  nlinarith [hElow]

theorem right_phase_quadratic_bound (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 4096 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
    (hp : 6*t*‖w‖^5+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hz : complexSlope 3 t v= -(Complex.I*z)) (s : ℝ) (hs0 : 0 ≤ s) :
    (leadingPhase t z v (s : ℂ)).re ≤
      (30005*Real.exp (-4*w.re+4))*s-(t*w.re^5/8)*s^2 := by
  let c := t*w.re^5/8
  let f := fun a : ℝ => (leadingPhase t z v (a : ℂ)).re+c*a^2
  let f1 := fun a : ℝ => (modelDerivative 3 t (v+(a : ℂ))+Complex.I*z).re+2*c*a
  let f2 := fun a : ℝ => (deriv (modelDerivative 3 t) (v+(a : ℂ))).re+2*c
  have h1 (a : ℝ) : HasDerivAt f (f1 a) a := by
    have hd := ((leadingPhase_hasDerivAt t z v (a : ℂ)).real_of_complex).add
      (((hasDerivAt_id a).pow 2).const_mul c)
    convert hd using 1
    · funext y; rfl
    · dsimp [f1]
      ring
  have h2 (a : ℝ) : HasDerivAt f1 (f2 a) a := by
    have hm := modelDerivative_hasDerivAt 3 t (v+(a : ℂ))
    have hc := (hm.comp (a : ℂ) ((hasDerivAt_id (a : ℂ)).const_add v)).add_const (Complex.I*z)
    have hc' : HasDerivAt (fun u : ℂ => modelDerivative 3 t (v+u)+Complex.I*z)
        (deriv (modelDerivative 3 t) (v+(a : ℂ))) (a : ℂ) := by
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
    have h := right_model_curvature t x ht hx w v hr hi hs hp hv a ha0
    dsimp [f2,c]
    linarith
  have htangent : f s ≤ f1 0*s := by
    rcases eq_or_lt_of_le hs0 with heq | hpos
    · subst s
      simp [hf0]
    · have h := hc.slope_le_of_hasDerivAt (show (0 : ℝ) ∈ Ici (0 : ℝ) from by simp) hs0 hpos (h1 0)
      rw [slope_def_field,hf0,sub_zero,sub_zero] at h
      exact (div_le_iff₀ hpos).mp h
  have he := horizontal_neighbor_error t x ht hx w v (by linarith) hi hs hp hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at he
  have hid : f1 0= -(complexSlope 3 t v-modelDerivative 3 t v).re := by
    have hid : modelDerivative 3 t v+Complex.I*z= -(complexSlope 3 t v-modelDerivative 3 t v) := by rw [hz]; ring
    simp only [f1,Complex.ofReal_zero,add_zero,mul_zero,hid,Complex.neg_re]
  have hf1 : f1 0 ≤ 30005*Real.exp (-4*w.re+4) := by
    rw [hid]
    exact (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans he)
  have hm := mul_le_mul_of_nonneg_right hf1 hs0
  dsimp [f,c] at htangent
  linarith

theorem actual_right_gaussian_envelope (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 4096 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
    (hp : 6*t*‖w‖^5+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hz : complexSlope 3 t v= -(Complex.I*z))
    (R : ℝ) (hR : 0 < R) (hsmall : 30005*Real.exp (-4*w.re+4) ≤ (t*w.re^5/16)*R)
    (s : ℝ) (hsR : R ≤ s) :
    ‖weight 3 t z (v+(s : ℂ))‖ ≤
      1000*‖weight 3 t z v‖*Real.exp (-(t*w.re^5/16)*s^2) := by
  have hs0 : 0 ≤ s := hR.le.trans hsR
  have hd := horizontal_neighbor_domain t x ht hx w v (by linarith) hi hs hp hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hd
  have hE : 1 ≤ (Complex.exp (4*(v+(s : ℂ)))).re := by
    rw [horizontal_exp_real_identity]
    have he : 1 ≤ Real.exp (4*s) := Real.one_le_exp (by linarith)
    nlinarith [hd.2.1]
  have hratio := actual_weight_model_envelope t z v (s : ℂ) hd.1 hd.2.1
    (by simp only [Complex.add_re,Complex.ofReal_re]; linarith [hd.1]) (by linarith)
  have hphase := right_phase_quadratic_bound t x ht hx w v hr hi hs hp hv z hz s hs0
  have hc : 0 ≤ t*w.re^5/16 := by positivity
  have hm := mul_le_mul_of_nonneg_left hsR hc
  have hm2 := mul_le_mul_of_nonneg_right hsmall hs0
  have hm3 := mul_le_mul_of_nonneg_right hm hs0
  have hexp : (leadingPhase t z v (s : ℂ)).re ≤ -(t*w.re^5/16)*s^2 := by nlinarith
  exact hratio.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity))


theorem actual_right_tail_bound (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 4096 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
    (hp : 6*t*‖w‖^5+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hz : complexSlope 3 t v= -(Complex.I*z))
    (R : ℝ) (hR : 0 < R) (hsmall : 30005*Real.exp (-4*w.re+4) ≤ (t*w.re^5/16)*R) :
    IntegrableOn (fun s : ℝ => weight 3 t z (v+(s : ℂ))) (Ioi R) ∧
    ‖∫ s : ℝ in Ioi R, weight 3 t z (v+(s : ℂ))‖ ≤
      1000*‖weight 3 t z v‖*Real.exp (-(t*w.re^5/16)*R^2)/(2*(t*w.re^5/16)*R) := by
  let c := t*w.re^5/16
  let A := 1000*‖weight 3 t z v‖
  let f := fun s : ℝ => weight 3 t z (v+(s : ℂ))
  have hc : 0 < c := by dsimp [c]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hg : IntegrableOn (fun s : ℝ => A*Real.exp (-c*s^2)) (Ioi R) :=
    ((integrable_exp_neg_mul_sq hc).const_mul A).integrableOn
  have hbound (s : ℝ) (hsR : s ∈ Ioi R) : ‖f s‖ ≤ A*Real.exp (-c*s^2) :=
    actual_right_gaussian_envelope t x ht hx w v hr hi hs hp hv z hz R hR hsmall s hsR.le
  have hd := horizontal_neighbor_domain t x ht hx w v (by linarith) hi hs hp hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hd
  have hfc : ContinuousOn f (Ioi R) := by
    intro s hsR
    have hE : 0 < (Complex.exp (4*(v+(s : ℂ)))).re := by
      rw [horizontal_exp_real_identity]
      exact mul_pos (Real.exp_pos _) (by linarith [hd.2.1])
    have hk := kernelComplex_analyticAt (v+(s : ℂ)) hE
    have hw : AnalyticAt ℂ (weight 3 t z) (v+(s : ℂ)) := by
      unfold weight
      apply AnalyticAt.mul
      · fun_prop
      · exact hk
    have hc' : ContinuousAt f s := ContinuousAt.comp (g := weight 3 t z)
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

theorem relative_actual_right_tail_bound (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x)
    (w v : ℂ) (hr : 4096 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
    (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hz : complexSlope 3 t v= -(Complex.I*z))
    (R : ℝ) (hR : 0 < R) (hsmall : 30005*Real.exp (-4*w.re+4) ≤ (t*w.re^5/16)*R) :
    ‖(∫ s : ℝ in Ioi R, weight 3 t z (v+(s : ℂ)))/
      (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))‖ ≤
      2000*Real.sqrt x*Real.exp (-(t*w.re^5/16)*R^2)/(2*(t*w.re^5/16)*R) := by
  have ht0 : 0 ≤ t := by linarith
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 5
  have hmul := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 6*t*‖w‖^5+9 ≤ x := by nlinarith [pow_nonneg (norm_nonneg w) 5]
  have he := (actual_right_tail_bound t x ht (by linarith) w v hr hi hs hp0 hv z hz R hR hsmall).2
  let W := weight 3 t z v
  let G := ∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)
  let B := 1000*Real.exp (-(t*w.re^5/16)*R^2)/(2*(t*w.re^5/16)*R)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hnormal := gaussian_normalization_lower t x ht hx w v hr hi hp hs hv
  change 1 ≤ 2*Real.sqrt x*‖G‖ at hnormal
  have hG : G ≠ 0 := by intro h; norm_num [h] at hnormal
  have hd := horizontal_neighbor_domain t x ht (by linarith) w v (by linarith) hi hs hp0 hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hd
  have hW : W ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (kernel_ne_zero v hd.1 hd.2.1)
  have hnum : ‖∫ s : ℝ in Ioi R, weight 3 t z (v+(s : ℂ))‖ ≤ ‖W‖*B := by
    apply he.trans_eq
    dsimp [W,B]
    ring
  have htarget : 2000*Real.sqrt x*Real.exp (-(t*w.re^5/16)*R^2)/(2*(t*w.re^5/16)*R)=2*Real.sqrt x*B := by
    dsimp [B]
    ring
  rw [htarget]
  change ‖(∫ s : ℝ in Ioi R, weight 3 t z (v+(s : ℂ)))/(W*G)‖ ≤ _
  rw [norm_div,norm_mul]
  apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hW) (norm_pos_iff.mpr hG))).mpr
  have hm := mul_le_mul_of_nonneg_left hnormal (mul_nonneg (norm_nonneg W) hB)
  nlinarith


private theorem model_frequency_exp_bound (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x)
    (w : ℂ) (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ))) : x ≤ 32*Real.exp (4*w.re) := by
  have ht0 : 0 ≤ t := by linarith
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 5
  have hm := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 6*t*‖w‖^5+9 ≤ x/2 := by nlinarith [pow_nonneg (norm_nonneg w) 5]
  exact RiemannEvenWeightEnvelope.model_frequency_exp_bound 3 t x ht0 (by linarith) w
    (by convert hp0 using 1 <;> norm_num) hs

theorem relative_right_tail_budget (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x)
    (w v : ℂ) (hr : 4096 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
    (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hz : complexSlope 3 t v= -(Complex.I*z))
    (R : ℝ) (hR : 0 < R) (hsmall : 30005*Real.exp (-4*w.re+4) ≤ (t*w.re^5/16)*R) :
    ‖(∫ s : ℝ in Ioi R, weight 3 t z (v+(s : ℂ)))/
      (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))‖ ≤
      rightBudget R w.re := by
  have h := relative_actual_right_tail_bound t x ht hx w v hr hi hs hp hv z hz R hR hsmall
  have hx0 : 0 < x := by linarith
  have hfreq := model_frequency_exp_bound t x ht hx w hp hs
  have hsqrt : Real.sqrt x ≤ 8*Real.exp (2*w.re) := by
    have hsq := Real.sq_sqrt hx0.le
    have hE : (Real.exp (2*w.re))^2=Real.exp (4*w.re) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    nlinarith [Real.sqrt_nonneg x,Real.exp_pos (2*w.re),Real.exp_pos (4*w.re)]
  have hw3 : 16 ≤ w.re^3 := by
    have hw2 : 1 ≤ w.re^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hw2 (by linarith : 0 ≤ w.re)]
  have h35 : w.re^3 ≤ w.re^5 := pow_le_pow_right₀ (by linarith : 1 ≤ w.re) (by norm_num)
  have hwt : w.re^3 ≤ t*w.re^5 := h35.trans (by nlinarith [pow_nonneg (by linarith : 0 ≤ w.re) 5])
  have hc : 1 ≤ t*w.re^5/16 := by linarith
  have hden : R ≤ 2*(t*w.re^5/16)*R := by nlinarith
  have hpow := mul_le_mul_of_nonneg_right hwt (sq_nonneg R)
  have he : Real.exp (-(t*w.re^5/16)*R^2) ≤ Real.exp (-(w.re^3/16)*R^2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  apply h.trans
  calc
    _ ≤ (2000*Real.sqrt x*Real.exp (-(t*w.re^5/16)*R^2))/R :=
      div_le_div_of_nonneg_left (by positivity) hR hden
    _ ≤ (2000*(8*Real.exp (2*w.re))*Real.exp (-(w.re^3/16)*R^2))/R := by
      apply div_le_div_of_nonneg_right _ hR.le
      exact mul_le_mul (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) he (by positivity) (by positivity)
    _ = rightBudget R w.re := by
      dsimp [rightBudget]
      rw [show 2*w.re-(R^2/16)*w.re^3=2*w.re+(-(w.re^3/16)*R^2) by ring,Real.exp_add]
      ring

theorem eventually_uniform_relative_right_tail (R η : ℝ) (hR : 0 < R) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, 1 ≤ t → ∀ w v : ℂ,
      4096 ≤ w.re → |w.im| ≤ 1/2 → 10000*(t*(‖w‖+1)^5+1) ≤ x →
      modelDerivative 3 t w= -(Complex.I*(x : ℂ)) → ‖v-w‖ ≤ 1/x →
      ∀ z : ℂ, complexSlope 3 t v= -(Complex.I*z) →
      IntegrableOn (fun s : ℝ => weight 3 t z (v+(s : ℂ))) (Ioi R) ∧
        ‖(∫ s : ℝ in Ioi R, weight 3 t z (v+(s : ℂ)))/
          (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))‖ ≤ η := by
  obtain ⟨A,hA⟩ := eventually_atTop.mp ((rightBudget_tendsto_zero R hR).eventually (gt_mem_nhds hη))
  filter_upwards [eventually_ge_atTop (10000 : ℝ),
    eventually_ge_atTop (32*Real.exp (4*A)),eventually_ge_atTop (100000000/R)] with x hx hxA hxR
  intro t ht w v hr hi hp hs hv z hz
  have hfreq := model_frequency_exp_bound t x ht hx w hp hs
  have hw : A ≤ w.re := by
    have he : Real.exp (4*A) ≤ Real.exp (4*w.re) := by linarith
    have he' := Real.exp_le_exp.mp he
    linarith
  have he := arithmetic_error_frequency_bound t x ht hx w hp hs
  have hx0 : 0 < x := by linarith
  have heR : 100000000/x ≤ R := by
    apply (div_le_iff₀ hx0).mpr
    have hm := (div_le_iff₀ hR).mp hxR
    nlinarith
  have hw3 : 16 ≤ w.re^3 := by
    have hw2 : 1 ≤ w.re^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hw2 (by linarith : 0 ≤ w.re)]
  have h35 : w.re^3 ≤ w.re^5 := pow_le_pow_right₀ (by linarith : 1 ≤ w.re) (by norm_num)
  have hwt : w.re^3 ≤ t*w.re^5 := h35.trans (by nlinarith [pow_nonneg (by linarith : 0 ≤ w.re) 5])
  have hsmall : 30005*Real.exp (-4*w.re+4) ≤ (t*w.re^5/16)*R := by
    have hm := mul_le_mul_of_nonneg_right (by linarith : 1 ≤ t*w.re^5/16) hR.le
    linarith
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 5
  have hm := mul_le_mul_of_nonneg_left hpow (by linarith : 0 ≤ t)
  have hp0 : 6*t*‖w‖^5+9 ≤ x := by nlinarith [pow_nonneg (norm_nonneg w) 5]
  exact ⟨(actual_right_tail_bound t x ht (by linarith) w v hr hi hs hp0 hv z hz R hR hsmall).1,
    (relative_right_tail_budget t x ht hx w v hr hi hs hp hv z hz R hR hsmall).trans (hA w.re hw).le⟩

theorem exists_uniform_actual_fixed_gaussian_right_tail (R : ℝ)
    (hR0 : 0 < R) (hR : R ≤ 1/8192) :
    ∃ K : ℝ, 0 < K ∧ ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ t u x : ℝ,
      1 ≤ t → 120021 ≤ u → RiemannEvenRealSaddle.phaseSlope 3 t u = 0 →
      max X (K*RiemannQuarticTransitionSaddle.realScale u) ≤ x →
      ∃ w : ℂ, 10000 ≤ x ∧ 120020 ≤ w.re ∧ |w.im| ≤ 1/2 ∧
        10000*(t*(‖w‖+1)^5+1) ≤ x ∧ modelDerivative 3 t w = -(Complex.I*(x : ℂ)) ∧
        ∀ z : ℂ, ‖z-(x : ℂ)‖ ≤ 1 → ∃ v : ℂ,
          v ∈ closedBall w (1/x) ∧ complexSlope 3 t v = -(Complex.I*z) ∧
          1 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ weight 3 t z v ≠ 0 ∧
          weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)) ≠ 0 ∧
          ‖(∫ s : ℝ in -R..R, weight 3 t z (v+(s : ℂ)))/
            (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))-1‖ ≤ η ∧
          IntegrableOn (fun s : ℝ => weight 3 t z (v+(s : ℂ))) (Ioi R) ∧
          ‖(∫ s : ℝ in Ioi R, weight 3 t z (v+(s : ℂ)))/
            (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))‖ ≤ η := by
  obtain ⟨K,hK,hC⟩ := exists_uniform_actual_fixed_gaussian R hR0 hR
  refine ⟨K,hK,?_⟩
  intro η hη
  obtain ⟨XC,hXC⟩ := hC η hη
  obtain ⟨XT,hXT⟩ := eventually_atTop.mp (eventually_uniform_relative_right_tail R η hR0 hη)
  refine ⟨max XC XT,?_⟩
  intro t u x ht hu hstat hx
  have hxC : max XC (K*RiemannQuarticTransitionSaddle.realScale u) ≤ x := by
    exact max_le ((le_max_left XC XT).trans ((le_max_left _ _).trans hx))
      ((le_max_right _ _).trans hx)
  have hxT : XT ≤ x := (le_max_right XC XT).trans ((le_max_left _ _).trans hx)
  obtain ⟨w,hxlarge,hr,hi,hp,hs,hroots⟩ := hXC t u x ht hu hstat hxC
  refine ⟨w,hxlarge,hr,hi,hp,hs,?_⟩
  intro z hz
  obtain ⟨v,hv,hvstat,hvre,hvim,hW,hD,hcentral⟩ := hroots z hz
  have hvdist : ‖v-w‖ ≤ 1/x := by simpa only [mem_closedBall,dist_eq_norm] using hv
  have htail := hXT x hxT t ht w v (by linarith) hi hp hs hvdist z hvstat
  exact ⟨v,hv,hvstat,hvre,hvim,hW,hD,hcentral,htail⟩

end OperatorDerivativeRewrite.Foundation.RiemannSixthFarRightTail
