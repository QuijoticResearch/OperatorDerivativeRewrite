import Foundation.RiemannQuarticFarGaussianFixed
import Foundation.RiemannQuarticNaturalContour
/-! Right-hand actual contour tails at corrected far Xi saddles.
Horizontal model curvature and existing arithmetic kernel envelopes control
all positive displacements, without a wide actual complex neighborhood. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticFarRightTail
open RiemannQuarticFarGaussianFixed RiemannQuarticFarGaussianLimit RiemannQuarticFarGaussianLocal
open RiemannQuarticFarRemainder RiemannQuarticFarCorrection RiemannQuarticFarSignedIntegral
open RiemannQuarticSaddleTheta RiemannQuarticSaddleBranch RiemannQuarticFrequencyBranch
open RiemannThetaComplexKernel RiemannQuarticNaturalContour RiemannThetaDerivativeBounds
open RiemannQuarticFarModelSaddle

theorem actual_weight_model_envelope (t : ℝ) (z v u : ℂ)
    (hv : 0 ≤ v.re) (hEv : 1 ≤ (Complex.exp (4*v)).re)
    (hq : 0 ≤ (v+u).re) (hEq : 1/2 ≤ (Complex.exp (4*(v+u))).re) :
    ‖saddleWeight t z (v+u)‖ ≤
      1000*‖saddleWeight t z v‖*Real.exp (leadingPhase t z v u).re := by
  let P := fun q : ℂ => (t : ℂ)*q^4+Complex.I*z*q+9*q-(Real.pi : ℂ)*Complex.exp (4*q)
  have hP (q : ℂ) : Real.exp (P q).re=
      Real.exp ((t : ℂ)*q^4+Complex.I*z*q).re *
        Real.exp (9*q.re)*Real.exp (-Real.pi*(Complex.exp (4*q)).re) := by
    have hid : (P q).re=((t : ℂ)*q^4+Complex.I*z*q).re+9*q.re+
        (-Real.pi*(Complex.exp (4*q)).re) := by
      dsimp [P]
      norm_num [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im]
      <;> ring
    rw [hid,Real.exp_add,Real.exp_add]
  have hupp := mul_le_mul_of_nonneg_left (kernel_norm_bound (v+u) hq hEq)
    (Real.exp_pos ((t : ℂ)*(v+u)^4+Complex.I*z*(v+u)).re).le
  have hlow := mul_le_mul_of_nonneg_left (kernel_norm_lower v hv hEv)
    (Real.exp_pos ((t : ℂ)*v^4+Complex.I*z*v).re).le
  have hnorm (q : ℂ) : ‖saddleWeight t z q‖=
      Real.exp ((t : ℂ)*q^4+Complex.I*z*q).re*‖kernelComplex q‖ := by
    rw [saddleWeight,norm_mul,Complex.norm_exp]
  rw [← hnorm (v+u)] at hupp
  rw [← hnorm v] at hlow
  have hupp' : ‖saddleWeight t z (v+u)‖ ≤ 5676*Real.exp (P (v+u)).re := by
    rw [hP]
    nlinarith
  have hlow' : (21/8 : ℝ)*Real.pi*Real.exp (P v).re ≤ ‖saddleWeight t z v‖ := by
    rw [hP]
    nlinarith
  have hratio : 5676*Real.exp (P v).re ≤ 1000*‖saddleWeight t z v‖ := by
    have hm := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (Real.exp_pos (P v).re).le
    nlinarith [Real.exp_pos (P v).re]
  have hid : P (v+u)=P v+leadingPhase t z v u := by dsimp [P,leadingPhase]; ring
  rw [hid,Complex.add_re,Real.exp_add] at hupp'
  have hm := mul_le_mul_of_nonneg_right hratio (Real.exp_pos (leadingPhase t z v u).re).le
  nlinarith

theorem right_model_curvature (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (hp : 4*t*‖w‖^3+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x) (s : ℝ) (hs0 : 0 ≤ s) :
    (deriv (modelDerivative t) (v+(s : ℂ))).re ≤ -(t*w.re^3)/4 := by
  have hd := horizontal_neighbor_domain t x ht hx w v (by linarith) hi hs hp hv 0 (by norm_num)
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


theorem right_phase_quadratic_bound (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (hp : 4*t*‖w‖^3+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x)
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

theorem actual_right_gaussian_envelope (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (hp : 4*t*‖w‖^3+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hz : complexSlope t v= -(Complex.I*z))
    (R : ℝ) (hR : 0 < R) (hsmall : 30005*Real.exp (-4*w.re+4) ≤ (t*w.re^3/16)*R)
    (s : ℝ) (hsR : R ≤ s) :
    ‖saddleWeight t z (v+(s : ℂ))‖ ≤
      1000*‖saddleWeight t z v‖*Real.exp (-(t*w.re^3/16)*s^2) := by
  have hs0 : 0 ≤ s := hR.le.trans hsR
  have hd := horizontal_neighbor_domain t x ht hx w v (by linarith) hi hs hp hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hd
  have hE : 1 ≤ (Complex.exp (4*(v+(s : ℂ)))).re := by
    rw [horizontal_exp_identity]
    have he : 1 ≤ Real.exp (4*s) := Real.one_le_exp (by linarith)
    nlinarith [hd.2.1]
  have hratio := actual_weight_model_envelope t z v (s : ℂ) hd.1 hd.2.1
    (by simp only [Complex.add_re,Complex.ofReal_re]; linarith [hd.1]) (by linarith)
  have hphase := right_phase_quadratic_bound t x ht hx w v hr hi hs hp hv z hz s hs0
  have hc : 0 ≤ t*w.re^3/16 := by positivity
  have hm := mul_le_mul_of_nonneg_left hsR hc
  have hm2 := mul_le_mul_of_nonneg_right hsmall hs0
  have hm3 := mul_le_mul_of_nonneg_right hm hs0
  have hexp : (leadingPhase t z v (s : ℂ)).re ≤ -(t*w.re^3/16)*s^2 := by nlinarith
  exact hratio.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity))


theorem actual_right_tail_bound (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (hp : 4*t*‖w‖^3+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x)
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
    actual_right_gaussian_envelope t x ht hx w v hr hi hs hp hv z hz R hR hsmall s hsR.le
  have hd := horizontal_neighbor_domain t x ht hx w v (by linarith) hi hs hp hv 0 (by norm_num)
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

theorem relative_actual_right_tail_bound (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x)
    (w v : ℂ) (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hz : complexSlope t v= -(Complex.I*z))
    (R : ℝ) (hR : 0 < R) (hsmall : 30005*Real.exp (-4*w.re+4) ≤ (t*w.re^3/16)*R) :
    ‖(∫ s : ℝ in Ioi R, saddleWeight t z (v+(s : ℂ)))/
      (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤
      2000*Real.sqrt x*Real.exp (-(t*w.re^3/16)*R^2)/(2*(t*w.re^3/16)*R) := by
  have ht0 : 0 ≤ t := by linarith
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hmul := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 4*t*‖w‖^3+9 ≤ x := by nlinarith [pow_nonneg (norm_nonneg w) 3]
  have he := (actual_right_tail_bound t x ht (by linarith) w v hr hi hs hp0 hv z hz R hR hsmall).2
  let W := saddleWeight t z v
  let G := ∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)
  let B := 1000*Real.exp (-(t*w.re^3/16)*R^2)/(2*(t*w.re^3/16)*R)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hnormal := gaussian_normalization_lower t x ht hx w v hr hi hp hs hv
  change 1 ≤ 2*Real.sqrt x*‖G‖ at hnormal
  have hG : G ≠ 0 := by intro h; norm_num [h] at hnormal
  have hd := horizontal_neighbor_domain t x ht (by linarith) w v (by linarith) hi hs hp0 hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hd
  have hW : W ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (kernel_ne_zero v hd.1 hd.2.1)
  have hnum : ‖∫ s : ℝ in Ioi R, saddleWeight t z (v+(s : ℂ))‖ ≤ ‖W‖*B := by
    apply he.trans_eq
    dsimp [W,B]
    ring
  have htarget : 2000*Real.sqrt x*Real.exp (-(t*w.re^3/16)*R^2)/(2*(t*w.re^3/16)*R)=2*Real.sqrt x*B := by
    dsimp [B]
    ring
  rw [htarget]
  change ‖(∫ s : ℝ in Ioi R, saddleWeight t z (v+(s : ℂ)))/(W*G)‖ ≤ _
  rw [norm_div,norm_mul]
  apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hW) (norm_pos_iff.mpr hG))).mpr
  have hm := mul_le_mul_of_nonneg_left hnormal (mul_nonneg (norm_nonneg W) hB)
  nlinarith


private theorem model_frequency_exp_bound (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x)
    (w : ℂ) (hp : 100*(t*(‖w‖+1)^3+1) ≤ x)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ))) :
    x ≤ 32*Real.exp (4*w.re) := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 < x := by linarith
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hm := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 4*t*‖w‖^3+9 ≤ x/2 := by nlinarith [pow_nonneg (norm_nonneg w) 3]
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
  have hE : ‖Complex.exp (4*w)‖=Real.exp (4*w.re) := by rw [Complex.norm_exp]; simp [Complex.mul_re]
  rw [hE] at htri hpi
  nlinarith

def rightBudget (R a : ℝ) : ℝ := (16000/R)*Real.exp (2*a-(R^2/16)*a^3)

theorem rightBudget_tendsto_zero (R : ℝ) (hR : 0 < R) :
    Tendsto (rightBudget R) atTop (nhds 0) := by
  let c := R^2/16
  have hc : 0 < c := by dsimp [c]; positivity
  have hu : Tendsto (fun a : ℝ => (16000/R)*Real.exp (-a)) atTop (nhds 0) := by
    simpa only [mul_zero,Function.comp_def] using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul (16000/R)
  change Tendsto (fun a : ℝ => (16000/R)*Real.exp (2*a-c*a^3)) atTop (nhds 0)
  apply squeeze_zero' (Eventually.of_forall (fun a => by positivity)) _ hu
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    (tendsto_pow_atTop two_ne_zero).eventually (eventually_ge_atTop (3/c))] with a ha hsq
  have hcsq : 3 ≤ c*a^2 := by
    have h := (div_le_iff₀ hc).mp hsq
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hcsq ha
  have hexp : 2*a-c*a^3 ≤ -a := by nlinarith
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)

theorem relative_right_tail_budget (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x)
    (w v : ℂ) (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hz : complexSlope t v= -(Complex.I*z))
    (R : ℝ) (hR : 0 < R) (hsmall : 30005*Real.exp (-4*w.re+4) ≤ (t*w.re^3/16)*R) :
    ‖(∫ s : ℝ in Ioi R, saddleWeight t z (v+(s : ℂ)))/
      (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤
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
  have hwt : w.re^3 ≤ t*w.re^3 := by nlinarith
  have hc : 1 ≤ t*w.re^3/16 := by linarith
  have hden : R ≤ 2*(t*w.re^3/16)*R := by nlinarith
  have hpow := mul_le_mul_of_nonneg_right hwt (sq_nonneg R)
  have he : Real.exp (-(t*w.re^3/16)*R^2) ≤ Real.exp (-(w.re^3/16)*R^2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  apply h.trans
  calc
    _ ≤ (2000*Real.sqrt x*Real.exp (-(t*w.re^3/16)*R^2))/R :=
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
      64 ≤ w.re → |w.im| ≤ 1/2 → 100*(t*(‖w‖+1)^3+1) ≤ x →
      modelDerivative t w= -(Complex.I*(x : ℂ)) → ‖v-w‖ ≤ 1/x →
      ∀ z : ℂ, complexSlope t v= -(Complex.I*z) →
      ‖(∫ s : ℝ in Ioi R, saddleWeight t z (v+(s : ℂ)))/
        (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤ η := by
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
  have hwt : w.re^3 ≤ t*w.re^3 := by nlinarith
  have hsmall : 30005*Real.exp (-4*w.re+4) ≤ (t*w.re^3/16)*R := by
    have hm := mul_le_mul_of_nonneg_right (by linarith : 1 ≤ t*w.re^3/16) hR.le
    linarith
  exact (relative_right_tail_budget t x ht hx w v hr hi hs hp hv z hz R hR hsmall).trans (hA w.re hw).le

end OperatorDerivativeRewrite.Foundation.RiemannQuarticFarRightTail
