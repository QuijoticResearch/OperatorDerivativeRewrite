import Foundation.RiemannSixthTransitionGaussian
import Foundation.RiemannSixthFarLeftAnnulus
import Foundation.RiemannQuarticTransitionContour
/-! Actual outer horizontal contour control on the transition scales.
The central signed approximation is supplemented by actual Gaussian domination.
Compact contour pieces and paired-channel zero conclusions remain separate. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthTransitionContour
open RiemannSixthTransitionCorrection RiemannSixthTransitionGaussian
open RiemannEvenModelPhase RiemannEvenSaddleBranch RiemannEvenComplexWeight
open RiemannSixthFarSignedIntegral (leadingPhase leadingPhase_zero leadingPhase_hasDerivAt)
open RiemannSixthFarRightTail (actual_weight_model_envelope)
open RiemannEvenWeightEnvelope (horizontal_exp_real_identity)
open RiemannQuarticFarCorrection (small_error_at_large_real_part)
open RiemannThetaComplexKernel RiemannQuarticErrorLimits
section Scaled
variable (t K c₀ : ℝ) (w v : ℂ)
  (ht : 1 ≤ t) (hK : 8 ≤ K) (hr : 120020 ≤ w.re)
  (hmargin : t*w.re^5+8 ≤ 4*Real.pi*(Complex.exp (4*w)).re) (hi : |w.im| ≤ 1/2)
  (hn : ‖w‖ ≤ 2*w.re)
  (hs : modelDerivative 3 t w= -(Complex.I*(c₀ : ℂ))) (hE : ‖Complex.exp (4*w)‖ ≤ K)
  (harith : (30005*Real.exp (-w.re))*K ≤ t*w.re^5/4)
  (hv : ‖v-w‖ ≤ 1/K)
include ht hK hr hmargin hi hn hs hE harith hv

theorem right_model_curvature (s : ℝ) (hs0 : 0 ≤ s) :
    (deriv (modelDerivative 3 t) (v+(s : ℂ))).re ≤ -(t*w.re^5)/4 := by
  let q := v+(s : ℂ)
  have hd := RiemannSixthTransitionGaussian.horizontal_neighbor_domain t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hd
  have ht0 : 0 ≤ t := by linarith
  have hr0 : 0 ≤ w.re := by linarith
  have hx0 : 0 < K := by linarith
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

theorem right_phase_quadratic_bound (z : ℂ) (hz : complexSlope 3 t v= -(Complex.I*z)) (s : ℝ) (hs0 : 0 ≤ s) :
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
    have h := right_model_curvature t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv a ha0
    dsimp [f2,c]
    linarith
  have htangent : f s ≤ f1 0*s := by
    rcases eq_or_lt_of_le hs0 with heq | hpos
    · subst s
      simp [hf0]
    · have h := hc.slope_le_of_hasDerivAt (show (0 : ℝ) ∈ Ici (0 : ℝ) from by simp) hs0 hpos (h1 0)
      rw [slope_def_field,hf0,sub_zero,sub_zero] at h
      exact (div_le_iff₀ hpos).mp h
  have he := RiemannSixthTransitionGaussian.horizontal_neighbor_error t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv 0 (by norm_num)
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

theorem left_unit_domain_curvature (s : ℝ) (hs1 : -1 ≤ s) (hs0 : s ≤ 0) :
    0 ≤ (v+(s : ℂ)).re ∧ 1 ≤ (Complex.exp (4*(v+(s : ℂ)))).re ∧
      (deriv (modelDerivative 3 t) (v+(s : ℂ))).re ≤ -(t*w.re^5)/1024 := by
  have hd := RiemannSixthTransitionGaussian.horizontal_neighbor_domain t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hd
  have ht0 : 0 ≤ t := by linarith
  have hw0 : 0 ≤ w.re := by linarith
  have hx0 : 0 < K := by linarith
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

theorem left_phase_quadratic_bound (z : ℂ) (hz : complexSlope 3 t v= -(Complex.I*z))
    (s : ℝ) (hs1 : -1 ≤ s) (hs0 : s ≤ 0) :
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
    have h := (left_unit_domain_curvature t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv a ha'.1 ha'.2).2.2
    dsimp [f2,c]
    linarith
  have htangent : f s ≤ f1 0*s := by
    rcases lt_or_eq_of_le hs0 with hneg | heq
    · have h := hc.le_slope_of_hasDerivAt ⟨hs1,hs0⟩ (show (0 : ℝ) ∈ Icc (-1 : ℝ) 0 by norm_num) hneg (h1 0)
      rw [slope_def_field,hf0] at h
      have hm := (le_div_iff₀ (by linarith : 0 < 0-s)).mp h
      nlinarith
    · subst s; simp [hf0]
  have he := RiemannSixthTransitionGaussian.horizontal_neighbor_error t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv 0 (by norm_num)
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

theorem actual_gaussian_mass_envelope (z : ℂ) (hz : complexSlope 3 t v= -(Complex.I*z))
    (s : ℝ) (hsl : -1 ≤ s) :
    ‖weight 3 t z (v+(s : ℂ))‖ ≤
      3000*‖weight 3 t z v‖*Real.exp (-(t*w.re^5/4096)*s^2) := by
  have heps : 30005*Real.exp (-4*w.re+4) ≤ 1 := by
    have hb := small_error_at_large_real_part w.re hr
    have he := Real.exp_le_exp.mpr (show -4*w.re+4 ≤ -w.re by linarith)
    nlinarith

  let C := t*w.re^5/4096
  have hcub : (4096 : ℝ) ≤ w.re^5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 16) (by linarith : 16 ≤ w.re) 5
    norm_num at h
    linarith
  have htcu : w.re^5 ≤ t*w.re^5 := by nlinarith [pow_nonneg (by linarith : 0 ≤ w.re) 5]
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hdom0 := RiemannSixthTransitionGaussian.horizontal_neighbor_domain t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hdom0
  have hphase : (leadingPhase t z v (s : ℂ)).re ≤
      (30005*Real.exp (-4*w.re+4))*|s|-2*C*s^2 := by
    rcases le_total s 0 with hleft | hright
    · have h := left_phase_quadratic_bound t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv z hz s hsl hleft
      dsimp [C]
      linarith
    · have h := right_phase_quadratic_bound t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv z hz s hright
      rw [abs_of_nonneg hright]
      dsimp [C]
      nlinarith [mul_nonneg (by positivity : 0 ≤ t*w.re^5) (sq_nonneg s)]
  have hdom : 0 ≤ (v+(s : ℂ)).re ∧ 1 ≤ (Complex.exp (4*(v+(s : ℂ)))).re := by
    rcases le_total s 0 with hleft | hright
    · have h := left_unit_domain_curvature t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv s hsl hleft
      exact ⟨h.1,h.2.1⟩
    · have heq : Complex.exp (4*(v+(s : ℂ)))=(Real.exp (4*s) : ℂ)*Complex.exp (4*v) := by
        rw [Complex.ofReal_exp,← Complex.exp_add]
        congr 1
        push_cast
        ring
      have hE : 1 ≤ Real.exp (4*s) := Real.one_le_exp (by positivity)
      constructor
      · simp only [Complex.add_re,Complex.ofReal_re]; linarith [hdom0.1]
      · rw [heq,Complex.mul_re]
        simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
        nlinarith [hdom0.2.1]
  have henv := actual_weight_model_envelope t z v (s : ℂ) hdom0.1 hdom0.2.1 hdom.1 (by linarith [hdom.2])
  have habs : |s| ≤ s^2+1 := by nlinarith [sq_nonneg (|s|-1),sq_abs s]
  have hmul := mul_le_mul_of_nonneg_right hC (sq_nonneg s)
  have he := mul_le_mul_of_nonneg_right heps (abs_nonneg s)
  have hpbound : (leadingPhase t z v (s : ℂ)).re ≤ 1-C*s^2 := by nlinarith
  apply henv.trans
  change 1000*‖weight 3 t z v‖*Real.exp (leadingPhase t z v (s : ℂ)).re ≤ _
  calc
    _ ≤ 1000*‖weight 3 t z v‖*Real.exp (1-C*s^2) := by gcongr
    _ = (1000*‖weight 3 t z v‖)*(Real.exp 1*Real.exp (-C*s^2)) := by rw [sub_eq_add_neg,Real.exp_add]; ring
    _ ≤ (1000*‖weight 3 t z v‖)*(3*Real.exp (-C*s^2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le (Real.exp_pos _).le) (by positivity)
    _ = _ := by dsimp [C]; ring

theorem horizontal_weight_continuous (z : ℂ) :
    Continuous (fun s : ℝ => weight 3 t z (v+(s : ℂ))) := by
  have hd := RiemannSixthTransitionGaussian.horizontal_neighbor_domain t K c₀ w v
    ht hK hr hmargin hi hn hs hE harith hv 0 (by norm_num)
  simp only [Complex.ofReal_zero, add_zero] at hd
  apply continuous_iff_continuousAt.mpr
  intro s
  have hpos : 0 < (Complex.exp (4*(v+(s : ℂ)))).re := by
    have hid : Complex.exp (4*(v+(s : ℂ)))=(Real.exp (4*s) : ℂ)*Complex.exp (4*v) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hid, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos (Real.exp_pos _) (by linarith [hd.2.1])
  have hk := kernelComplex_analyticAt (v+(s : ℂ)) hpos
  have hw : AnalyticAt ℂ (weight 3 t z) (v+(s : ℂ)) := by
    unfold weight
    apply AnalyticAt.mul
    · fun_prop
    · exact hk
  exact ContinuousAt.comp (g := weight 3 t z) (f := fun a : ℝ => v+(a : ℂ))
    hw.continuousAt (by fun_prop)

theorem actual_outer_integrable (z : ℂ) (hz : complexSlope 3 t v= -(Complex.I*z)) :
    IntegrableOn (fun s : ℝ => weight 3 t z (v+(s : ℂ))) (Ioi (-1)) := by
  have hQ : 0 < t*w.re^5/4096 := by positivity
  have hg : Integrable (fun s : ℝ =>
      (3000*‖weight 3 t z v‖)*Real.exp (-(t*w.re^5/4096)*s^2)) :=
    (integrable_exp_neg_mul_sq hQ).const_mul _
  apply hg.integrableOn.mono'
    (horizontal_weight_continuous t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv z).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs1
  exact actual_gaussian_mass_envelope t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv z hz s hs1.le

theorem actual_outer_central_difference (z : ℂ) (hz : complexSlope 3 t v= -(Complex.I*z))
    (r : ℝ) (hr0 : 0 < r) (hrr : r < 1) :
    ‖(∫ s : ℝ in Ioi (-1), weight 3 t z (v+(s : ℂ)))-
      (∫ s : ℝ in -r..r, weight 3 t z (v+(s : ℂ)))‖ ≤
      3000*‖weight 3 t z v‖*Real.sqrt (8192*Real.pi/(t*w.re^5))*
        Real.exp (-(t*w.re^5)*r^2/8192) := by
  let F := fun s : ℝ => weight 3 t z (v+(s : ℂ))
  let S := Ioi (-1 : ℝ) \ Ioc (-r) r
  let b := t*w.re^5/8192
  let A := 3000*‖weight 3 t z v‖
  have hb : 0 < b := by dsimp [b]; positivity
  have hsub : Ioc (-r) r ⊆ Ioi (-1 : ℝ) := by intro s hs; exact lt_trans (by linarith) hs.1
  have hf := actual_outer_integrable t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv z hz
  have hdiff : (∫ s : ℝ in Ioi (-1), F s)-(∫ s : ℝ in -r..r, F s)=∫ s : ℝ in S, F s := by
    rw [intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
    exact (setIntegral_sdiff measurableSet_Ioc hf hsub).symm
  change ‖(∫ s : ℝ in Ioi (-1), F s)-(∫ s : ℝ in -r..r, F s)‖ ≤ _
  rw [hdiff]
  have hg : Integrable (fun s : ℝ => (A*Real.exp (-b*r^2))*Real.exp (-b*s^2)) :=
    (integrable_exp_neg_mul_sq hb).const_mul _
  have hbound : ∀ s ∈ S, ‖F s‖ ≤ (A*Real.exp (-b*r^2))*Real.exp (-b*s^2) := by
    intro s hsS
    have hs1 : -1 ≤ s := hsS.1.le
    have hsr : r ≤ |s| := by
      by_contra h
      have hh := abs_lt.mp (lt_of_not_ge h)
      exact hsS.2 ⟨by linarith [hh.1], by linarith [hh.2]⟩
    have hsq := pow_le_pow_left₀ hr0.le hsr 2
    rw [sq_abs] at hsq
    have he : -(t*w.re^5/4096)*s^2 ≤ -b*r^2+(-b*s^2) := by
      have hm := mul_le_mul_of_nonneg_left hsq hb.le
      dsimp [b] at *
      nlinarith
    have hh := actual_gaussian_mass_envelope t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv z hz s hs1
    change ‖F s‖ ≤ A*Real.exp (-(t*w.re^5/4096)*s^2) at hh
    calc
      _ ≤ A*Real.exp (-(t*w.re^5/4096)*s^2) := hh
      _ ≤ A*Real.exp (-b*r^2+(-b*s^2)) := by gcongr
      _ = _ := by rw [Real.exp_add]; ring
  have hpoint : ∀ᵐ s : ℝ ∂volume.restrict S, ‖F s‖ ≤ (A*Real.exp (-b*r^2))*Real.exp (-b*s^2) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.diff measurableSet_Ioc)] with s hsS
    exact hbound s hsS
  have hi := norm_integral_le_of_norm_le hg.integrableOn hpoint
  have hwhole := setIntegral_le_integral (s := S) hg (Eventually.of_forall (fun s : ℝ =>
    (show 0 ≤ (A*Real.exp (-b*r^2))*Real.exp (-b*s^2) from by dsimp [A]; positivity)))
  apply hi.trans (hwhole.trans_eq ?_)
  rw [integral_const_mul, integral_gaussian]
  have harg : Real.pi/b=8192*Real.pi/(t*w.re^5) := by dsimp [b]; ring
  rw [harg]
  dsimp [A,b]
  ring

theorem relative_outer_central_difference (z : ℂ) (hz : complexSlope 3 t v= -(Complex.I*z))
    (r : ℝ) (hr0 : 0 < r) (hrr : r < 1) :
    ‖((∫ s : ℝ in Ioi (-1), weight 3 t z (v+(s : ℂ)))-
        (∫ s : ℝ in -r..r, weight 3 t z (v+(s : ℂ))))/
      (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))‖ ≤
      24000*Real.sqrt K*Real.sqrt (8192*Real.pi)*Real.exp (-(t*w.re^5)*r^2/8192) := by
  have he := actual_outer_central_difference t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv z hz r hr0 hrr
  let W := weight 3 t z v
  let G := ∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)
  let B := 3000*Real.sqrt (8192*Real.pi)*Real.exp (-(t*w.re^5)*r^2/8192)
  let L := (∫ s : ℝ in Ioi (-1), weight 3 t z (v+(s : ℂ)))-
    (∫ s : ℝ in -r..r, weight 3 t z (v+(s : ℂ)))
  have hQ : 1 ≤ t*w.re^5 := by
    have hp : 1 ≤ w.re^5 := one_le_pow₀ (by linarith : 1 ≤ w.re)
    nlinarith
  have harg : 8192*Real.pi/(t*w.re^5) ≤ 8192*Real.pi :=
    (div_le_self (by positivity) hQ)
  have hsqrt := Real.sqrt_le_sqrt harg
  have hnum : ‖L‖ ≤ ‖W‖*B := by
    apply he.trans
    dsimp [B,W]
    have hh := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ 3000*‖weight 3 t z v‖ by positivity)
    have hm := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-(t*w.re^5)*r^2/8192)).le
    nlinarith
  have hnormal := gaussian_normalization_lower t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv
  change 1 ≤ 8*Real.sqrt K*‖G‖ at hnormal
  have hG : G ≠ 0 := by intro h; norm_num [h] at hnormal
  have hd := RiemannSixthTransitionGaussian.horizontal_neighbor_domain t K c₀ w v
    ht hK hr hmargin hi hn hs hE harith hv 0 (by norm_num)
  simp only [Complex.ofReal_zero, add_zero] at hd
  have hW : W ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (kernel_ne_zero v hd.1 hd.2.1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  change ‖L/(W*G)‖ ≤ _
  rw [norm_div, norm_mul]
  apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hW) (norm_pos_iff.mpr hG))).mpr
  have hm := mul_le_mul_of_nonneg_left hnormal (mul_nonneg (norm_nonneg W) hB)
  dsimp [B] at *
  nlinarith

end Scaled

theorem eventually_uniform_relative_outer_error (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ Q : ℝ in atTop, ∀ (t K c₀ : ℝ) (w v z : ℂ),
      1 ≤ t → 8 ≤ K → 120020 ≤ w.re → t*w.re^5+8 ≤ 4*Real.pi*(Complex.exp (4*w)).re → |w.im| ≤ 1/2 → ‖w‖ ≤ 2*w.re →
      modelDerivative 3 t w= -(Complex.I*(c₀ : ℂ)) → ‖Complex.exp (4*w)‖ ≤ K → (30005*Real.exp (-w.re))*K ≤ t*w.re^5/4 → ‖v-w‖ ≤ 1/K →
      complexSlope 3 t v= -(Complex.I*z) → Q=t*w.re^5 → K ≤ C*Q →
      ‖(∫ s : ℝ in Ioi (-1), weight 3 t z (v+(s : ℂ)))/
        (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))-1‖ < ε := by
  filter_upwards [eventually_uniform_relative_central_error C (ε/2) hC (half_pos hε),
    eventually_gt_atTop (0 : ℝ),
    centralRadius_tendsto_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    (RiemannQuarticTransitionContour.outer_tail_budget_tendsto_zero C).eventually (gt_mem_nhds (half_pos hε))]
    with Q hcentral hQ hcap hbudget
  intro t K c₀ w v z ht hK hr hmargin hi hn hs hE harith hv hstat hQid hratio
  have hr0 : 0 < centralRadius Q := Real.rpow_pos_of_pos hQ _
  have hc := hcentral t K c₀ w v z ht hK hr hmargin hi hn hs hE harith hv hstat hQid hratio
  have hd := relative_outer_central_difference t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv
    z hstat (centralRadius Q) hr0 hcap
  rw [← hQid] at hd
  have he : -Q*centralRadius Q^2/8192= -(1/8192 : ℝ)*Q^(1/8 : ℝ) := by
    rw [show -Q*centralRadius Q^2/8192= -(1/8192 : ℝ)*(Q*centralRadius Q^2) by ring,
      gaussian_argument Q hQ]
  rw [he] at hd
  have hroot : Real.sqrt K ≤ Real.sqrt C*Real.sqrt Q := by
    rw [← Real.sqrt_mul hC.le]
    exact Real.sqrt_le_sqrt hratio
  have hmul := mul_le_mul_of_nonneg_right hroot (show 0 ≤
      24000*Real.sqrt (8192*Real.pi)*Real.exp (-(1/8192 : ℝ)*Q^(1/8 : ℝ)) by positivity)
  have htail :
      ‖((∫ s : ℝ in Ioi (-1), weight 3 t z (v+(s : ℂ)))-
          (∫ s : ℝ in -(centralRadius Q)..centralRadius Q, weight 3 t z (v+(s : ℂ))))/
        (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))‖ < ε/2 := by
    nlinarith
  let D := weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2))
  let L := ∫ s : ℝ in Ioi (-1), weight 3 t z (v+(s : ℂ))
  let Lc := ∫ s : ℝ in -(centralRadius Q)..centralRadius Q, weight 3 t z (v+(s : ℂ))
  have hid : L/D-1=(Lc/D-1)+(L-Lc)/D := by rw [sub_div]; ring
  change ‖L/D-1‖ < ε
  rw [hid]
  have htri := norm_add_le (Lc/D-1) ((L-Lc)/D)
  change ‖Lc/D-1‖ < ε/2 at hc
  change ‖(L-Lc)/D‖ < ε/2 at htail
  linarith

theorem eventually_actual_relative_outer_error (M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∃ u : ℝ, 65536*(M+7) ≤ u ∧ RiemannEvenRealSaddle.phaseSlope 3 t u=0 ∧
      ∀ c : ℝ, |c| ≤ M*RiemannQuarticTransitionSaddle.realScale u →
        ∃ (w : ℂ) (b : ℂ → ℂ), ‖w-(u : ℂ)‖ ≤ M+7 ∧
          ∀ z : ℂ, ‖z-(c : ℂ)‖ ≤ 1/(2048*(M+8)) →
            AnalyticAt ℂ b z ∧ complexSlope 3 t (b z)= -(Complex.I*z) ∧
            RiemannSixthFarPairing.modelGaussianAmplitude t z (b z) ≠ 0 ∧
            ‖(∫ s : ℝ in Ioi (-1),
              weight 3 t z (b z+(s : ℂ)))/RiemannSixthFarPairing.modelGaussianAmplitude t z (b z)-1‖ < ε := by
  let C := 1024*(M+8)
  have hC0 : 0 < C := by dsimp [C]; positivity
  obtain ⟨U,hU⟩ := eventually_atTop.1 (eventually_uniform_relative_outer_error C ε hC0 hε)
  filter_upwards [RiemannSixthTransitionCorrection.eventually_exists_actual_transition_family M hM,
    eventually_ge_atTop (max U 1)] with t hfamily htU
  obtain ⟨u,hu,hstationary,_⟩ := hfamily
  have ht : 1 ≤ t := (le_max_right U 1).trans htU
  refine ⟨u,hu,hstationary,?_⟩
  intro c hc
  let K := (M+8)*RiemannQuarticTransitionSaddle.realScale u
  let C := 1024*(M+8)
  let r := 1/C
  have hC : 0 < C := by dsimp [C]; positivity
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hcnorm : ‖(c : ℂ)‖ ≤ M*RiemannQuarticTransitionSaddle.realScale u := by simpa using hc
  obtain ⟨w,hw,_⟩ := RiemannSixthTransitionSaddle.existsUnique_transition_model_saddle
    t u M (c : ℂ) ht hM hu hstationary (by simp) hcnorm
  have hg := RiemannSixthTransitionSaddle.transition_model_geometry t u M (c : ℂ) w
    ht hM hu hstationary (by simp) hcnorm hw.1 hw.2
  have hd := transition_scale_data t u M (c : ℂ) w ht hM hu hstationary (by simp) hcnorm hw.1 hw.2
  have hK : 8 ≤ K := hd.1
  have hnorm := hd.2.2.2.1
  have hE := hd.2.2.2.2.1
  have hsmall := hd.2.2.2.2.2.1
  have hmargin := hd.2.2.2.2.2.2
  have hcoord := (Complex.abs_re_le_norm (w-(u : ℂ))).trans hg.1
  simp only [Complex.sub_re,Complex.ofReal_re] at hcoord
  have hr : 120020 ≤ w.re := by linarith [(abs_le.mp hcoord).1]
  have hscale : K ≤ C*(t*w.re^5) :=
    RiemannSixthTransitionAnalyticBranch.moving_scale_ratio_bound t u M w ht hM hu hstationary hg.1
  have hradius : r ≤ t*w.re^5/K := by
    apply (le_div_iff₀ (by linarith : 0 < K)).mpr
    dsimp [r]
    have hh : K/C ≤ t*w.re^5 := (div_le_iff₀ hC).mpr (by nlinarith)
    simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul] using hh
  let b := RiemannSixthTransitionAnalyticBranch.branch t K c r w ht hK hr hmargin hd.2.2.1 hnorm hw.2 hE hsmall hradius
  have hQ : U ≤ t*w.re^5 := by
    have hp : 1 ≤ w.re^5 := one_le_pow₀ (by linarith : 1 ≤ w.re)
    have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ t by linarith)
    linarith [(le_max_left U 1).trans htU]
  refine ⟨w,b,hg.1,?_⟩
  intro z hz
  have hzlt : ‖z-(c : ℂ)‖ < r := by
    have hpos : 0 < M+8 := by positivity
    dsimp [r,C]
    have hhalf : 1/(2048*(M+8)) < 1/(1024*(M+8)) := by
      apply one_div_lt_one_div_of_lt (by positivity)
      nlinarith
    exact hz.trans_lt hhalf
  have hspec := RiemannSixthTransitionAnalyticBranch.branch_spec t K c r w ht hK hr hmargin hd.2.2.1
    hnorm hw.2 hE hsmall hrpos hradius z hzlt.le
  have hv : ‖b z-w‖ ≤ 1/K := by simpa only [mem_closedBall,dist_eq_norm] using hspec.1
  have he := hU (t*w.re^5) hQ t K c w (b z) z ht hK hr hmargin hd.2.2.1 hnorm hw.2 hE hsmall hv hspec.2 rfl hscale
  refine ⟨RiemannSixthTransitionAnalyticBranch.branch_analyticAt t K c r w ht hK hr hmargin hd.2.2.1
    hnorm hw.2 hE hsmall hrpos hradius z hzlt,hspec.2,?_,he⟩
  exact mul_ne_zero
    (RiemannSixthTransitionAnalyticBranch.actual_weight_ne_zero t K c r w ht hK hr hmargin hd.2.2.1
      hnorm hw.2 hE hsmall hrpos hradius z hzlt.le)
    (RiemannSixthTransitionGaussianPhase.gaussian_ne_zero t K c r w ht hK hr hmargin hd.2.2.1
      hnorm hw.2 hE hsmall hrpos hradius z hzlt.le)

end OperatorDerivativeRewrite.Foundation.RiemannSixthTransitionContour
