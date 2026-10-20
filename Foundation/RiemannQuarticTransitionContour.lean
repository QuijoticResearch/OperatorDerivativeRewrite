import Foundation.RiemannQuarticTransitionGaussian
import Foundation.RiemannQuarticReflectedDominance
/-! Actual outer horizontal contour control on the transition scales.
The central signed approximation is supplemented by actual Gaussian domination.
Compact contour pieces and paired-channel zero conclusions remain separate. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticTransitionContour
open RiemannQuarticTransitionCorrection RiemannQuarticTransitionGaussian
open RiemannQuarticSaddleTheta RiemannQuarticSaddleBranch RiemannQuarticFrequencyBranch
open RiemannQuarticFarModelSaddle RiemannQuarticFarCorrection RiemannQuarticFarSignedIntegral
open RiemannQuarticFarRightTail RiemannThetaComplexKernel RiemannQuarticErrorLimits
section Scaled
variable (t K : ℝ) (c₀ w v : ℂ)
  (ht : 1 ≤ t) (hK : 8 ≤ K) (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
  (hn : ‖w‖ ≤ 2*w.re) (hcenter : c₀.im ≤ 1)
  (hs : modelDerivative t w= -(Complex.I*c₀)) (hE : ‖Complex.exp (4*w)‖ ≤ K)
  (hv : ‖v-w‖ ≤ 1/K)
include ht hK hr hi hn hcenter hs hE hv

theorem right_model_curvature (s : ℝ) (hs0 : 0 ≤ s) :
    (deriv (modelDerivative t) (v+(s : ℂ))).re ≤ -(t*w.re^3)/4 := by
  have hd := RiemannQuarticTransitionGaussian.horizontal_neighbor_domain t K c₀ w v ht hK (by linarith) hi hn hcenter hs hE hv 0 (by norm_num)
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

theorem right_phase_quadratic_bound (z : ℂ) (hz : complexSlope t v= -(Complex.I*z)) (s : ℝ) (hs0 : 0 ≤ s) :
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
    have h := right_model_curvature t K c₀ w v ht hK hr hi hn hcenter hs hE hv a ha0
    dsimp [f2,c]
    linarith
  have htangent : f s ≤ f1 0*s := by
    rcases eq_or_lt_of_le hs0 with heq | hpos
    · subst s
      simp [hf0]
    · have h := hc.slope_le_of_hasDerivAt (show (0 : ℝ) ∈ Ici (0 : ℝ) from by simp) hs0 hpos (h1 0)
      rw [slope_def_field,hf0,sub_zero,sub_zero] at h
      exact (div_le_iff₀ hpos).mp h
  have he := RiemannQuarticTransitionGaussian.horizontal_neighbor_error t K c₀ w v ht hK (by linarith) hi hn hcenter hs hE hv 0 (by norm_num)
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

theorem left_unit_domain_curvature (s : ℝ) (hs1 : -1 ≤ s) (hs0 : s ≤ 0) :
    0 ≤ (v+(s : ℂ)).re ∧ 1 ≤ (Complex.exp (4*(v+(s : ℂ)))).re ∧
      (deriv (modelDerivative t) (v+(s : ℂ))).re ≤ -(t*w.re^3)/1024 := by
  have hd := RiemannQuarticTransitionGaussian.horizontal_neighbor_domain t K c₀ w v ht hK (by linarith) hi hn hcenter hs hE hv 0 (by norm_num)
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

theorem left_phase_quadratic_bound (z : ℂ) (hz : complexSlope t v= -(Complex.I*z))
    (s : ℝ) (hs1 : -1 ≤ s) (hs0 : s ≤ 0) :
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
    have h := (left_unit_domain_curvature t K c₀ w v ht hK hr hi hn hcenter hs hE hv a ha'.1 ha'.2).2.2
    dsimp [f2,c]
    linarith
  have htangent : f s ≤ f1 0*s := by
    rcases lt_or_eq_of_le hs0 with hneg | heq
    · have h := hc.le_slope_of_hasDerivAt ⟨hs1,hs0⟩ (show (0 : ℝ) ∈ Icc (-1 : ℝ) 0 by norm_num) hneg (h1 0)
      rw [slope_def_field,hf0] at h
      have hm := (le_div_iff₀ (by linarith : 0 < 0-s)).mp h
      nlinarith
    · subst s; simp [hf0]
  have he := RiemannQuarticTransitionGaussian.horizontal_neighbor_error t K c₀ w v ht hK (by linarith) hi hn hcenter hs hE hv 0 (by norm_num)
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

theorem actual_gaussian_mass_envelope (z : ℂ) (hz : complexSlope t v= -(Complex.I*z))
    (s : ℝ) (hsl : -1 ≤ s) :
    ‖saddleWeight t z (v+(s : ℂ))‖ ≤
      3000*‖saddleWeight t z v‖*Real.exp (-(t*w.re^3/4096)*s^2) := by
  have heps : 30005*Real.exp (-4*w.re+4) ≤ 1 := by
    have hb := small_error_at_large_real_part w.re hr
    have he := Real.exp_le_exp.mpr (show -4*w.re+4 ≤ -w.re by linarith)
    nlinarith

  let C := t*w.re^3/4096
  have hcub : (4096 : ℝ) ≤ w.re^3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 16) (by linarith : 16 ≤ w.re) 3
    norm_num at h
    exact h
  have htcu : w.re^3 ≤ t*w.re^3 := by nlinarith [pow_nonneg (by linarith : 0 ≤ w.re) 3]
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hdom0 := RiemannQuarticTransitionGaussian.horizontal_neighbor_domain t K c₀ w v ht hK (by linarith) hi hn hcenter hs hE hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hdom0
  have hphase : (RiemannQuarticFarSignedIntegral.leadingPhase t z v (s : ℂ)).re ≤
      (30005*Real.exp (-4*w.re+4))*|s|-2*C*s^2 := by
    rcases le_total s 0 with hleft | hright
    · have h := left_phase_quadratic_bound t K c₀ w v ht hK hr hi hn hcenter hs hE hv z hz s hsl hleft
      dsimp [C]
      linarith
    · have h := right_phase_quadratic_bound t K c₀ w v ht hK hr hi hn hcenter hs hE hv z hz s hright
      rw [abs_of_nonneg hright]
      dsimp [C]
      nlinarith [mul_nonneg (by positivity : 0 ≤ t*w.re^3) (sq_nonneg s)]
  have hdom : 0 ≤ (v+(s : ℂ)).re ∧ 1 ≤ (Complex.exp (4*(v+(s : ℂ)))).re := by
    rcases le_total s 0 with hleft | hright
    · have h := left_unit_domain_curvature t K c₀ w v ht hK hr hi hn hcenter hs hE hv s hsl hleft
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
  have hpbound : (RiemannQuarticFarSignedIntegral.leadingPhase t z v (s : ℂ)).re ≤ 1-C*s^2 := by nlinarith
  apply henv.trans
  change 1000*‖saddleWeight t z v‖*Real.exp (RiemannQuarticFarSignedIntegral.leadingPhase t z v (s : ℂ)).re ≤ _
  calc
    _ ≤ 1000*‖saddleWeight t z v‖*Real.exp (1-C*s^2) := by gcongr
    _ = (1000*‖saddleWeight t z v‖)*(Real.exp 1*Real.exp (-C*s^2)) := by rw [sub_eq_add_neg,Real.exp_add]; ring
    _ ≤ (1000*‖saddleWeight t z v‖)*(3*Real.exp (-C*s^2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le (Real.exp_pos _).le) (by positivity)
    _ = _ := by dsimp [C]; ring

theorem horizontal_weight_continuous (z : ℂ) :
    Continuous (fun s : ℝ => saddleWeight t z (v+(s : ℂ))) := by
  have hd := RiemannQuarticTransitionGaussian.horizontal_neighbor_domain t K c₀ w v
    ht hK (by linarith) hi hn hcenter hs hE hv 0 (by norm_num)
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
  have hw : AnalyticAt ℂ (saddleWeight t z) (v+(s : ℂ)) := by
    unfold saddleWeight
    apply AnalyticAt.mul
    · fun_prop
    · exact hk
  exact ContinuousAt.comp (g := saddleWeight t z) (f := fun a : ℝ => v+(a : ℂ))
    hw.continuousAt (by fun_prop)

theorem actual_outer_integrable (z : ℂ) (hz : complexSlope t v= -(Complex.I*z)) :
    IntegrableOn (fun s : ℝ => saddleWeight t z (v+(s : ℂ))) (Ioi (-1)) := by
  have hQ : 0 < t*w.re^3/4096 := by positivity
  have hg : Integrable (fun s : ℝ =>
      (3000*‖saddleWeight t z v‖)*Real.exp (-(t*w.re^3/4096)*s^2)) :=
    (integrable_exp_neg_mul_sq hQ).const_mul _
  apply hg.integrableOn.mono'
    (horizontal_weight_continuous t K c₀ w v ht hK hr hi hn hcenter hs hE hv z).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs1
  exact actual_gaussian_mass_envelope t K c₀ w v ht hK hr hi hn hcenter hs hE hv z hz s hs1.le

theorem actual_outer_central_difference (z : ℂ) (hz : complexSlope t v= -(Complex.I*z))
    (r : ℝ) (hr0 : 0 < r) (hrr : r < 1) :
    ‖(∫ s : ℝ in Ioi (-1), saddleWeight t z (v+(s : ℂ)))-
      (∫ s : ℝ in -r..r, saddleWeight t z (v+(s : ℂ)))‖ ≤
      3000*‖saddleWeight t z v‖*Real.sqrt (8192*Real.pi/(t*w.re^3))*
        Real.exp (-(t*w.re^3)*r^2/8192) := by
  let F := fun s : ℝ => saddleWeight t z (v+(s : ℂ))
  let S := Ioi (-1 : ℝ) \ Ioc (-r) r
  let b := t*w.re^3/8192
  let A := 3000*‖saddleWeight t z v‖
  have hb : 0 < b := by dsimp [b]; positivity
  have hsub : Ioc (-r) r ⊆ Ioi (-1 : ℝ) := by intro s hs; exact lt_trans (by linarith) hs.1
  have hf := actual_outer_integrable t K c₀ w v ht hK hr hi hn hcenter hs hE hv z hz
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
    have he : -(t*w.re^3/4096)*s^2 ≤ -b*r^2+(-b*s^2) := by
      have hm := mul_le_mul_of_nonneg_left hsq hb.le
      dsimp [b] at *
      nlinarith
    have hh := actual_gaussian_mass_envelope t K c₀ w v ht hK hr hi hn hcenter hs hE hv z hz s hs1
    change ‖F s‖ ≤ A*Real.exp (-(t*w.re^3/4096)*s^2) at hh
    calc
      _ ≤ A*Real.exp (-(t*w.re^3/4096)*s^2) := hh
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
  have harg : Real.pi/b=8192*Real.pi/(t*w.re^3) := by dsimp [b]; ring
  rw [harg]
  dsimp [A,b]
  ring

theorem relative_outer_central_difference (z : ℂ) (hz : complexSlope t v= -(Complex.I*z))
    (r : ℝ) (hr0 : 0 < r) (hrr : r < 1) :
    ‖((∫ s : ℝ in Ioi (-1), saddleWeight t z (v+(s : ℂ)))-
        (∫ s : ℝ in -r..r, saddleWeight t z (v+(s : ℂ))))/
      (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤
      24000*Real.sqrt K*Real.sqrt (8192*Real.pi)*Real.exp (-(t*w.re^3)*r^2/8192) := by
  have he := actual_outer_central_difference t K c₀ w v ht hK hr hi hn hcenter hs hE hv z hz r hr0 hrr
  let W := saddleWeight t z v
  let G := ∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)
  let B := 3000*Real.sqrt (8192*Real.pi)*Real.exp (-(t*w.re^3)*r^2/8192)
  let L := (∫ s : ℝ in Ioi (-1), saddleWeight t z (v+(s : ℂ)))-
    (∫ s : ℝ in -r..r, saddleWeight t z (v+(s : ℂ)))
  have hQ : 1 ≤ t*w.re^3 := by
    have hp : 1 ≤ w.re^3 := one_le_pow₀ (by linarith : 1 ≤ w.re)
    nlinarith
  have harg : 8192*Real.pi/(t*w.re^3) ≤ 8192*Real.pi :=
    (div_le_self (by positivity) hQ)
  have hsqrt := Real.sqrt_le_sqrt harg
  have hnum : ‖L‖ ≤ ‖W‖*B := by
    apply he.trans
    dsimp [B,W]
    have hh := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ 3000*‖saddleWeight t z v‖ by positivity)
    have hm := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-(t*w.re^3)*r^2/8192)).le
    nlinarith
  have hnormal := gaussian_normalization_lower t K c₀ w v ht hK (by linarith) hi hn hcenter hs hE hv
  change 1 ≤ 8*Real.sqrt K*‖G‖ at hnormal
  have hG : G ≠ 0 := by intro h; norm_num [h] at hnormal
  have hd := RiemannQuarticTransitionGaussian.horizontal_neighbor_domain t K c₀ w v
    ht hK (by linarith) hi hn hcenter hs hE hv 0 (by norm_num)
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

theorem outer_tail_budget_tendsto_zero (C : ℝ) :
    Tendsto (fun Q : ℝ => 24000*Real.sqrt C*Real.sqrt Q*Real.sqrt (8192*Real.pi)*
      Real.exp (-(1/8192 : ℝ)*Q^(1/8 : ℝ))) atTop (nhds 0) := by
  have hcomp := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4 : ℝ)
    (1/8192) (by norm_num)).comp (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/8))
  have hbase : Tendsto (fun Q : ℝ => Real.sqrt Q*Real.exp (-(1/8192 : ℝ)*Q^(1/8 : ℝ)))
      atTop (nhds 0) := by
    apply hcomp.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with Q hQ
    simp only [Function.comp_def]
    rw [← Real.rpow_mul hQ.le]
    norm_num [Real.sqrt_eq_rpow]
  have h := hbase.const_mul (24000*Real.sqrt C*Real.sqrt (8192*Real.pi))
  convert h using 1
  · ext Q
    ring
  · ring

theorem eventually_uniform_relative_outer_error (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ Q : ℝ in atTop, ∀ (t K : ℝ) (c₀ w v z : ℂ),
      1 ≤ t → 8 ≤ K → 120020 ≤ w.re → |w.im| ≤ 1/2 → ‖w‖ ≤ 2*w.re → c₀.im ≤ 1 →
      modelDerivative t w= -(Complex.I*c₀) → ‖Complex.exp (4*w)‖ ≤ K → ‖v-w‖ ≤ 1/K →
      complexSlope t v= -(Complex.I*z) → Q=t*w.re^3 → K ≤ C*Q →
      ‖(∫ s : ℝ in Ioi (-1), saddleWeight t z (v+(s : ℂ)))/
        (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))-1‖ < ε := by
  filter_upwards [eventually_uniform_relative_central_error C (ε/2) hC (half_pos hε),
    eventually_gt_atTop (0 : ℝ),
    centralRadius_tendsto_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    (outer_tail_budget_tendsto_zero C).eventually (gt_mem_nhds (half_pos hε))]
    with Q hcentral hQ hcap hbudget
  intro t K c₀ w v z ht hK hr hi hn hcenter hs hE hv hstat hQid hratio
  have hr0 : 0 < centralRadius Q := Real.rpow_pos_of_pos hQ _
  have hc := hcentral t K c₀ w v z ht hK (by linarith) hi hn hcenter hs hE hv hstat hQid hratio
  have hd := relative_outer_central_difference t K c₀ w v ht hK hr hi hn hcenter hs hE hv
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
      ‖((∫ s : ℝ in Ioi (-1), saddleWeight t z (v+(s : ℂ)))-
          (∫ s : ℝ in -(centralRadius Q)..centralRadius Q, saddleWeight t z (v+(s : ℂ))))/
        (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ < ε/2 := by
    nlinarith
  let D := saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2))
  let L := ∫ s : ℝ in Ioi (-1), saddleWeight t z (v+(s : ℂ))
  let Lc := ∫ s : ℝ in -(centralRadius Q)..centralRadius Q, saddleWeight t z (v+(s : ℂ))
  have hid : L/D-1=(Lc/D-1)+(L-Lc)/D := by rw [sub_div]; ring
  change ‖L/D-1‖ < ε
  rw [hid]
  have htri := norm_add_le (Lc/D-1) ((L-Lc)/D)
  change ‖Lc/D-1‖ < ε/2 at hc
  change ‖(L-Lc)/D‖ < ε/2 at htail
  linarith

theorem eventually_actual_relative_outer_error (M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∃ u : ℝ, 65536*(M+7) ≤ u ∧ RiemannQuarticSaddleTimes.phaseSlope t u=0 ∧
      ∀ z : ℂ, z.im ≤ 1 → ‖z‖ ≤ M*RiemannQuarticTransitionSaddle.realScale u →
        ∃ w v : ℂ, w ∈ closedBall (RiemannQuarticTransitionSaddle.movingAnchor u z) (1/1024) ∧
          modelDerivative t w= -(Complex.I*z) ∧
          ‖v-w‖ ≤ 1/((M+8)*RiemannQuarticTransitionSaddle.realScale u) ∧
          complexSlope t v= -(Complex.I*z) ∧
          ‖(∫ s : ℝ in Ioi (-1), saddleWeight t z (v+(s : ℂ)))/
            (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))-1‖ < ε := by
  let C := 128*(M+8)
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨U,hU⟩ := eventually_atTop.1 (eventually_uniform_relative_outer_error C ε hC hε)
  filter_upwards [RiemannQuarticTransitionSaddle.eventually_exists_transition_family M hM,
    eventually_ge_atTop (max U 1)] with t hmodels htU
  obtain ⟨u,hu,hs,hmodel⟩ := hmodels
  have ht : 1 ≤ t := (le_max_right U 1).trans htU
  refine ⟨u,hu,hs,?_⟩
  intro z hy hz
  obtain ⟨w,hw,_⟩ := hmodel z hy hz
  have hd := transition_scale_data t u M z w ht hM hu hs hy hz hw.1 hw.2
  let K := (M+8)*RiemannQuarticTransitionSaddle.realScale u
  have hK0 : 0 < K := by
    change 0 < (M+8)*RiemannQuarticTransitionSaddle.realScale u
    positivity [RiemannQuarticTransitionSaddle.realScale_pos u]
  have hwpos : 0 < w.re := by linarith [hd.2.1]
  obtain ⟨v,hv,_⟩ := actual_scaled_frequency_disk t K z w z ht hd.1 hd.2.1 hd.2.2.1
    hd.2.2.2.1 hy hw.2 hd.2.2.2.2.1 hd.2.2.2.2.2 (by simp; positivity)
  have hvdist : ‖v-w‖ ≤ 1/K := by simpa only [mem_closedBall, dist_eq_norm] using hv.1
  have hg := RiemannQuarticTransitionSaddle.transition_model_geometry t u M z w ht hM hu hs hy hz hw.1 hw.2
  have hratio : K ≤ C*(t*w.re^3) := moving_scale_ratio_bound t u M w ht hM hu hs hg.1
  have hcoord := (Complex.abs_re_le_norm (w-(u : ℂ))).trans hg.1
  simp only [Complex.sub_re, Complex.ofReal_re] at hcoord
  have hlarge : 120020 ≤ w.re := by linarith [(abs_le.mp hcoord).1]
  have hQ : U ≤ t*w.re^3 := by
    have hp : 1 ≤ w.re^3 := one_le_pow₀ (by linarith : 1 ≤ w.re)
    have hh := mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ t)
    linarith [(le_max_left U 1).trans htU]
  have he := hU (t*w.re^3) hQ t K z w v z ht hd.1 hlarge hd.2.2.1 hd.2.2.2.1
    hy hw.2 hd.2.2.2.2.1 hvdist hv.2 rfl hratio
  exact ⟨w,v,hw.1,hw.2,hvdist,hv.2,he⟩

end OperatorDerivativeRewrite.Foundation.RiemannQuarticTransitionContour
