import Foundation.RiemannQuarticComplexCorrection
import Foundation.RiemannQuarticFarGaussianLimit
/-! Signed local Gaussian approximation at actual complex-frequency quartic saddles.
The arithmetic phase is reconstructed on real horizontal intervals. The model
curvature and its actual-stationarity mismatch remain explicit. Complementary
contours and competing-channel dominance are separate obligations. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticComplexGaussian
open RiemannQuarticSaddleTheta RiemannQuarticSaddleBranch RiemannQuarticFarModelSaddle
open RiemannQuarticFrequencyBranch RiemannThetaComplexKernel
open RiemannQuarticFarCorrection RiemannQuarticFarRemainder RiemannQuarticFarSignedIntegral
open RiemannQuarticFarGaussianLocal RiemannQuarticFarGaussianLimit
open RiemannQuarticErrorLimits

theorem neighbor_error_sharp_bound (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c‖) (w v : ℂ)
    (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c‖) (hv : ‖v-w‖ ≤ 2/‖c‖) :
    ‖complexSlope t v-modelDerivative t v‖ ≤ 30005*Real.exp (-4*w.re+4) := by
  have hdom := RiemannQuarticComplexCorrection.neighbor_domain t c hcenter ht hx w v hr hi hs hp hv
  have hd : ‖v-w‖ ≤ 1 := hv.trans ((div_le_iff₀ (by linarith : 0 < ‖c‖)).mpr (by linarith))
  have hcoord := (Complex.abs_re_le_norm (v-w)).trans hd
  simp only [Complex.sub_re] at hcoord
  have hlo := (abs_le.mp hcoord).1
  have hhi := (abs_le.mp hcoord).2
  have heq : complexSlope t v-modelDerivative t v=
      kernelDerivative v/kernelComplex v-(9-4*(Real.pi : ℂ)*Complex.exp (4*v)) := by
    unfold complexSlope modelDerivative
    rw [(kernelComplex_hasDerivAt v (by linarith [hdom.2.1])).deriv]
    ring
  rw [heq]
  apply (RiemannQuarticSaddleNeighborhood.logDerivative_coarse_bound v hdom.1 hdom.2.1).trans
  have hcub : 1024*w.re ≤ w.re^3 := by
    have hsq : 1024 ≤ w.re^2 := by nlinarith
    have h := mul_le_mul_of_nonneg_right hsq (by linarith : 0 ≤ w.re)
    nlinarith
  have htcub : w.re^3 ≤ t*w.re^3 := by nlinarith [pow_nonneg (by linarith : 0 ≤ w.re) 3]
  have hpi := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (by linarith [hdom.2.1] : 0 ≤ (Complex.exp (4*v)).re)
  have h1 : Real.exp (-4*v.re) ≤ Real.exp (-4*w.re+4) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (4*v.re)*Real.exp (-3*Real.pi*(Complex.exp (4*v)).re) ≤ Real.exp (-4*w.re+4) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hdom.2.2]
  have hh1 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ)≤5)
  have hh2 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ)≤30000)
  nlinarith






theorem horizontal_neighbor_domain (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c‖) (w v : ℂ)
    (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖) (s : ℝ) (hsr : |s| ≤ 1/16) :
    0 ≤ (v+(s : ℂ)).re ∧ 1 ≤ (Complex.exp (4*(v+(s : ℂ)))).re ∧
      t*w.re^3/64 ≤ (Complex.exp (4*(v+(s : ℂ)))).re ∧
      |(v+(s : ℂ)).re-w.re| ≤ 1 := by
  have hx0 : 0 < ‖c‖ := by linarith
  have hd2 : ‖v-w‖ ≤ 2/‖c‖ := hv.trans (by apply (div_le_div_iff_of_pos_right hx0).mpr; norm_num)
  have hdom := RiemannQuarticComplexCorrection.neighbor_domain t c hcenter ht hx w v hr hi hs hp hd2
  have hE := horizontal_exp_real_lower v (by linarith [hdom.2.1]) s hsr
  have hd : ‖v-w‖ ≤ 1/8 := hv.trans ((div_le_iff₀ hx0).mpr (by linarith))
  have hre := (Complex.abs_re_le_norm (v-w)).trans hd
  simp only [Complex.sub_re] at hre
  have hcub : 32768 ≤ w.re^3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤32) hr 3
    norm_num at h
    exact h
  have htcu : w.re^3 ≤ t*w.re^3 := by nlinarith
  simp only [Complex.add_re,Complex.ofReal_re] at *
  rcases abs_le.mp hre with ⟨hr1,hr2⟩
  rcases abs_le.mp hsr with ⟨hs1,hs2⟩
  refine ⟨by linarith,by nlinarith [hdom.2.2],by nlinarith [hdom.2.2],?_⟩
  exact abs_le.mpr ⟨by linarith,by linarith⟩



theorem horizontal_neighbor_error (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c‖) (w v : ℂ)
    (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖) (s : ℝ) (hsr : |s| ≤ 1/16) :
    ‖complexSlope t (v+(s : ℂ))-modelDerivative t (v+(s : ℂ))‖ ≤
      30005*Real.exp (-4*w.re+4) := by
  let q := v+(s : ℂ)
  have hd := horizontal_neighbor_domain t c hcenter ht hx w v hr hi hs hp hv s hsr
  change 0 ≤ q.re ∧ 1 ≤ (Complex.exp (4*q)).re ∧ t*w.re^3/64 ≤ (Complex.exp (4*q)).re ∧
    |q.re-w.re| ≤ 1 at hd
  have heq : complexSlope t q-modelDerivative t q=
      kernelDerivative q/kernelComplex q-(9-4*(Real.pi : ℂ)*Complex.exp (4*q)) := by
    unfold complexSlope modelDerivative
    rw [(kernelComplex_hasDerivAt q (by linarith [hd.2.1])).deriv]
    ring
  change ‖complexSlope t q-modelDerivative t q‖ ≤ _
  rw [heq]
  apply (RiemannQuarticSaddleNeighborhood.logDerivative_coarse_bound q hd.1 hd.2.1).trans
  have hcub : 1024*w.re ≤ w.re^3 := by
    have hsq : 1024 ≤ w.re^2 := by nlinarith
    have h := mul_le_mul_of_nonneg_right hsq (by linarith : 0 ≤ w.re)
    nlinarith
  have htcub : w.re^3 ≤ t*w.re^3 := by nlinarith [pow_nonneg (by linarith : 0 ≤ w.re) 3]
  have hpi := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (by linarith [hd.2.1] : 0 ≤ (Complex.exp (4*q)).re)
  have hlo := (abs_le.mp hd.2.2.2).1
  have hhi := (abs_le.mp hd.2.2.2).2
  have h1 : Real.exp (-4*q.re) ≤ Real.exp (-4*w.re+4) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (4*q.re)*Real.exp (-3*Real.pi*(Complex.exp (4*q)).re) ≤ Real.exp (-4*w.re+4) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hd.2.2.1]
  have hh1 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ)≤5)
  have hh2 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ)≤30000)
  nlinarith



theorem horizontal_slope_continuousOn (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c‖) (w v : ℂ)
    (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖)
    (z : ℂ) : ContinuousOn (fun a : ℝ => complexSlope t (v+(a : ℂ))+Complex.I*z)
      (Ioo (-(1/16 : ℝ)) (1/16)) := by
  intro a ha
  have had : |a| ≤ 1/16 := (abs_lt.mpr ha).le
  have hd := horizontal_neighbor_domain t c hcenter ht hx w v hr hi hs hp hv a had
  have hka := kernelComplex_analyticAt (v+(a : ℂ)) (by linarith [hd.2.1])
  have hkn := kernel_ne_zero (v+(a : ℂ)) hd.1 hd.2.1
  have hsa : AnalyticAt ℂ (complexSlope t) (v+(a : ℂ)) :=
    (analyticAt_const.mul (analyticAt_id.pow 3)).add (hka.deriv.div hka hkn)
  have hc : ContinuousAt (fun b : ℝ => complexSlope t (v+(b : ℂ))) a :=
    ContinuousAt.comp (g := complexSlope t) (f := fun b : ℝ => v+(b : ℂ))
      hsa.continuousAt (by fun_prop)
  exact (hc.add continuousAt_const).continuousWithinAt



theorem actual_horizontal_phase (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c‖) (w v : ℂ)
    (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖)
    (z : ℂ) (s : ℝ) (hsr : |s| < 1/16) :
    saddleWeight t z (v+(s : ℂ))=saddleWeight t z v*
      Complex.exp (∫ a : ℝ in 0..s, complexSlope t (v+(a : ℂ))+Complex.I*z) := by
  have hH := horizontal_slope_continuousOn t c hcenter ht hx w v hr hi hs hp hv z
  have hW : ∀ a ∈ Ioo (-(1/16 : ℝ)) (1/16),
      HasDerivAt (fun a : ℝ => saddleWeight t z (v+(a : ℂ)))
        ((complexSlope t (v+(a : ℂ))+Complex.I*z)*saddleWeight t z (v+(a : ℂ))) a := by
    intro a ha
    have hd := horizontal_neighbor_domain t c hcenter ht hx w v hr hi hs hp hv a (abs_lt.mpr ha).le
    have hkn := kernel_ne_zero (v+(a : ℂ)) hd.1 hd.2.1
    have h := (RiemannQuarticSpatialPhase.spatial_weight_hasDerivAt t z (v+(a : ℂ))
      (by linarith [hd.2.1]) hkn).comp (a : ℂ) ((hasDerivAt_id (a : ℂ)).const_add v)
    have he : HasDerivAt (fun a : ℂ => saddleWeight t z (v+a))
        ((complexSlope t (v+(a : ℂ))+Complex.I*z)*saddleWeight t z (v+(a : ℂ))) (a : ℂ) := by
      convert h using 1 <;> first | rfl | simp only [mul_one]
    exact he.comp_ofReal
  simpa only [Complex.ofReal_zero,add_zero] using normalized_real_ode
    (fun a : ℝ => saddleWeight t z (v+(a : ℂ)))
    (fun a : ℝ => complexSlope t (v+(a : ℂ))+Complex.I*z)
    (1/16) (by norm_num) hH hW s (abs_lt.mp hsr)




theorem actual_phase_model_error (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c‖) (w v : ℂ)
    (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖)
    (z : ℂ) (s : ℝ) (hsr : |s| < 1/16) :
    ‖(∫ a : ℝ in 0..s, complexSlope t (v+(a : ℂ))+Complex.I*z)-leadingPhase t z v (s : ℂ)‖ ≤
      (30005*Real.exp (-4*w.re+4))*|s| := by
  have hH := horizontal_slope_continuousOn t c hcenter ht hx w v hr hi hs hp hv z
  have hsub : uIcc (0 : ℝ) s ⊆ Ioo (-(1/16 : ℝ)) (1/16) := by
    intro a ha
    rcases le_total 0 s with h | h
    · rw [uIcc_of_le h] at ha
      constructor <;> linarith [(abs_lt.mp hsr).1,(abs_lt.mp hsr).2,ha.1,ha.2]
    · rw [uIcc_of_ge h] at ha
      constructor <;> linarith [(abs_lt.mp hsr).1,(abs_lt.mp hsr).2,ha.1,ha.2]
  have hA : IntervalIntegrable (fun a : ℝ => complexSlope t (v+(a : ℂ))+Complex.I*z) volume 0 s :=
    (hH.mono hsub).intervalIntegrable
  have hM : IntervalIntegrable (fun a : ℝ => modelDerivative t (v+(a : ℂ))+Complex.I*z) volume 0 s := by
    apply Continuous.intervalIntegrable
    unfold modelDerivative
    fun_prop
  rw [← leadingPhase_integral t z v s,← intervalIntegral.integral_sub hA hM]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := s)
    (f := fun a : ℝ => (complexSlope t (v+(a : ℂ))+Complex.I*z)-
      (modelDerivative t (v+(a : ℂ))+Complex.I*z))
    (C := 30005*Real.exp (-4*w.re+4)) (fun a ha => ?_)
  · simpa only [sub_zero] using h
  · have had := hsub (uIoc_subset_uIcc ha)
    have he := horizontal_neighbor_error t c hcenter ht hx w v hr hi hs hp hv a (abs_lt.mpr had).le
    convert he using 1 <;> congr 1 <;> ring



theorem actual_weight_leading_error (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c‖) (w v : ℂ)
    (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖)
    (z : ℂ) (s : ℝ) (hsr : |s| < 1/16)
    (hsmall : (30005*Real.exp (-4*w.re+4))*|s| ≤ 1) :
    ‖saddleWeight t z (v+(s : ℂ))/(saddleWeight t z v*Complex.exp (leadingPhase t z v (s : ℂ)))-1‖ ≤
      (60010*Real.exp (-4*w.re+4))*|s| := by
  have hd := horizontal_neighbor_domain t c hcenter ht hx w v hr hi hs hp hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hd
  have hn : saddleWeight t z v ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _)
    (kernel_ne_zero v hd.1 hd.2.1)
  rw [actual_horizontal_phase t c hcenter ht hx w v hr hi hs hp hv z s hsr,
    mul_div_mul_left _ _ hn,← Complex.exp_sub]
  have he := actual_phase_model_error t c hcenter ht hx w v hr hi hs hp hv z s hsr
  have hh := Complex.norm_exp_sub_one_le (he.trans hsmall)
  nlinarith




theorem horizontal_model_curvature (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c‖) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖) (s : ℝ) (hsr : |s| ≤ 1/16) :
    (deriv (modelDerivative t) (v+(s : ℂ))).re ≤ -(t*w.re^3)/4 := by
  let q := v+(s : ℂ)
  have hd := horizontal_neighbor_domain t c hcenter ht hx w v (by linarith) hi hs hp hv s hsr
  change 0 ≤ q.re ∧ 1 ≤ (Complex.exp (4*q)).re ∧ t*w.re^3/64 ≤ (Complex.exp (4*q)).re ∧
    |q.re-w.re| ≤ 1 at hd
  have ht0 : 0 ≤ t := by linarith
  have hr0 : 0 ≤ w.re := by linarith
  have hq : q.re ≤ w.re+1 := by linarith [(abs_le.mp hd.2.2.2).2]
  have hqs := pow_le_pow_left₀ hd.1 hq 2
  have hsq : q.re^2 ≤ 2*w.re^2 := by nlinarith
  have hcube : 64*w.re^2 ≤ w.re^3 := by nlinarith [mul_nonneg (by linarith : 0 ≤ w.re-64) (sq_nonneg w.re)]
  have hmul1 := mul_le_mul_of_nonneg_left hsq ht0
  have hmul2 := mul_le_mul_of_nonneg_left hcube ht0
  have hpoly : 12*t*(q.re^2-q.im^2) ≤ (3/8 : ℝ)*t*w.re^3 := by
    nlinarith [mul_nonneg ht0 (sq_nonneg q.im)]
  have hpi := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (by linarith [hd.2.1] : 0 ≤ (Complex.exp (4*q)).re)
  have hid : (deriv (modelDerivative t) q).re=
      12*t*(q.re^2-q.im^2)-16*Real.pi*(Complex.exp (4*q)).re := by
    rw [(modelDerivative_hasDerivAt t q).deriv]
    simp [pow_two,Complex.sub_re,Complex.mul_re,Complex.mul_im]
  change (deriv (modelDerivative t) q).re ≤ _
  rw [hid]
  nlinarith [hd.2.2.1,pow_nonneg hr0 3]




theorem leadingPhase_re_le (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c‖) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖)
    (z : ℂ) (hstat : complexSlope t v= -(Complex.I*z)) (s : ℝ) (hsr : |s| < 1/16) :
    (leadingPhase t z v (s : ℂ)).re ≤ (30005*Real.exp (-4*w.re+4))*|s| := by
  let f := fun a : ℝ => (leadingPhase t z v (a : ℂ)).re
  let f1 := fun a : ℝ => (modelDerivative t (v+(a : ℂ))+Complex.I*z).re
  let f2 := fun a : ℝ => (deriv (modelDerivative t) (v+(a : ℂ))).re
  have h1 (a : ℝ) : HasDerivAt f (f1 a) a := (leadingPhase_hasDerivAt t z v (a : ℂ)).real_of_complex
  have h2 (a : ℝ) : HasDerivAt f1 (f2 a) a := by
    have hm := modelDerivative_hasDerivAt t (v+(a : ℂ))
    have h := (hm.comp (a : ℂ) ((hasDerivAt_id (a : ℂ)).const_add v)).add_const (Complex.I*z)
    have hc : HasDerivAt (fun u : ℂ => modelDerivative t (v+u)+Complex.I*z)
        (deriv (modelDerivative t) (v+(a : ℂ))) (a : ℂ) := by
      convert h using 1 <;> first | rfl | simp only [hm.deriv,mul_one]
    exact hc.real_of_complex
  have hf0 : f 0=0 := by simp [f,leadingPhase_zero]
  have hzero : (0 : ℝ) ∈ Ioo (-(1/16 : ℝ)) (1/16) := by norm_num
  have hs' : s ∈ Ioo (-(1/16 : ℝ)) (1/16) := abs_lt.mp hsr
  have hc : ConcaveOn ℝ (Ioo (-(1/16 : ℝ)) (1/16)) f := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := f1) (f'' := f2)
      (convex_Ioo _ _) (fun a _ => (h1 a).continuousAt.continuousWithinAt)
      (fun a _ => (h1 a).hasDerivWithinAt) (fun a _ => (h2 a).hasDerivWithinAt)
    intro a ha
    rw [interior_Ioo] at ha
    exact (horizontal_model_curvature t c hcenter ht hx w v hr hi hs hp hv a (abs_lt.mpr ha).le).trans
      (by
        have ht0 : 0 ≤ t := by linarith
        have hr0 : 0 ≤ w.re := by linarith
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by norm_num))
  have htangent : f s ≤ f1 0*s := by
    rcases lt_trichotomy s 0 with hneg | heq | hpos
    · have h := hc.le_slope_of_hasDerivAt hs' hzero hneg (h1 0)
      rw [slope_def_field,hf0] at h
      have hm := (le_div_iff₀ (by linarith : 0 < 0-s)).mp h
      nlinarith
    · subst s
      simp [hf0]
    · have h := hc.slope_le_of_hasDerivAt hzero hs' hpos (h1 0)
      rw [slope_def_field,hf0,sub_zero,sub_zero] at h
      exact (div_le_iff₀ hpos).mp h
  have he := horizontal_neighbor_error t c hcenter ht hx w v (by linarith) hi hs hp hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at he
  have hid : f1 0= -(complexSlope t v-modelDerivative t v).re := by
    have hid : modelDerivative t v+Complex.I*z= -(complexSlope t v-modelDerivative t v) := by rw [hstat]; ring
    simpa only [f1,Complex.ofReal_zero,add_zero,hid,Complex.neg_re]
  have hf1 : |f1 0| ≤ 30005*Real.exp (-4*w.re+4) := by
    rw [hid,abs_neg]
    exact (Complex.abs_re_le_norm _).trans he
  have hmul := mul_le_mul_of_nonneg_right hf1 (abs_nonneg s)
  have hprod : f1 0*s ≤ (30005*Real.exp (-4*w.re+4))*|s| :=
    (le_abs_self _).trans (by rw [abs_mul]; exact hmul)
  exact htangent.trans hprod




theorem actual_weight_leading_absolute_error (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c‖) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖)
    (z : ℂ) (hstat : complexSlope t v= -(Complex.I*z)) (s : ℝ) (hsr : |s| < 1/16)
    (hsmall : (30005*Real.exp (-4*w.re+4))*|s| ≤ 1) :
    ‖saddleWeight t z (v+(s : ℂ))-saddleWeight t z v*Complex.exp (leadingPhase t z v (s : ℂ))‖ ≤
      (180030*Real.exp (-4*w.re+4))*|s| *‖saddleWeight t z v‖ := by
  have hrel := actual_weight_leading_error t c hcenter ht hx w v (by linarith) hi hs hp hv z s hsr hsmall
  have hre := (leadingPhase_re_le t c hcenter ht hx w v hr hi hs hp hv z hstat s hsr).trans hsmall
  have he3 : Real.exp (1 : ℝ) ≤ 3 := Real.exp_one_lt_three.le
  have hexp : ‖Complex.exp (leadingPhase t z v (s : ℂ))‖ ≤ 3 := by
    rw [Complex.norm_exp]
    exact (Real.exp_le_exp.mpr hre).trans he3
  let B := saddleWeight t z v*Complex.exp (leadingPhase t z v (s : ℂ))
  have hd := horizontal_neighbor_domain t c hcenter ht hx w v (by linarith) hi hs hp hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hd
  have hn : saddleWeight t z v ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (kernel_ne_zero v hd.1 hd.2.1)
  have hB : B ≠ 0 := mul_ne_zero hn (Complex.exp_ne_zero _)
  have hBn : ‖B‖ ≤ 3*‖saddleWeight t z v‖ := by
    dsimp [B]
    rw [norm_mul]
    nlinarith [mul_le_mul_of_nonneg_left hexp (norm_nonneg (saddleWeight t z v))]
  have heq : saddleWeight t z (v+(s : ℂ))-B=(saddleWeight t z (v+(s : ℂ))/B-1)*B := by field_simp
  change ‖saddleWeight t z (v+(s : ℂ))-B‖ ≤ _
  rw [heq,norm_mul]
  have h := mul_le_mul hrel hBn (norm_nonneg B) (by positivity : 0 ≤ (60010*Real.exp (-4*w.re+4))*|s|)
  nlinarith



private theorem horizontal_weight_continuousOn (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c‖) (w v : ℂ)
    (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖) (z : ℂ) :
    ContinuousOn (fun a : ℝ => saddleWeight t z (v+(a : ℂ)))
      (Ioo (-(1/16 : ℝ)) (1/16)) := by
  intro a ha
  have hd := horizontal_neighbor_domain t c hcenter ht hx w v hr hi hs hp hv a (abs_lt.mpr ha).le
  have hk := kernelComplex_analyticAt (v+(a : ℂ)) (by linarith [hd.2.1])
  have hw : AnalyticAt ℂ (saddleWeight t z) (v+(a : ℂ)) := by
    unfold saddleWeight
    apply AnalyticAt.mul
    · fun_prop
    · exact hk
  have hc : ContinuousAt (fun b : ℝ => saddleWeight t z (v+(b : ℂ))) a :=
    ContinuousAt.comp (g := saddleWeight t z) (f := fun b : ℝ => v+(b : ℂ))
      hw.continuousAt (by fun_prop)
  exact hc.continuousWithinAt



theorem signed_local_leading_error (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c‖) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖)
    (z : ℂ) (hstat : complexSlope t v= -(Complex.I*z)) (r : ℝ) (hr0 : 0 ≤ r) (hrr : r < 1/16)
    (hsmall : (30005*Real.exp (-4*w.re+4))*r ≤ 1) :
    ‖(∫ s : ℝ in -r..r, saddleWeight t z (v+(s : ℂ)))-
      saddleWeight t z v*(∫ s : ℝ in -r..r, Complex.exp (leadingPhase t z v (s : ℂ)))‖ ≤
      (360060*Real.exp (-4*w.re+4))*r^2*‖saddleWeight t z v‖ := by
  have hsub : uIcc (-r) r ⊆ Ioo (-(1/16 : ℝ)) (1/16) := by
    intro a ha
    rw [uIcc_of_le (by linarith : -r ≤ r)] at ha
    constructor <;> linarith [ha.1,ha.2]
  have hf : IntervalIntegrable (fun s : ℝ => saddleWeight t z (v+(s : ℂ))) volume (-r) r :=
    ((horizontal_weight_continuousOn t c hcenter ht hx w v (by linarith) hi hs hp hv z).mono hsub).intervalIntegrable
  have hg : IntervalIntegrable (fun s : ℝ => saddleWeight t z v*Complex.exp (leadingPhase t z v (s : ℂ))) volume (-r) r := by
    apply Continuous.intervalIntegrable
    unfold leadingPhase
    fun_prop
  rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_sub hf hg]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := -r) (b := r)
    (f := fun s : ℝ => saddleWeight t z (v+(s : ℂ))-saddleWeight t z v*Complex.exp (leadingPhase t z v (s : ℂ)))
    (C := (180030*Real.exp (-4*w.re+4))*r*‖saddleWeight t z v‖) (fun s hsi => ?_)
  · rw [show r-(-r)=2*r by ring,abs_of_nonneg (by positivity : 0 ≤ 2*r)] at hb
    convert hb using 1 <;> ring
  · rw [uIoc_of_le (by linarith : -r ≤ r)] at hsi
    have habs : |s| ≤ r := abs_le.mpr ⟨hsi.1.le,hsi.2⟩
    have hsm : (30005*Real.exp (-4*w.re+4))*|s| ≤ 1 :=
      (mul_le_mul_of_nonneg_left habs (by positivity)).trans hsmall
    exact (actual_weight_leading_absolute_error t c hcenter ht hx w v hr hi hs hp hv z hstat s
      (habs.trans_lt hrr) hsm).trans (by gcongr)



theorem corrected_exp_norm (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 0 ≤ t) (hx : 8 ≤ ‖c‖) (w v : ℂ)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖) :
    ‖Complex.exp (4*v)‖ ≤ 2*‖c‖ := by
  have hx0 : 0 < ‖c‖ := by linarith
  have hE := RiemannQuarticComplexCorrection.model_exp_norm_le_frequency t c ht hx0 w hp hs
  have hq : 1/‖c‖ ≤ (1/4 : ℝ) := (div_le_iff₀ hx0).mpr (by linarith)
  have hsmall : 4*‖v-w‖ ≤ 1 := by linarith
  have he := exp4_difference_bound w v hsmall
  have hm := mul_le_mul hE hv (norm_nonneg _) hx0.le
  have hcancel : ‖c‖*(1/‖c‖)=1 := by field_simp
  have he8 : ‖Complex.exp (4*v)-Complex.exp (4*w)‖ ≤ 8 := by nlinarith
  have htri := norm_add_le (Complex.exp (4*v)-Complex.exp (4*w)) (Complex.exp (4*w))
  rw [sub_add_cancel] at htri
  linarith



theorem corrected_polynomial_scale (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c‖) (w v : ℂ)
    (hr : 64 ≤ w.re) (hp : 4*t*‖w‖^3+9 ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖) :
    t*(4*‖v‖+1) ≤ ‖c‖ := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 < ‖c‖ := by linarith
  have hN : 64 ≤ ‖w‖ := hr.trans (Complex.re_le_norm w)
  have hv1 : ‖v-w‖ ≤ 1 := hv.trans ((div_le_iff₀ hx0).mpr (by linarith))
  have htri := norm_add_le (v-w) w
  rw [sub_add_cancel] at htri
  have hnorm : ‖v‖ ≤ ‖w‖+1 := by linarith
  have hN2 : 4 ≤ ‖w‖^2 := by nlinarith
  have hN3 : 4*‖w‖ ≤ ‖w‖^3 := by
    have hm := mul_le_mul_of_nonneg_right hN2 (norm_nonneg w)
    nlinarith
  have hc : 4*‖v‖+1 ≤ 4*‖w‖^3 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hc ht0
  nlinarith



theorem leadingPhase_cubic_bound (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c‖) (w v : ℂ)
    (hr : 64 ≤ w.re) (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖) (z u : ℂ) (hu : ‖u‖ ≤ 1/16) :
    ‖leadingPhase t z v u-(modelDerivative t v+Complex.I*z)*u-
      deriv (modelDerivative t) v*u^2/2‖ ≤ 2048*‖c‖*‖u‖^3 := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 ≤ ‖c‖ := by linarith
  have he := exponential_cubic_remainder u hu
  have hE := corrected_exp_norm t c hcenter ht0 hx w v hs hp hv
  have hP := corrected_polynomial_scale t c hcenter ht hx w v hr hp hv
  have hunit : ‖u‖ ≤ 1 := by linarith
  have heq : Complex.exp (4*(v+u))=Complex.exp (4*v)*Complex.exp (4*u) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hid : leadingPhase t z v u-(modelDerivative t v+Complex.I*z)*u-
      deriv (modelDerivative t) v*u^2/2=
      (t : ℂ)*(4*v+u)*u^3-(Real.pi : ℂ)*Complex.exp (4*v)*(Complex.exp (4*u)-1-4*u-8*u^2) := by
    rw [leadingPhase,(modelDerivative_hasDerivAt t v).deriv,heq]
    unfold modelDerivative
    ring
  rw [hid]
  have htri := norm_sub_le ((t : ℂ)*(4*v+u)*u^3)
    ((Real.pi : ℂ)*Complex.exp (4*v)*(Complex.exp (4*u)-1-4*u-8*u^2))
  have hadd := norm_add_le (4*v) u
  simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ht0,abs_of_pos Real.pi_pos] at htri hadd
  have hpoly : t*‖4*v+u‖ ≤ ‖c‖ := by
    have hm := mul_le_mul_of_nonneg_left (by linarith : ‖4*v+u‖ ≤ 4*‖v‖+1) ht0
    exact hm.trans hP
  have hpoly3 := mul_le_mul_of_nonneg_right hpoly (pow_nonneg (norm_nonneg u) 3)
  have hpe := mul_le_mul Real.pi_lt_four.le hE (norm_nonneg _) (by norm_num : (0 : ℝ)≤4)
  have hrem := mul_le_mul hpe he (norm_nonneg _) (by positivity : 0 ≤ 4*(2*‖c‖))
  nlinarith [pow_nonneg (norm_nonneg u) 3]




theorem model_gaussian_coefficient_pos (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c‖) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖) :
    0 < (-(deriv (modelDerivative t) v)/2).re := by
  have h := horizontal_model_curvature t c hcenter ht hx w v hr hi hs hp hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at h
  simp only [Complex.div_ofNat_re,Complex.neg_re]
  have ht0 : 0 < t := by linarith
  have hr0 : 0 < w.re := by linarith
  have hp0 : 0 < t*w.re^3 := by positivity
  linarith



theorem quadratic_norm_le_one (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c‖) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖) (s : ℝ) :
    ‖Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)‖ ≤ 1 := by
  have h := GaussianOscillatoryTail.gaussian_norm_le_one (-(deriv (modelDerivative t) v)/2)
    (model_gaussian_coefficient_pos t c hcenter ht hx w v hr hi hs hp hv).le s
  convert h using 1 <;> congr 1 <;> ring



theorem leadingPhase_quadratic_bound (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c‖) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖)
    (z : ℂ) (hstat : complexSlope t v= -(Complex.I*z)) (s : ℝ) (hsr : |s| ≤ 1/16) :
    ‖leadingPhase t z v (s : ℂ)-deriv (modelDerivative t) v*(s : ℂ)^2/2‖ ≤
      (30005*Real.exp (-4*w.re+4))*|s|+2048*‖c‖*|s|^3 := by
  have hc := leadingPhase_cubic_bound t c hcenter ht hx w v hr hs hp hv z (s : ℂ) (by simpa using hsr)
  simp only [Complex.norm_real,Real.norm_eq_abs] at hc
  have he := horizontal_neighbor_error t c hcenter ht hx w v (by linarith) hi hs hp hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at he
  have hid : modelDerivative t v+Complex.I*z= -(complexSlope t v-modelDerivative t v) := by rw [hstat]; ring
  have hlin : ‖(modelDerivative t v+Complex.I*z)*(s : ℂ)‖ ≤ (30005*Real.exp (-4*w.re+4))*|s| := by
    rw [norm_mul,hid,norm_neg,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right he (abs_nonneg s)
  have htri := norm_add_le
    (leadingPhase t z v (s : ℂ)-(modelDerivative t v+Complex.I*z)*(s : ℂ)-deriv (modelDerivative t) v*(s : ℂ)^2/2)
    ((modelDerivative t v+Complex.I*z)*(s : ℂ))
  have halg : leadingPhase t z v (s : ℂ)-(modelDerivative t v+Complex.I*z)*(s : ℂ)-deriv (modelDerivative t) v*(s : ℂ)^2/2+
      (modelDerivative t v+Complex.I*z)*(s : ℂ)=leadingPhase t z v (s : ℂ)-deriv (modelDerivative t) v*(s : ℂ)^2/2 := by ring
  rw [halg] at htri
  linarith



theorem leading_quadratic_weight_error (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c‖) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖)
    (z : ℂ) (hstat : complexSlope t v= -(Complex.I*z)) (s : ℝ) (hsr : |s| ≤ 1/16)
    (hsmall : (30005*Real.exp (-4*w.re+4))*|s|+2048*‖c‖*|s|^3 ≤ 1) :
    ‖Complex.exp (leadingPhase t z v (s : ℂ))-Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)‖ ≤
      2*((30005*Real.exp (-4*w.re+4))*|s|+2048*‖c‖*|s|^3) := by
  let P := leadingPhase t z v (s : ℂ)
  let Q := deriv (modelDerivative t) v*(s : ℂ)^2/2
  have he := Complex.norm_exp_sub_one_le
    ((leadingPhase_quadratic_bound t c hcenter ht hx w v hr hi hs hp hv z hstat s hsr).trans hsmall)
  have hQ := quadratic_norm_le_one t c hcenter ht hx w v hr hi hs hp hv s
  have hid : Complex.exp P-Complex.exp Q=Complex.exp Q*(Complex.exp (P-Q)-1) := by
    rw [mul_sub,mul_one,← Complex.exp_add]
    congr 1
    ring
  change ‖Complex.exp P-Complex.exp Q‖ ≤ _
  rw [hid,norm_mul]
  have hpq := leadingPhase_quadratic_bound t c hcenter ht hx w v hr hi hs hp hv z hstat s hsr
  change ‖Complex.exp (P-Q)-1‖ ≤ 2*‖P-Q‖ at he
  change ‖Complex.exp Q‖ ≤ 1 at hQ
  have hmul := mul_le_mul_of_nonneg_right hQ (norm_nonneg (Complex.exp (P-Q)-1))
  nlinarith



theorem leading_local_quadratic_error (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c‖) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖)
    (z : ℂ) (hstat : complexSlope t v= -(Complex.I*z)) (r : ℝ) (hr0 : 0 ≤ r) (hrr : r < 1/16)
    (hsmall : (30005*Real.exp (-4*w.re+4))*r+2048*‖c‖*r^3 ≤ 1) :
    ‖(∫ s : ℝ in -r..r, Complex.exp (leadingPhase t z v (s : ℂ)))-
      (∫ s : ℝ in -r..r, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2))‖ ≤
      4*(30005*Real.exp (-4*w.re+4))*r^2+8192*‖c‖*r^4 := by
  have hf : IntervalIntegrable (fun s : ℝ => Complex.exp (leadingPhase t z v (s : ℂ))) volume (-r) r := by
    apply Continuous.intervalIntegrable
    unfold leadingPhase
    fun_prop
  have hg : IntervalIntegrable (fun s : ℝ => Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)) volume (-r) r :=
    (by fun_prop : Continuous (fun s : ℝ => Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2))).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub hf hg]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := -r) (b := r)
    (f := fun s : ℝ => Complex.exp (leadingPhase t z v (s : ℂ))-Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2))
    (C := 2*((30005*Real.exp (-4*w.re+4))*r+2048*‖c‖*r^3)) (fun s hsi => ?_)
  · rw [show r-(-r)=2*r by ring,abs_of_nonneg (by positivity : 0 ≤ 2*r)] at hb
    convert hb using 1 <;> ring
  · rw [uIoc_of_le (by linarith : -r ≤ r)] at hsi
    have habs : |s| ≤ r := abs_le.mpr ⟨hsi.1.le,hsi.2⟩
    have hpow := pow_le_pow_left₀ (abs_nonneg s) habs 3
    have h1 := mul_le_mul_of_nonneg_left habs (by positivity : 0 ≤ 30005*Real.exp (-4*w.re+4))
    have h2 := mul_le_mul_of_nonneg_left hpow (by linarith : 0 ≤ 2048*‖c‖)
    have hsm : (30005*Real.exp (-4*w.re+4))*|s|+2048*‖c‖*|s|^3 ≤ 1 := by linarith
    exact (leading_quadratic_weight_error t c hcenter ht hx w v hr hi hs hp hv z hstat s
      (habs.trans hrr.le) hsm).trans (by linarith)




theorem actual_local_quadratic_error (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c‖) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖)
    (z : ℂ) (hstat : complexSlope t v= -(Complex.I*z)) (r : ℝ) (hr0 : 0 ≤ r) (hrr : r < 1/16)
    (hsmall : (30005*Real.exp (-4*w.re+4))*r+2048*‖c‖*r^3 ≤ 1) :
    ‖(∫ s : ℝ in -r..r, saddleWeight t z (v+(s : ℂ)))-
      saddleWeight t z v*(∫ s : ℝ in -r..r, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2))‖ ≤
      (16*(30005*Real.exp (-4*w.re+4))*r^2+8192*‖c‖*r^4)*‖saddleWeight t z v‖ := by
  have hx0 : 0 ≤ ‖c‖ := by linarith
  have heps : (30005*Real.exp (-4*w.re+4))*r ≤ 1 := by
    nlinarith [mul_nonneg hx0 (pow_nonneg hr0 3)]
  have ha := signed_local_leading_error t c hcenter ht hx w v hr hi hs hp hv z hstat r hr0 hrr heps
  have hl := leading_local_quadratic_error t c hcenter ht hx w v hr hi hs hp hv z hstat r hr0 hrr hsmall
  let W := saddleWeight t z v
  let L := ∫ s : ℝ in -r..r, saddleWeight t z (v+(s : ℂ))
  let M := ∫ s : ℝ in -r..r, Complex.exp (leadingPhase t z v (s : ℂ))
  let G := ∫ s : ℝ in -r..r, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)
  have he : L-W*G=(L-W*M)+W*(M-G) := by ring
  change ‖L-W*G‖ ≤ _
  rw [he]
  have hn := norm_add_le (L-W*M) (W*(M-G))
  rw [norm_mul] at hn
  have hm := mul_le_mul_of_nonneg_left hl (norm_nonneg W)
  change ‖L-W*M‖ ≤ _ at ha
  change ‖W‖*‖M-G‖ ≤ _ at hm
  nlinarith



theorem actual_local_full_gaussian_error (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c‖) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖)
    (z : ℂ) (hstat : complexSlope t v= -(Complex.I*z)) (r : ℝ) (hr0 : 0 < r) (hrr : r < 1/16)
    (hsmall : (30005*Real.exp (-4*w.re+4))*r+2048*‖c‖*r^3 ≤ 1) :
    ‖(∫ s : ℝ in -r..r, saddleWeight t z (v+(s : ℂ)))-
      saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2))‖ ≤
      ‖saddleWeight t z v‖*(16*(30005*Real.exp (-4*w.re+4))*r^2+8192*‖c‖*r^4+
        2/(‖-(deriv (modelDerivative t) v)/2‖*r)) := by
  let b := -(deriv (modelDerivative t) v)/2
  have hb : 0 < b.re := model_gaussian_coefficient_pos t c hcenter ht hx w v hr hi hs hp hv
  have htail := GaussianOscillatoryTail.full_minus_truncated_bound b hb r hr0
  have hfun : (fun s : ℝ => Complex.exp (-b*(s : ℂ)^2))=
      (fun s : ℝ => Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)) := by
    funext s
    congr 1
    dsimp [b]
    ring
  rw [hfun] at htail
  have hl := actual_local_quadratic_error t c hcenter ht hx w v hr hi hs hp hv z hstat r hr0.le hrr hsmall
  let W := saddleWeight t z v
  let L := ∫ s : ℝ in -r..r, saddleWeight t z (v+(s : ℂ))
  let G0 := ∫ s : ℝ in -r..r, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)
  let G := ∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)
  have he : L-W*G=(L-W*G0)+W*(G0-G) := by ring
  change ‖L-W*G‖ ≤ _
  rw [he]
  have hn := norm_add_le (L-W*G0) (W*(G0-G))
  rw [norm_mul,norm_sub_rev G0 G] at hn
  have hm := mul_le_mul_of_nonneg_left htail (norm_nonneg W)
  change ‖L-W*G0‖ ≤ _ at hl
  change ‖W‖*‖G-G0‖ ≤ _ at hm
  nlinarith



theorem full_gaussian_formula (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c‖) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖) :
    (∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2))=
      ((Real.pi : ℂ)/(-(deriv (modelDerivative t) v)/2))^(1/2 : ℂ) := by
  have h := integral_gaussian_complex (model_gaussian_coefficient_pos t c hcenter ht hx w v hr hi hs hp hv)
  convert h using 1 <;> congr 1 <;> ring



private theorem polynomial_half (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 0 ≤ t) (w : ℂ)
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ ‖c‖) : 4*t*‖w‖^3+9 ≤ ‖c‖/2 := by
  have hpw := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hm := mul_le_mul_of_nonneg_left hpw ht
  nlinarith [mul_nonneg ht (pow_nonneg (norm_nonneg w) 3)]



theorem arithmetic_error_frequency_bound (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 10000 ≤ ‖c‖) (w : ℂ)
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ ‖c‖)
    (hs : modelDerivative t w= -(Complex.I*c)) :
    30005*Real.exp (-4*w.re+4) ≤ 100000000/‖c‖ := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 < ‖c‖ := by linarith
  have hpoly := polynomial_half t c hcenter ht0 w hp
  have hn : ‖modelDerivative t w‖=‖c‖ := by
    rw [hs]
    simp only [norm_neg,norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,one_mul]
  have htri := norm_sub_le (4*(t : ℂ)*w^3+9) (4*(Real.pi : ℂ)*Complex.exp (4*w))
  have hadd := norm_add_le (4*(t : ℂ)*w^3) (9 : ℂ)
  change ‖modelDerivative t w‖ ≤ _ at htri
  rw [hn] at htri
  simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ht0,abs_of_pos Real.pi_pos] at htri hadd
  have hpi := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (norm_nonneg (Complex.exp (4*w)))
  have hfreq : ‖c‖ ≤ 32*‖Complex.exp (4*w)‖ := by nlinarith
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
  have heps : (30005*Real.exp (-4*w.re+4))*‖c‖ ≤ 100000000 := by
    have hm' : ‖c‖*Real.exp (-4*w.re+4) ≤ 32*Real.exp 4 := by nlinarith [heq]
    nlinarith
  exact (le_div_iff₀ hx0).mpr heps



theorem gaussian_coefficient_norm_bounds (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 10000 ≤ ‖c‖) (w v : ℂ)
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ ‖c‖)
    (hs : modelDerivative t w= -(Complex.I*c)) (hv : ‖v-w‖ ≤ 1/‖c‖) :
    ‖c‖ ≤ ‖-(deriv (modelDerivative t) v)/2‖ ∧ ‖-(deriv (modelDerivative t) v)/2‖ ≤ 4*‖c‖ := by
  have hx0 : 0 < ‖c‖ := by linarith
  let A := -(4 : ℂ)*Complex.I*c
  have hA : ‖A‖=4*‖c‖ := by
    simp only [A,norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_I,
      Complex.norm_real,Real.norm_eq_abs,mul_one]
  have hnear := RiemannQuarticComplexCorrection.model_deriv_near_far_saddle t c ht hx w v hp hs hv
  change ‖deriv (modelDerivative t) v-A‖ ≤ ‖c‖ at hnear
  have hu := norm_add_le (deriv (modelDerivative t) v-A) A
  rw [sub_add_cancel,hA] at hu
  have hl := norm_sub_le (deriv (modelDerivative t) v) (deriv (modelDerivative t) v-A)
  rw [sub_sub_cancel,hA] at hl
  rw [norm_div,norm_neg,Complex.norm_ofNat]
  constructor <;> linarith



theorem gaussian_normalization_lower (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 10000 ≤ ‖c‖) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ ‖c‖)
    (hs : modelDerivative t w= -(Complex.I*c)) (hv : ‖v-w‖ ≤ 1/‖c‖) :
    1 ≤ 2*Real.sqrt ‖c‖*‖∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)‖ := by
  have hx0 : 0 < ‖c‖ := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hp0 : 4*t*‖w‖^3+9 ≤ ‖c‖ := (polynomial_half t c hcenter ht0 w hp).trans (by linarith)
  let b := -(deriv (modelDerivative t) v)/2
  have hb : 0 < b.re := model_gaussian_coefficient_pos t c hcenter ht (by linarith) w v hr hi hs hp0 hv
  have hn := (gaussian_coefficient_norm_bounds t c hcenter ht hx w v hp hs hv).2
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
  have hprod : 0 ≤ 2*Real.sqrt ‖c‖*g := by positivity
  have hsquare : 1 ≤ (2*Real.sqrt ‖c‖*g)^2 := by
    calc
      _ ≤ Real.pi := by linarith [Real.pi_gt_three]
      _ ≤ g^2*(4*‖c‖) := by nlinarith [hid,hm]
      _ = _ := by rw [mul_pow,mul_pow,hroot]; ring
  change 1 ≤ 2*Real.sqrt ‖c‖*g
  nlinarith




theorem relative_local_error_bound (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 10000 ≤ ‖c‖) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ ‖c‖)
    (hs : modelDerivative t w= -(Complex.I*c)) (hv : ‖v-w‖ ≤ 1/‖c‖)
    (z : ℂ) (hstat : complexSlope t v= -(Complex.I*z)) (r : ℝ) (hr0 : 0 < r) (hrr : r < 1/16)
    (hsmall : (30005*Real.exp (-4*w.re+4))*r+2048*‖c‖*r^3 ≤ 1) :
    ‖(∫ s : ℝ in -r..r, saddleWeight t z (v+(s : ℂ)))/
      (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))-1‖ ≤
      2*Real.sqrt ‖c‖*(16*(30005*Real.exp (-4*w.re+4))*r^2+8192*‖c‖*r^4+2/(‖c‖*r)) := by
  have hx0 : 0 < ‖c‖ := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hp0 : 4*t*‖w‖^3+9 ≤ ‖c‖ := (polynomial_half t c hcenter ht0 w hp).trans (by linarith)
  have he := actual_local_full_gaussian_error t c hcenter ht (by linarith) w v hr hi hs hp0 hv z hstat r hr0 hrr hsmall
  have hnormb := (gaussian_coefficient_norm_bounds t c hcenter ht hx w v hp hs hv).1
  have htail : 2/(‖-(deriv (modelDerivative t) v)/2‖*r) ≤ 2/(‖c‖*r) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos hx0 hr0)
      (mul_le_mul_of_nonneg_right hnormb hr0.le)
  let W := saddleWeight t z v
  let G := ∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)
  let L := ∫ s : ℝ in -r..r, saddleWeight t z (v+(s : ℂ))
  let B := 16*(30005*Real.exp (-4*w.re+4))*r^2+8192*‖c‖*r^4+2/(‖c‖*r)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hnum : ‖L-W*G‖ ≤ ‖W‖*B := by
    apply he.trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg W)
    dsimp [B]
    linarith
  have hnormal := gaussian_normalization_lower t c hcenter ht hx w v hr hi hp hs hv
  change 1 ≤ 2*Real.sqrt ‖c‖*‖G‖ at hnormal
  have hG : G ≠ 0 := by intro h; norm_num [h] at hnormal
  have hd := horizontal_neighbor_domain t c hcenter ht (by linarith) w v (by linarith) hi hs hp0 hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hd
  have hW : W ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _)
    (RiemannThetaComplexKernel.kernel_ne_zero v hd.1 hd.2.1)
  have hden : W*G ≠ 0 := mul_ne_zero hW hG
  have hfrac : L/(W*G)-1=(L-W*G)/(W*G) := by field_simp
  change ‖L/(W*G)-1‖ ≤ _
  rw [hfrac,norm_div,norm_mul]
  apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hW) (norm_pos_iff.mpr hG))).mpr
  have hm := mul_le_mul_of_nonneg_left hnormal (mul_nonneg (norm_nonneg W) hB)
  change ‖L-W*G‖ ≤ (2*Real.sqrt ‖c‖*B)*(‖W‖*‖G‖)
  nlinarith




theorem central_relative_error_bound (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 10000 ≤ ‖c‖) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ ‖c‖)
    (hs : modelDerivative t w= -(Complex.I*c)) (hv : ‖v-w‖ ≤ 1/‖c‖)
    (z : ℂ) (hstat : complexSlope t v= -(Complex.I*z))
    (hrr : centralRadius ‖c‖ < 1/16) (hsmall : smallBudget ‖c‖ ≤ 1) :
    ‖(∫ s : ℝ in -(centralRadius ‖c‖)..centralRadius ‖c‖, saddleWeight t z (v+(s : ℂ)))/
      (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))-1‖ ≤
      relativeBudget ‖c‖ := by
  have hx0 : 0 < ‖c‖ := by linarith
  have hrpos : 0 < centralRadius ‖c‖ := Real.rpow_pos_of_pos hx0 _
  have he := arithmetic_error_frequency_bound t c hcenter ht hx w hp hs
  have hm := mul_le_mul_of_nonneg_right he hrpos.le
  have hsm : (30005*Real.exp (-4*w.re+4))*centralRadius ‖c‖+2048*‖c‖*centralRadius ‖c‖^3 ≤ 1 := by
    change (100000000/‖c‖)*centralRadius ‖c‖+2048*‖c‖*centralRadius ‖c‖^3 ≤ 1 at hsmall
    linarith
  have hc := relative_local_error_bound t c hcenter ht hx w v hr hi hp hs hv z hstat
    (centralRadius ‖c‖) hrpos hrr hsm
  apply hc.trans
  rw [← central_relative_budget ‖c‖ hx0]
  gcongr


theorem uniform_local_gaussian_error (η : ℝ) (hη : 0 < η) :
    ∃ R : ℝ, ∀ c : ℂ, c.im ≤ 0 → R ≤ ‖c‖ → ∀ t : ℝ, 1 ≤ t → ∀ w v : ℂ,
      64 ≤ w.re → |w.im| ≤ 1/2 → 100*(t*(‖w‖+1)^3+1) ≤ ‖c‖ →
      modelDerivative t w = -(Complex.I*c) → ‖v-w‖ ≤ 1/‖c‖ →
      ∀ z : ℂ, complexSlope t v = -(Complex.I*z) →
      ‖(∫ s : ℝ in -(centralRadius ‖c‖)..centralRadius ‖c‖, saddleWeight t z (v+(s : ℂ)))/
        (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))-1‖ ≤ η := by
  have hb : ∀ᶠ r : ℝ in atTop, 10000 ≤ r ∧ centralRadius r < 1/16 ∧
      smallBudget r < 1 ∧ relativeBudget r < η := by
    filter_upwards [eventually_ge_atTop (10000 : ℝ),
      centralRadius_tendsto_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/16)),
      smallBudget_tendsto_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1)),
      relativeBudget_tendsto_zero.eventually (gt_mem_nhds hη)] with r hr hrad hsm hrel
    exact ⟨hr,hrad,hsm,hrel⟩
  obtain ⟨R,hR⟩ := eventually_atTop.mp hb
  refine ⟨R,?_⟩
  intro c hc hlarge t ht w v hr hi hp hs hv z hstat
  have hb := hR ‖c‖ hlarge
  exact (central_relative_error_bound t c hc ht hb.1 w v hr hi hp hs hv z hstat
    hb.2.1 hb.2.2.1.le).trans hb.2.2.2.le

theorem eventually_actual_local_gaussian (t : ℝ) (ht : 1 ≤ t) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ a : ℝ in atTop, ∀ c : ℂ, c.im ≤ 0 → ‖c‖ = 4*Real.pi*Real.exp (4*a) →
      ∃ v : ℂ, complexSlope t v = -(Complex.I*c) ∧
        1 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ kernelComplex v ≠ 0 ∧
        ‖(∫ s : ℝ in -(centralRadius ‖c‖)..centralRadius ‖c‖, saddleWeight t c (v+(s : ℂ)))/
          (saddleWeight t c v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))-1‖ ≤ η := by
  obtain ⟨N,hN⟩ := uniform_local_gaussian_error η hη
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
  have hr : 64 ≤ w.re := by linarith [(abs_le.mp hreal).1]
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
  exact ⟨v,hroot,hrv,hiv,hkn,hN c hc hNc t ht w v hr hi hps hs hclose c hroot⟩

theorem far_actual_local_gaussian (t : ℝ) (ht : 1 ≤ t) (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ c : ℂ, R ≤ ‖c‖ → c.im ≤ 0 → ∃ v : ℂ,
      complexSlope t v = -(Complex.I*c) ∧
      1 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ kernelComplex v ≠ 0 ∧
      ‖(∫ s : ℝ in -(centralRadius ‖c‖)..centralRadius ‖c‖, saddleWeight t c (v+(s : ℂ)))/
        (saddleWeight t c v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))-1‖ ≤ η ∧
      (∫ s : ℝ in -(centralRadius ‖c‖)..centralRadius ‖c‖, saddleWeight t c (v+(s : ℂ))) ≠ 0 := by
  obtain ⟨A,hA⟩ := eventually_atTop.mp (eventually_actual_local_gaussian t ht η hη)
  let R := 4*Real.pi*Real.exp (4*A)
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨R,hR,?_⟩
  intro c hc him
  have hn0 : 0 < ‖c‖ := hR.trans_le hc
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
  obtain ⟨v,hroot,hr,hi,hkn,hrel⟩ := hA a hAa c him hn
  refine ⟨v,hroot,hr,hi,hkn,hrel,?_⟩
  intro hz
  rw [hz,zero_div,zero_sub,norm_neg,norm_one] at hrel
  linarith

end OperatorDerivativeRewrite.Foundation.RiemannQuarticComplexGaussian
