import Foundation.RiemannSixthFarRemainder
import Foundation.RiemannEvenComplexWeight
import Foundation.RiemannQuarticFarSignedIntegral
/-! Actual horizontal phase reconstruction at sixth-order far saddles.
The arithmetic/model mismatch and signed local integral error are explicit. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthFarSignedIntegral
open RiemannSixthFarRemainder RiemannSixthFarCorrection
open RiemannEvenModelPhase RiemannEvenSaddleBranch RiemannEvenComplexWeight
open RiemannThetaComplexKernel
open RiemannQuarticFarSignedIntegral (normalized_real_ode)

theorem spatial_weight_hasDerivAt (t : ℝ) (z v : ℂ)
    (hv : 0 < (Complex.exp (4*v)).re) (hk : kernelComplex v ≠ 0) :
    HasDerivAt (weight 3 t z) ((complexSlope 3 t v+Complex.I*z)*weight 3 t z v) v := by
  have hd := kernelComplex_hasDerivAt v hv
  have hp := (((hasDerivAt_id v).pow 6).const_mul (t : ℂ)).add
    ((hasDerivAt_id v).const_mul (Complex.I*z))
  have h := hp.cexp.mul hd
  convert h using 1
  · funext y; rfl
  · unfold complexSlope weight
    rw [hd.deriv]
    simp only [Pi.add_apply,Pi.mul_apply,Pi.pow_apply,id_eq]
    norm_num
    field_simp [hk]
    ring

private theorem horizontal_segment_subset (R s : ℝ) (hR : 0 < R) (hs : s ∈ Ioo (-R) R) :
    uIcc 0 s ⊆ Ioo (-R) R := by
  intro y hy
  rcases le_total 0 s with h | h
  · rw [uIcc_of_le h] at hy
    constructor <;> linarith [hy.1,hy.2,hs.1,hs.2]
  · rw [uIcc_of_ge h] at hy
    constructor <;> linarith [hy.1,hy.2,hs.1,hs.2]

theorem horizontal_slope_continuousOn (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
    (hp : 6*t*‖w‖^5+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) : ContinuousOn (fun a : ℝ => complexSlope 3 t (v+(a : ℂ))+Complex.I*z)
      (Ioo (-(1/16 : ℝ)) (1/16)) := by
  intro a ha
  have had : |a| ≤ 1/16 := (abs_lt.mpr ha).le
  have hd := horizontal_neighbor_domain t x ht hx w v hr hi hs hp hv a had
  have hka := kernelComplex_analyticAt (v+(a : ℂ)) (by linarith [hd.2.1])
  have hkn := kernel_ne_zero (v+(a : ℂ)) hd.1 hd.2.1
  have hsa : AnalyticAt ℂ (complexSlope 3 t) (v+(a : ℂ)) :=
    (analyticAt_const.mul (analyticAt_id.pow 5)).add (hka.deriv.div hka hkn)
  have hc : ContinuousAt (fun b : ℝ => complexSlope 3 t (v+(b : ℂ))) a :=
    ContinuousAt.comp (g := complexSlope 3 t) (f := fun b : ℝ => v+(b : ℂ))
      hsa.continuousAt (by fun_prop)
  exact (hc.add continuousAt_const).continuousWithinAt

theorem actual_horizontal_phase (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
    (hp : 6*t*‖w‖^5+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (s : ℝ) (hsr : |s| < 1/16) :
    weight 3 t z (v+(s : ℂ))=weight 3 t z v*
      Complex.exp (∫ a : ℝ in 0..s, complexSlope 3 t (v+(a : ℂ))+Complex.I*z) := by
  have hH := horizontal_slope_continuousOn t x ht hx w v hr hi hs hp hv z
  have hW : ∀ a ∈ Ioo (-(1/16 : ℝ)) (1/16),
      HasDerivAt (fun a : ℝ => weight 3 t z (v+(a : ℂ)))
        ((complexSlope 3 t (v+(a : ℂ))+Complex.I*z)*weight 3 t z (v+(a : ℂ))) a := by
    intro a ha
    have hd := horizontal_neighbor_domain t x ht hx w v hr hi hs hp hv a (abs_lt.mpr ha).le
    have hkn := kernel_ne_zero (v+(a : ℂ)) hd.1 hd.2.1
    have h := (spatial_weight_hasDerivAt t z (v+(a : ℂ))
      (by linarith [hd.2.1]) hkn).comp (a : ℂ) ((hasDerivAt_id (a : ℂ)).const_add v)
    have he : HasDerivAt (fun a : ℂ => weight 3 t z (v+a))
        ((complexSlope 3 t (v+(a : ℂ))+Complex.I*z)*weight 3 t z (v+(a : ℂ))) (a : ℂ) := by
      convert h using 1 <;> first | rfl | simp only [mul_one]
    exact he.comp_ofReal
  simpa only [Complex.ofReal_zero,add_zero] using normalized_real_ode
    (fun a : ℝ => weight 3 t z (v+(a : ℂ)))
    (fun a : ℝ => complexSlope 3 t (v+(a : ℂ))+Complex.I*z)
    (1/16) (by norm_num) hH hW s (abs_lt.mp hsr)


def leadingPhase (t : ℝ) (z v u : ℂ) : ℂ :=
  (t : ℂ)*((v+u)^6-v^6)+9*u-(Real.pi : ℂ)*(Complex.exp (4*(v+u))-Complex.exp (4*v))+Complex.I*z*u

theorem leadingPhase_zero (t : ℝ) (z v : ℂ) : leadingPhase t z v 0=0 := by
  simp [leadingPhase]

theorem leadingPhase_hasDerivAt (t : ℝ) (z v u : ℂ) :
    HasDerivAt (leadingPhase t z v) (modelDerivative 3 t (v+u)+Complex.I*z) u := by
  have h1 := ((((hasDerivAt_id u).const_add v).pow 6).sub_const (v^6)).const_mul (t : ℂ)
  have h2 := (hasDerivAt_id u).const_mul (9 : ℂ)
  have h3 := (((((hasDerivAt_id u).const_add v).const_mul (4 : ℂ)).cexp).sub_const
    (Complex.exp (4*v))).const_mul (Real.pi : ℂ)
  have h4 := (hasDerivAt_id u).const_mul (Complex.I*z)
  have h := ((h1.add h2).sub h3).add h4
  convert h using 1
  · funext y; rfl
  · dsimp only [id_eq]
    unfold modelDerivative
    ring

theorem leadingPhase_integral (t : ℝ) (z v : ℂ) (s : ℝ) :
    (∫ a : ℝ in 0..s, modelDerivative 3 t (v+(a : ℂ))+Complex.I*z)=leadingPhase t z v (s : ℂ) := by
  have hc : Continuous (fun a : ℝ => modelDerivative 3 t (v+(a : ℂ))+Complex.I*z) := by
    unfold modelDerivative
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun a _ => (leadingPhase_hasDerivAt t z v (a : ℂ)).comp_ofReal) (hc.intervalIntegrable 0 s)
  simpa only [Complex.ofReal_zero,leadingPhase_zero,sub_zero] using h


theorem actual_phase_model_error (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
    (hp : 6*t*‖w‖^5+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (s : ℝ) (hsr : |s| < 1/16) :
    ‖(∫ a : ℝ in 0..s, complexSlope 3 t (v+(a : ℂ))+Complex.I*z)-leadingPhase t z v (s : ℂ)‖ ≤
      (30005*Real.exp (-4*w.re+4))*|s| := by
  have hH := horizontal_slope_continuousOn t x ht hx w v hr hi hs hp hv z
  have hsub := horizontal_segment_subset (1/16) s (by norm_num) (abs_lt.mp hsr)
  have hA : IntervalIntegrable (fun a : ℝ => complexSlope 3 t (v+(a : ℂ))+Complex.I*z) volume 0 s :=
    (hH.mono hsub).intervalIntegrable
  have hM : IntervalIntegrable (fun a : ℝ => modelDerivative 3 t (v+(a : ℂ))+Complex.I*z) volume 0 s := by
    apply Continuous.intervalIntegrable
    unfold modelDerivative
    fun_prop
  rw [← leadingPhase_integral t z v s,← intervalIntegral.integral_sub hA hM]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := s)
    (f := fun a : ℝ => (complexSlope 3 t (v+(a : ℂ))+Complex.I*z)-
      (modelDerivative 3 t (v+(a : ℂ))+Complex.I*z))
    (C := 30005*Real.exp (-4*w.re+4)) (fun a ha => ?_)
  · simpa only [sub_zero] using h
  · have had := hsub (uIoc_subset_uIcc ha)
    have he := horizontal_neighbor_error t x ht hx w v hr hi hs hp hv a (abs_lt.mpr had).le
    convert he using 1 <;> congr 1 <;> ring

theorem actual_weight_leading_error (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
    (hp : 6*t*‖w‖^5+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (s : ℝ) (hsr : |s| < 1/16)
    (hsmall : (30005*Real.exp (-4*w.re+4))*|s| ≤ 1) :
    ‖weight 3 t z (v+(s : ℂ))/(weight 3 t z v*Complex.exp (leadingPhase t z v (s : ℂ)))-1‖ ≤
      (60010*Real.exp (-4*w.re+4))*|s| := by
  have hd := horizontal_neighbor_domain t x ht hx w v hr hi hs hp hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hd
  have hn : weight 3 t z v ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _)
    (kernel_ne_zero v hd.1 hd.2.1)
  rw [actual_horizontal_phase t x ht hx w v hr hi hs hp hv z s hsr,
    mul_div_mul_left _ _ hn,← Complex.exp_sub]
  have he := actual_phase_model_error t x ht hx w v hr hi hs hp hv z s hsr
  have hh := Complex.norm_exp_sub_one_le (he.trans hsmall)
  nlinarith


theorem horizontal_model_curvature (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 4096 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w = -(Complex.I*(x : ℂ)))
    (hp : 6*t*‖w‖^5+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x) (s : ℝ) (hsr : |s| ≤ 1/16) :
    (deriv (modelDerivative 3 t) (v+(s : ℂ))).re ≤ -(t*w.re^5)/4 := by
  let q := v+(s : ℂ)
  have hd := horizontal_neighbor_domain t x ht hx w v (by linarith) hi hs hp hv s hsr
  change 0 ≤ q.re ∧ 1 ≤ (Complex.exp (4*q)).re ∧ t*w.re^5/64 ≤ (Complex.exp (4*q)).re ∧
    |q.re-w.re| ≤ 1 at hd
  have ht0 : 0 ≤ t := by linarith
  have hr0 : 0 ≤ w.re := by linarith
  have hx0 : 0 < x := by linarith
  have hvsmall : ‖v-w‖ ≤ 1/8 := hv.trans ((div_le_iff₀ hx0).mpr (by linarith))
  have hwNorm := Complex.norm_le_abs_re_add_abs_im w
  rw [abs_of_nonneg hr0] at hwNorm
  have htri := norm_add_le (v-w) w
  rw [sub_add_cancel] at htri
  have hqtri := norm_add_le v (s : ℂ)
  simp only [Complex.norm_real,Real.norm_eq_abs] at hqtri
  have hqnorm : ‖q‖ ≤ 2*w.re := by dsimp [q]; linarith
  have hqpow : ‖q‖^4 ≤ 16*w.re^4 := by
    calc
      _ ≤ (2*w.re)^4 := pow_le_pow_left₀ (norm_nonneg q) hqnorm 4
      _ = _ := by ring
  have hpower : 1920*w.re^4 ≤ w.re^5 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ w.re-1920) (pow_nonneg hr0 4)]
  have hmul1 := mul_le_mul_of_nonneg_left hqpow ht0
  have hmul2 := mul_le_mul_of_nonneg_left hpower ht0
  have hreal := Complex.re_le_norm (q^4)
  rw [norm_pow] at hreal
  have hrealmul := mul_le_mul_of_nonneg_left hreal (by positivity : 0 ≤ 30*t)
  have hid : (deriv (modelDerivative 3 t) q).re =
      30*t*(q^4).re-16*Real.pi*(Complex.exp (4*q)).re := by
    rw [(modelDerivative_hasDerivAt 3 t q).deriv]
    norm_num [Complex.mul_re,Complex.sub_re]
  have hpi := mul_le_mul_of_nonneg_right Real.pi_gt_three.le
    (by linarith [hd.2.1] : 0 ≤ (Complex.exp (4*q)).re)
  change (deriv (modelDerivative 3 t) q).re ≤ _
  rw [hid]
  nlinarith [hd.2.2.1,pow_nonneg hr0 5]


theorem leadingPhase_re_le (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 4096 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
    (hp : 6*t*‖w‖^5+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hstat : complexSlope 3 t v= -(Complex.I*z)) (s : ℝ) (hsr : |s| < 1/16) :
    (leadingPhase t z v (s : ℂ)).re ≤ (30005*Real.exp (-4*w.re+4))*|s| := by
  let f := fun a : ℝ => (leadingPhase t z v (a : ℂ)).re
  let f1 := fun a : ℝ => (modelDerivative 3 t (v+(a : ℂ))+Complex.I*z).re
  let f2 := fun a : ℝ => (deriv (modelDerivative 3 t) (v+(a : ℂ))).re
  have h1 (a : ℝ) : HasDerivAt f (f1 a) a := (leadingPhase_hasDerivAt t z v (a : ℂ)).real_of_complex
  have h2 (a : ℝ) : HasDerivAt f1 (f2 a) a := by
    have hm := modelDerivative_hasDerivAt 3 t (v+(a : ℂ))
    have h := (hm.comp (a : ℂ) ((hasDerivAt_id (a : ℂ)).const_add v)).add_const (Complex.I*z)
    have hc : HasDerivAt (fun u : ℂ => modelDerivative 3 t (v+u)+Complex.I*z)
        (deriv (modelDerivative 3 t) (v+(a : ℂ))) (a : ℂ) := by
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
    exact (horizontal_model_curvature t x ht hx w v hr hi hs hp hv a (abs_lt.mpr ha).le).trans
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
  have he := horizontal_neighbor_error t x ht hx w v (by linarith) hi hs hp hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at he
  have hid : f1 0= -(complexSlope 3 t v-modelDerivative 3 t v).re := by
    have hid : modelDerivative 3 t v+Complex.I*z= -(complexSlope 3 t v-modelDerivative 3 t v) := by rw [hstat]; ring
    simpa only [f1,Complex.ofReal_zero,add_zero,hid,Complex.neg_re]
  have hf1 : |f1 0| ≤ 30005*Real.exp (-4*w.re+4) := by
    rw [hid,abs_neg]
    exact (Complex.abs_re_le_norm _).trans he
  have hmul := mul_le_mul_of_nonneg_right hf1 (abs_nonneg s)
  have hprod : f1 0*s ≤ (30005*Real.exp (-4*w.re+4))*|s| :=
    (le_abs_self _).trans (by rw [abs_mul]; exact hmul)
  exact htangent.trans hprod


theorem actual_weight_leading_absolute_error (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 4096 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
    (hp : 6*t*‖w‖^5+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hstat : complexSlope 3 t v= -(Complex.I*z)) (s : ℝ) (hsr : |s| < 1/16)
    (hsmall : (30005*Real.exp (-4*w.re+4))*|s| ≤ 1) :
    ‖weight 3 t z (v+(s : ℂ))-weight 3 t z v*Complex.exp (leadingPhase t z v (s : ℂ))‖ ≤
      (180030*Real.exp (-4*w.re+4))*|s| *‖weight 3 t z v‖ := by
  have hrel := actual_weight_leading_error t x ht hx w v (by linarith) hi hs hp hv z s hsr hsmall
  have hre := (leadingPhase_re_le t x ht hx w v hr hi hs hp hv z hstat s hsr).trans hsmall
  have he3 : Real.exp (1 : ℝ) ≤ 3 := Real.exp_one_lt_three.le
  have hexp : ‖Complex.exp (leadingPhase t z v (s : ℂ))‖ ≤ 3 := by
    rw [Complex.norm_exp]
    exact (Real.exp_le_exp.mpr hre).trans he3
  let B := weight 3 t z v*Complex.exp (leadingPhase t z v (s : ℂ))
  have hd := horizontal_neighbor_domain t x ht hx w v (by linarith) hi hs hp hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hd
  have hn : weight 3 t z v ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (kernel_ne_zero v hd.1 hd.2.1)
  have hB : B ≠ 0 := mul_ne_zero hn (Complex.exp_ne_zero _)
  have hBn : ‖B‖ ≤ 3*‖weight 3 t z v‖ := by
    dsimp [B]
    rw [norm_mul]
    nlinarith [mul_le_mul_of_nonneg_left hexp (norm_nonneg (weight 3 t z v))]
  have heq : weight 3 t z (v+(s : ℂ))-B=(weight 3 t z (v+(s : ℂ))/B-1)*B := by field_simp
  change ‖weight 3 t z (v+(s : ℂ))-B‖ ≤ _
  rw [heq,norm_mul]
  have h := mul_le_mul hrel hBn (norm_nonneg B) (by positivity : 0 ≤ (60010*Real.exp (-4*w.re+4))*|s|)
  nlinarith

private theorem horizontal_weight_continuousOn (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
    (hp : 6*t*‖w‖^5+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x) (z : ℂ) :
    ContinuousOn (fun a : ℝ => weight 3 t z (v+(a : ℂ)))
      (Ioo (-(1/16 : ℝ)) (1/16)) := by
  intro a ha
  have hd := horizontal_neighbor_domain t x ht hx w v hr hi hs hp hv a (abs_lt.mpr ha).le
  have hk := kernelComplex_analyticAt (v+(a : ℂ)) (by linarith [hd.2.1])
  have hw : AnalyticAt ℂ (weight 3 t z) (v+(a : ℂ)) := by
    unfold weight
    apply AnalyticAt.mul
    · fun_prop
    · exact hk
  have hc : ContinuousAt (fun b : ℝ => weight 3 t z (v+(b : ℂ))) a :=
    ContinuousAt.comp (g := weight 3 t z) (f := fun b : ℝ => v+(b : ℂ))
      hw.continuousAt (by fun_prop)
  exact hc.continuousWithinAt

theorem signed_local_leading_error (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 4096 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
    (hp : 6*t*‖w‖^5+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hstat : complexSlope 3 t v= -(Complex.I*z)) (r : ℝ) (hr0 : 0 ≤ r) (hrr : r < 1/16)
    (hsmall : (30005*Real.exp (-4*w.re+4))*r ≤ 1) :
    ‖(∫ s : ℝ in -r..r, weight 3 t z (v+(s : ℂ)))-
      weight 3 t z v*(∫ s : ℝ in -r..r, Complex.exp (leadingPhase t z v (s : ℂ)))‖ ≤
      (360060*Real.exp (-4*w.re+4))*r^2*‖weight 3 t z v‖ := by
  have hsub : uIcc (-r) r ⊆ Ioo (-(1/16 : ℝ)) (1/16) := by
    intro a ha
    rw [uIcc_of_le (by linarith : -r ≤ r)] at ha
    constructor <;> linarith [ha.1,ha.2]
  have hf : IntervalIntegrable (fun s : ℝ => weight 3 t z (v+(s : ℂ))) volume (-r) r :=
    ((horizontal_weight_continuousOn t x ht hx w v (by linarith) hi hs hp hv z).mono hsub).intervalIntegrable
  have hg : IntervalIntegrable (fun s : ℝ => weight 3 t z v*Complex.exp (leadingPhase t z v (s : ℂ))) volume (-r) r := by
    apply Continuous.intervalIntegrable
    unfold leadingPhase
    fun_prop
  rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_sub hf hg]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := -r) (b := r)
    (f := fun s : ℝ => weight 3 t z (v+(s : ℂ))-weight 3 t z v*Complex.exp (leadingPhase t z v (s : ℂ)))
    (C := (180030*Real.exp (-4*w.re+4))*r*‖weight 3 t z v‖) (fun s hsi => ?_)
  · rw [show r-(-r)=2*r by ring,abs_of_nonneg (by positivity : 0 ≤ 2*r)] at hb
    convert hb using 1 <;> ring
  · rw [uIoc_of_le (by linarith : -r ≤ r)] at hsi
    have habs : |s| ≤ r := abs_le.mpr ⟨hsi.1.le,hsi.2⟩
    have hsm : (30005*Real.exp (-4*w.re+4))*|s| ≤ 1 :=
      (mul_le_mul_of_nonneg_left habs (by positivity)).trans hsmall
    exact (actual_weight_leading_absolute_error t x ht hx w v hr hi hs hp hv z hstat s
      (habs.trans_lt hrr) hsm).trans (by gcongr)

end OperatorDerivativeRewrite.Foundation.RiemannSixthFarSignedIntegral
