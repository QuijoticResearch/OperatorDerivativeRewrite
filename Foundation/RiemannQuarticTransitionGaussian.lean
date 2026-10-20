import Foundation.RiemannQuarticTransitionCorrection
import Foundation.RiemannQuarticComplexGaussian
/-! Signed central Gaussian approximation on the actual transition saddles.
The arithmetic phase is integrated on a fixed horizontal interval; no
frequency-dominance assumption or vanishing model mismatch is imposed. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticTransitionGaussian
open RiemannQuarticSaddleTheta RiemannQuarticSaddleBranch RiemannThetaComplexKernel
open RiemannQuarticFarModelSaddle RiemannQuarticFarCorrection RiemannQuarticFarRemainder
open RiemannQuarticFarSignedIntegral RiemannQuarticFarGaussianLocal
open RiemannQuarticTransitionCorrection
open RiemannQuarticFrequencyBranch
open RiemannQuarticErrorLimits

section Scaled
variable (t K : ℝ) (c w v : ℂ)
  (ht : 1 ≤ t) (hK : 8 ≤ K) (hr : 1000 ≤ w.re) (hi : |w.im| ≤ 1/2)
  (hn : ‖w‖ ≤ 2*w.re) (hcenter : c.im ≤ 1)
  (hs : modelDerivative t w= -(Complex.I*c)) (hE : ‖Complex.exp (4*w)‖ ≤ K)
  (hv : ‖v-w‖ ≤ 1/K)
include ht hK hr hi hn hcenter hs hE hv

theorem horizontal_neighbor_domain (s : ℝ) (hsr : |s| ≤ 1/16) :
    0 ≤ (v+(s : ℂ)).re ∧ 1 ≤ (Complex.exp (4*(v+(s : ℂ)))).re ∧
      t*w.re^3/64 ≤ (Complex.exp (4*(v+(s : ℂ)))).re ∧
      |(v+(s : ℂ)).re-w.re| ≤ 1 := by
  have hK0 : 0 < K := by linarith
  have hd2 : ‖v-w‖ ≤ 2/K := hv.trans (by
    apply (div_le_div_iff_of_pos_right hK0).mpr; norm_num)
  have hd := scaled_neighbor_domain t K c w v ht hK hr hi hcenter hs hE hd2
  have hExp := horizontal_exp_real_lower v (by linarith [hd.2.1]) s hsr
  have hv8 : ‖v-w‖ ≤ 1/8 := hv.trans ((div_le_iff₀ hK0).mpr (by linarith))
  have hre := (Complex.abs_re_le_norm (v-w)).trans hv8
  simp only [Complex.sub_re] at hre
  have hcub : 32768 ≤ w.re^3 := by nlinarith [sq_nonneg (w.re-1000)]
  have htcub : w.re^3 ≤ t*w.re^3 := by nlinarith
  simp only [Complex.add_re, Complex.ofReal_re] at *
  rcases abs_le.mp hre with ⟨hr1,hr2⟩
  rcases abs_le.mp hsr with ⟨hs1,hs2⟩
  refine ⟨by linarith, by nlinarith [hd.2.2], by nlinarith [hd.2.2], ?_⟩
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem horizontal_neighbor_error (s : ℝ) (hsr : |s| ≤ 1/16) :
    ‖complexSlope t (v+(s : ℂ))-modelDerivative t (v+(s : ℂ))‖ ≤
      30005*Real.exp (-4*w.re+4) := by
  let q := v+(s : ℂ)
  have hd := horizontal_neighbor_domain t K c w v ht hK hr hi hn hcenter hs hE hv s hsr
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
    nlinarith [mul_le_mul_of_nonneg_right hsq (by linarith : 0 ≤ w.re)]
  have htcub : w.re^3 ≤ t*w.re^3 := by nlinarith [pow_nonneg (by linarith : 0 ≤ w.re) 3]
  have hpi := mul_le_mul_of_nonneg_right Real.pi_gt_three.le
    (by linarith [hd.2.1] : 0 ≤ (Complex.exp (4*q)).re)
  have hlo := (abs_le.mp hd.2.2.2).1
  have hhi := (abs_le.mp hd.2.2.2).2
  have h1 : Real.exp (-4*q.re) ≤ Real.exp (-4*w.re+4) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (4*q.re)*Real.exp (-3*Real.pi*(Complex.exp (4*q)).re) ≤ Real.exp (-4*w.re+4) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hd.2.2.1]
  nlinarith [mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 5),
    mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 30000)]

theorem horizontal_slope_continuousOn (z : ℂ) :
    ContinuousOn (fun a : ℝ => complexSlope t (v+(a : ℂ))+Complex.I*z)
      (Ioo (-(1/16 : ℝ)) (1/16)) := by
  intro a ha
  have hd := horizontal_neighbor_domain t K c w v ht hK hr hi hn hcenter hs hE hv a (abs_lt.mpr ha).le
  have hka := kernelComplex_analyticAt (v+(a : ℂ)) (by linarith [hd.2.1])
  have hkn := kernel_ne_zero (v+(a : ℂ)) hd.1 hd.2.1
  have hsa : AnalyticAt ℂ (complexSlope t) (v+(a : ℂ)) :=
    (analyticAt_const.mul (analyticAt_id.pow 3)).add (hka.deriv.div hka hkn)
  have hc : ContinuousAt (fun b : ℝ => complexSlope t (v+(b : ℂ))) a :=
    ContinuousAt.comp (g := complexSlope t) (f := fun b : ℝ => v+(b : ℂ))
      hsa.continuousAt (by fun_prop)
  exact (hc.add continuousAt_const).continuousWithinAt

theorem horizontal_weight_hasDerivAt (z : ℂ) (s : ℝ) (hsr : |s| ≤ 1/16) :
    HasDerivAt (fun a : ℝ => saddleWeight t z (v+(a : ℂ)))
      ((complexSlope t (v+(s : ℂ))+Complex.I*z)*saddleWeight t z (v+(s : ℂ))) s := by
  have hd := horizontal_neighbor_domain t K c w v ht hK hr hi hn hcenter hs hE hv s hsr
  have hkn := kernel_ne_zero (v+(s : ℂ)) hd.1 hd.2.1
  have h := (RiemannQuarticSpatialPhase.spatial_weight_hasDerivAt t z (v+(s : ℂ))
    (by linarith [hd.2.1]) hkn).comp (s : ℂ) ((hasDerivAt_id (s : ℂ)).const_add v)
  have he : HasDerivAt (fun a : ℂ => saddleWeight t z (v+a))
      ((complexSlope t (v+(s : ℂ))+Complex.I*z)*saddleWeight t z (v+(s : ℂ))) (s : ℂ) := by
    convert h using 1 <;> first | rfl | simp only [mul_one]
  exact he.comp_ofReal

theorem actual_horizontal_phase (z : ℂ) (s : ℝ) (hsr : |s| < 1/16) :
    saddleWeight t z (v+(s : ℂ))=saddleWeight t z v*
      Complex.exp (∫ a : ℝ in 0..s, complexSlope t (v+(a : ℂ))+Complex.I*z) := by
  simpa only [Complex.ofReal_zero, add_zero] using normalized_real_ode
    (fun a : ℝ => saddleWeight t z (v+(a : ℂ)))
    (fun a : ℝ => complexSlope t (v+(a : ℂ))+Complex.I*z)
    (1/16) (by norm_num)
    (horizontal_slope_continuousOn t K c w v ht hK hr hi hn hcenter hs hE hv z)
    (fun a ha => horizontal_weight_hasDerivAt t K c w v ht hK hr hi hn hcenter hs hE hv z a
      (abs_lt.mpr ha).le) s (abs_lt.mp hsr)

theorem actual_phase_model_error (z : ℂ) (s : ℝ) (hsr : |s| < 1/16) :
    ‖(∫ a : ℝ in 0..s, complexSlope t (v+(a : ℂ))+Complex.I*z)-leadingPhase t z v (s : ℂ)‖ ≤
      (30005*Real.exp (-4*w.re+4))*|s| := by
  have hH := horizontal_slope_continuousOn t K c w v ht hK hr hi hn hcenter hs hE hv z
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
  rw [← leadingPhase_integral t z v s, ← intervalIntegral.integral_sub hA hM]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := s)
    (f := fun a : ℝ => (complexSlope t (v+(a : ℂ))+Complex.I*z)-
      (modelDerivative t (v+(a : ℂ))+Complex.I*z))
    (C := 30005*Real.exp (-4*w.re+4)) (fun a ha => ?_)
  · simpa only [sub_zero] using h
  · have had := hsub (uIoc_subset_uIcc ha)
    have he := horizontal_neighbor_error t K c w v ht hK hr hi hn hcenter hs hE hv a (abs_lt.mpr had).le
    convert he using 1 <;> congr 1 <;> ring

theorem corrected_exp_norm : ‖Complex.exp (4*v)‖ ≤ 2*K := by
  have hK0 : 0 < K := by linarith
  have hsmall : 4*‖v-w‖ ≤ 1 := by
    have hh : 1/K ≤ 1/4 := (div_le_iff₀ hK0).mpr (by linarith)
    linarith
  have he := exp4_difference_bound w v hsmall
  have hm := mul_le_mul hE hv (norm_nonneg _) hK0.le
  have hc : K*(1/K)=1 := by field_simp
  rw [hc] at hm
  have he8 : ‖Complex.exp (4*v)-Complex.exp (4*w)‖ ≤ 8 := by nlinarith
  have hh := norm_add_le (Complex.exp (4*v)-Complex.exp (4*w)) (Complex.exp (4*w))
  rw [sub_add_cancel] at hh
  linarith

theorem corrected_polynomial_scale : t*(4*‖v‖+1) ≤ K := by
  have ht0 : 0 ≤ t := by linarith
  have ha0 : 0 ≤ w.re := by linarith
  have hd : ‖v-w‖ ≤ 1 := hv.trans ((div_le_iff₀ (by linarith : 0 < K)).mpr (by linarith))
  have hnorm : ‖v‖ ≤ 3*w.re := by
    have h := norm_add_le (v-w) w
    rw [sub_add_cancel] at h
    linarith
  have hm := RiemannQuarticComplexModelSaddle.real_margin t c w ht0 (by linarith) hi hs
  have hQ0 : 0 ≤ t*w.re^3 := by positivity
  have hR0 : 0 ≤ (Complex.exp (4*w)).re := by nlinarith [Real.pi_pos]
  have hpi := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hR0
  have hnormexp := (Complex.re_le_norm (Complex.exp (4*w))).trans hE
  have hQ : t*w.re^3 ≤ 16*K := by nlinarith
  have hsq : 1000000 ≤ w.re^2 := by nlinarith
  have hcube := mul_le_mul_of_nonneg_right hsq ha0
  have hpoly : 16*(12*w.re+1) ≤ w.re^3 := by nlinarith
  have hp := mul_le_mul_of_nonneg_left hpoly ht0
  have hnT := mul_le_mul_of_nonneg_left hnorm ht0
  nlinarith

theorem model_real_curvature : (deriv (modelDerivative t) v).re ≤ -3*t*w.re^3 := by
  have hb := scaled_model_deriv_bound t K w v ht hK hr hn hE hv
  let A : ℂ := -(16 : ℂ)*(Real.pi : ℂ)*Complex.exp (4*w)
  have he : A.re= -16*Real.pi*(Complex.exp (4*w)).re := by simp [A, Complex.mul_re]
  have hre := Complex.re_le_norm (deriv (modelDerivative t) v-A)
  rw [Complex.sub_re, he] at hre
  have hm := RiemannQuarticComplexModelSaddle.real_margin t c w (by linarith) (by linarith) hi hs
  nlinarith

theorem quadratic_norm_le_one (s : ℝ) :
    ‖Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)‖ ≤ 1 := by
  have hc := model_real_curvature t K c w v ht hK hr hi hn hcenter hs hE hv
  have hq : 0 ≤ t*w.re^3 := by positivity
  have hb : 0 ≤ (-(deriv (modelDerivative t) v)/2).re := by
    simp only [Complex.div_ofNat_re, Complex.neg_re]
    linarith
  have h := GaussianOscillatoryTail.gaussian_norm_le_one (-(deriv (modelDerivative t) v)/2) hb s
  convert h using 1 <;> congr 1 <;> ring

theorem leadingPhase_cubic_bound (z u : ℂ) (hu : ‖u‖ ≤ 1/16) :
    ‖leadingPhase t z v u-(modelDerivative t v+Complex.I*z)*u-
      deriv (modelDerivative t) v*u^2/2‖ ≤ 2048*K*‖u‖^3 := by
  have ht0 : 0 ≤ t := by linarith
  have he := exponential_cubic_remainder u hu
  have heE := corrected_exp_norm t K c w v ht hK hr hi hn hcenter hs hE hv
  have hP := corrected_polynomial_scale t K c w v ht hK hr hi hn hcenter hs hE hv
  have hunit : ‖u‖ ≤ 1 := by linarith
  have heq : Complex.exp (4*(v+u))=Complex.exp (4*v)*Complex.exp (4*u) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hid : leadingPhase t z v u-(modelDerivative t v+Complex.I*z)*u-
      deriv (modelDerivative t) v*u^2/2=
      (t : ℂ)*(4*v+u)*u^3-(Real.pi : ℂ)*Complex.exp (4*v)*(Complex.exp (4*u)-1-4*u-8*u^2) := by
    rw [leadingPhase, (modelDerivative_hasDerivAt t v).deriv, heq]
    unfold modelDerivative
    ring
  rw [hid]
  have htri := norm_sub_le ((t : ℂ)*(4*v+u)*u^3)
    ((Real.pi : ℂ)*Complex.exp (4*v)*(Complex.exp (4*u)-1-4*u-8*u^2))
  have hadd := norm_add_le (4*v) u
  simp only [norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ht0, abs_of_pos Real.pi_pos] at htri hadd
  have hpoly : t*‖4*v+u‖ ≤ K := by
    have hm := mul_le_mul_of_nonneg_left (by linarith : ‖4*v+u‖ ≤ 4*‖v‖+1) ht0
    linarith
  have hp3 := mul_le_mul_of_nonneg_right hpoly (pow_nonneg (norm_nonneg u) 3)
  have hpe := mul_le_mul Real.pi_lt_four.le heE (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
  have hrem := mul_le_mul hpe he (norm_nonneg _) (by positivity : 0 ≤ 4*(2*K))
  nlinarith [pow_nonneg (norm_nonneg u) 3]

theorem leadingPhase_quadratic_bound (z : ℂ) (hstat : complexSlope t v= -(Complex.I*z))
    (s : ℝ) (hsr : |s| ≤ 1/16) :
    ‖leadingPhase t z v (s : ℂ)-deriv (modelDerivative t) v*(s : ℂ)^2/2‖ ≤
      (30005*Real.exp (-4*w.re+4))*|s|+2048*K*|s|^3 := by
  have hc := leadingPhase_cubic_bound t K c w v ht hK hr hi hn hcenter hs hE hv z (s : ℂ) (by simpa using hsr)
  simp only [Complex.norm_real, Real.norm_eq_abs] at hc
  have he := horizontal_neighbor_error t K c w v ht hK hr hi hn hcenter hs hE hv 0 (by norm_num)
  simp only [Complex.ofReal_zero, add_zero] at he
  have hid : modelDerivative t v+Complex.I*z= -(complexSlope t v-modelDerivative t v) := by rw [hstat]; ring
  have hlin : ‖(modelDerivative t v+Complex.I*z)*(s : ℂ)‖ ≤ (30005*Real.exp (-4*w.re+4))*|s| := by
    rw [norm_mul, hid, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right he (abs_nonneg s)
  have htri := norm_add_le
    (leadingPhase t z v (s : ℂ)-(modelDerivative t v+Complex.I*z)*(s : ℂ)-deriv (modelDerivative t) v*(s : ℂ)^2/2)
    ((modelDerivative t v+Complex.I*z)*(s : ℂ))
  have halg : leadingPhase t z v (s : ℂ)-(modelDerivative t v+Complex.I*z)*(s : ℂ)-deriv (modelDerivative t) v*(s : ℂ)^2/2+
      (modelDerivative t v+Complex.I*z)*(s : ℂ)=leadingPhase t z v (s : ℂ)-deriv (modelDerivative t) v*(s : ℂ)^2/2 := by ring
  rw [halg] at htri
  linarith

theorem actual_phase_quadratic_bound (z : ℂ) (hstat : complexSlope t v= -(Complex.I*z))
    (s : ℝ) (hsr : |s| < 1/16) :
    ‖(∫ a : ℝ in 0..s, complexSlope t (v+(a : ℂ))+Complex.I*z)-
      deriv (modelDerivative t) v*(s : ℂ)^2/2‖ ≤
      2*(30005*Real.exp (-4*w.re+4))*|s|+2048*K*|s|^3 := by
  have h1 := actual_phase_model_error t K c w v ht hK hr hi hn hcenter hs hE hv z s hsr
  have h2 := leadingPhase_quadratic_bound t K c w v ht hK hr hi hn hcenter hs hE hv z hstat s hsr.le
  have h3 := norm_add_le
    ((∫ a : ℝ in 0..s, complexSlope t (v+(a : ℂ))+Complex.I*z)-leadingPhase t z v (s : ℂ))
    (leadingPhase t z v (s : ℂ)-deriv (modelDerivative t) v*(s : ℂ)^2/2)
  rw [sub_add_sub_cancel] at h3
  linarith

theorem actual_quadratic_weight_error (z : ℂ) (hstat : complexSlope t v= -(Complex.I*z))
    (s : ℝ) (hsr : |s| < 1/16)
    (hsmall : 2*(30005*Real.exp (-4*w.re+4))*|s|+2048*K*|s|^3 ≤ 1) :
    ‖saddleWeight t z (v+(s : ℂ))-saddleWeight t z v*
      Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)‖ ≤
      2*(2*(30005*Real.exp (-4*w.re+4))*|s|+2048*K*|s|^3)*‖saddleWeight t z v‖ := by
  let P := ∫ a : ℝ in 0..s, complexSlope t (v+(a : ℂ))+Complex.I*z
  let Q := deriv (modelDerivative t) v*(s : ℂ)^2/2
  have hp := actual_phase_quadratic_bound t K c w v ht hK hr hi hn hcenter hs hE hv z hstat s hsr
  have he := Complex.norm_exp_sub_one_le (hp.trans hsmall)
  have hQ := quadratic_norm_le_one t K c w v ht hK hr hi hn hcenter hs hE hv s
  have hid : Complex.exp P-Complex.exp Q=Complex.exp Q*(Complex.exp (P-Q)-1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    ring
  have hb : ‖Complex.exp P-Complex.exp Q‖ ≤
      2*(2*(30005*Real.exp (-4*w.re+4))*|s|+2048*K*|s|^3) := by
    rw [hid, norm_mul]
    change ‖Complex.exp Q‖ ≤ 1 at hQ
    change ‖Complex.exp (P-Q)-1‖ ≤ 2*‖P-Q‖ at he
    have hm := mul_le_mul_of_nonneg_right hQ (norm_nonneg (Complex.exp (P-Q)-1))
    change ‖P-Q‖ ≤ _ at hp
    nlinarith
  rw [actual_horizontal_phase t K c w v ht hK hr hi hn hcenter hs hE hv z s hsr]
  change ‖saddleWeight t z v*Complex.exp P-saddleWeight t z v*Complex.exp Q‖ ≤ _
  rw [← mul_sub, norm_mul]
  nlinarith [mul_le_mul_of_nonneg_left hb (norm_nonneg (saddleWeight t z v))]

theorem actual_local_quadratic_error (z : ℂ) (hstat : complexSlope t v= -(Complex.I*z))
    (r : ℝ) (hr0 : 0 ≤ r) (hrr : r < 1/16)
    (hsmall : 2*(30005*Real.exp (-4*w.re+4))*r+2048*K*r^3 ≤ 1) :
    ‖(∫ s : ℝ in -r..r, saddleWeight t z (v+(s : ℂ)))-
      saddleWeight t z v*(∫ s : ℝ in -r..r, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2))‖ ≤
      (8*(30005*Real.exp (-4*w.re+4))*r^2+8192*K*r^4)*‖saddleWeight t z v‖ := by
  have hf : IntervalIntegrable (fun s : ℝ => saddleWeight t z (v+(s : ℂ))) volume (-r) r := by
    apply ContinuousOn.intervalIntegrable
    intro s hsi
    have hsi' : -r ≤ s ∧ s ≤ r := by simpa only [uIcc_of_le (by linarith : -r ≤ r), mem_Icc] using hsi
    exact (horizontal_weight_hasDerivAt t K c w v ht hK hr hi hn hcenter hs hE hv z s
      ((abs_le.mpr ⟨hsi'.1,hsi'.2⟩).trans hrr.le)).continuousAt.continuousWithinAt
  have hg : IntervalIntegrable (fun s : ℝ => saddleWeight t z v*
      Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)) volume (-r) r :=
    (by fun_prop : Continuous (fun s : ℝ => saddleWeight t z v*
      Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2))).intervalIntegrable _ _
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hf hg]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := -r) (b := r)
    (f := fun s : ℝ => saddleWeight t z (v+(s : ℂ))-saddleWeight t z v*
      Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2))
    (C := 2*(2*(30005*Real.exp (-4*w.re+4))*r+2048*K*r^3)*‖saddleWeight t z v‖) (fun s hsi => ?_)
  · rw [show r-(-r)=2*r by ring, abs_of_nonneg (by positivity : 0 ≤ 2*r)] at hb
    convert hb using 1 <;> ring
  · rw [uIoc_of_le (by linarith : -r ≤ r)] at hsi
    have habs : |s| ≤ r := abs_le.mpr ⟨hsi.1.le,hsi.2⟩
    have hpow := pow_le_pow_left₀ (abs_nonneg s) habs 3
    have h1 := mul_le_mul_of_nonneg_left habs (by positivity : 0 ≤ 2*(30005*Real.exp (-4*w.re+4)))
    have h2 := mul_le_mul_of_nonneg_left hpow (by linarith : 0 ≤ 2048*K)
    have hsm : 2*(30005*Real.exp (-4*w.re+4))*|s|+2048*K*|s|^3 ≤ 1 := by linarith
    have he := actual_quadratic_weight_error t K c w v ht hK hr hi hn hcenter hs hE hv z hstat s
      (habs.trans_lt hrr) hsm
    have hm := mul_le_mul_of_nonneg_right (show
        2*(2*(30005*Real.exp (-4*w.re+4))*|s|+2048*K*|s|^3) ≤
        2*(2*(30005*Real.exp (-4*w.re+4))*r+2048*K*r^3) by linarith)
      (norm_nonneg (saddleWeight t z v))
    exact he.trans hm

theorem model_gaussian_coefficient_pos : 0 < (-(deriv (modelDerivative t) v)/2).re := by
  have h := model_real_curvature t K c w v ht hK hr hi hn hcenter hs hE hv
  have hQ : 0 < t*w.re^3 := by positivity
  simp only [Complex.div_ofNat_re, Complex.neg_re]
  linarith

theorem actual_local_full_gaussian_error (z : ℂ) (hstat : complexSlope t v= -(Complex.I*z))
    (r : ℝ) (hr0 : 0 < r) (hrr : r < 1/16)
    (hsmall : 2*(30005*Real.exp (-4*w.re+4))*r+2048*K*r^3 ≤ 1) :
    ‖(∫ s : ℝ in -r..r, saddleWeight t z (v+(s : ℂ)))-
      saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2))‖ ≤
      ‖saddleWeight t z v‖*(8*(30005*Real.exp (-4*w.re+4))*r^2+8192*K*r^4+
        2/(‖-(deriv (modelDerivative t) v)/2‖*r)) := by
  let b := -(deriv (modelDerivative t) v)/2
  have hb : 0 < b.re := model_gaussian_coefficient_pos t K c w v ht hK hr hi hn hcenter hs hE hv
  have htail := GaussianOscillatoryTail.full_minus_truncated_bound b hb r hr0
  have hfun : (fun s : ℝ => Complex.exp (-b*(s : ℂ)^2))=
      (fun s : ℝ => Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)) := by
    funext s
    congr 1
    dsimp [b]
    ring
  rw [hfun] at htail
  have hl := actual_local_quadratic_error t K c w v ht hK hr hi hn hcenter hs hE hv z hstat r hr0.le hrr hsmall
  let W := saddleWeight t z v
  let L := ∫ s : ℝ in -r..r, saddleWeight t z (v+(s : ℂ))
  let G0 := ∫ s : ℝ in -r..r, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)
  let G := ∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)
  have he : L-W*G=(L-W*G0)+W*(G0-G) := by ring
  change ‖L-W*G‖ ≤ _
  rw [he]
  have htri := norm_add_le (L-W*G0) (W*(G0-G))
  rw [norm_mul, norm_sub_rev G0 G] at htri
  have hm := mul_le_mul_of_nonneg_left htail (norm_nonneg W)
  change ‖L-W*G0‖ ≤ _ at hl
  change ‖W‖*‖G-G0‖ ≤ _ at hm
  nlinarith

theorem gaussian_coefficient_norm_bounds :
    t*w.re^3 ≤ ‖-(deriv (modelDerivative t) v)/2‖ ∧
      ‖-(deriv (modelDerivative t) v)/2‖ ≤ 64*K := by
  have hreal := model_real_curvature t K c w v ht hK hr hi hn hcenter hs hE hv
  have hQ0 : 0 ≤ t*w.re^3 := by positivity
  have hm := RiemannQuarticComplexModelSaddle.real_margin t c w (by linarith) (by linarith) hi hs
  have hR0 : 0 ≤ (Complex.exp (4*w)).re := by nlinarith [Real.pi_pos]
  have hpi := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hR0
  have hnormexp := (Complex.re_le_norm (Complex.exp (4*w))).trans hE
  have hQ : t*w.re^3 ≤ 16*K := by nlinarith
  have hb := scaled_model_deriv_bound t K w v ht hK hr hn hE hv
  have hnA : ‖-(16 : ℂ)*(Real.pi : ℂ)*Complex.exp (4*w)‖ ≤ 64*K := by
    simp only [norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hmul := mul_le_mul Real.pi_lt_four.le hE (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
    nlinarith
  have htri := norm_add_le (deriv (modelDerivative t) v-(-(16 : ℂ)*(Real.pi : ℂ)*Complex.exp (4*w)))
    (-(16 : ℂ)*(Real.pi : ℂ)*Complex.exp (4*w))
  rw [sub_add_cancel] at htri
  have hre := Complex.re_le_norm (-(deriv (modelDerivative t) v)/2)
  simp only [Complex.div_ofNat_re, Complex.neg_re] at hre
  rw [norm_div, norm_neg, Complex.norm_ofNat] at hre
  rw [norm_div, norm_neg, Complex.norm_ofNat]
  constructor <;> nlinarith

theorem gaussian_normalization_lower :
    1 ≤ 8*Real.sqrt K*‖∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)‖ := by
  let b := -(deriv (modelDerivative t) v)/2
  have hb : 0 < b.re := model_gaussian_coefficient_pos t K c w v ht hK hr hi hn hcenter hs hE hv
  have hn := (gaussian_coefficient_norm_bounds t K c w v ht hK hr hi hn hcenter hs hE hv).2
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
  simp only [norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos] at hnorm
  let g := ‖∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)‖
  have hid : g^2*‖b‖=Real.pi := (eq_div_iff hbn.ne').mp hnorm
  have hm := mul_le_mul_of_nonneg_left hn (sq_nonneg g)
  have hroot := Real.sq_sqrt (show 0 ≤ K by linarith)
  have hprod : 0 ≤ 8*Real.sqrt K*g := by positivity
  have hsquare : 1 ≤ (8*Real.sqrt K*g)^2 := by
    calc
      _ ≤ Real.pi := by linarith [Real.pi_gt_three]
      _ ≤ g^2*(64*K) := by nlinarith
      _ = _ := by rw [mul_pow, mul_pow, hroot]; ring
  change 1 ≤ 8*Real.sqrt K*g
  nlinarith

theorem relative_local_error_bound (z : ℂ) (hstat : complexSlope t v= -(Complex.I*z))
    (r : ℝ) (hr0 : 0 < r) (hrr : r < 1/16)
    (hsmall : 2*(30005*Real.exp (-4*w.re+4))*r+2048*K*r^3 ≤ 1) :
    ‖(∫ s : ℝ in -r..r, saddleWeight t z (v+(s : ℂ)))/
      (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))-1‖ ≤
      8*Real.sqrt K*(8*(30005*Real.exp (-4*w.re+4))*r^2+8192*K*r^4+2/(t*w.re^3*r)) := by
  have hQ : 0 < t*w.re^3 := by positivity
  have he := actual_local_full_gaussian_error t K c w v ht hK hr hi hn hcenter hs hE hv z hstat r hr0 hrr hsmall
  have hnormb := (gaussian_coefficient_norm_bounds t K c w v ht hK hr hi hn hcenter hs hE hv).1
  have htail : 2/(‖-(deriv (modelDerivative t) v)/2‖*r) ≤ 2/(t*w.re^3*r) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos hQ hr0)
      (mul_le_mul_of_nonneg_right hnormb hr0.le)
  let W := saddleWeight t z v
  let G := ∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)
  let L := ∫ s : ℝ in -r..r, saddleWeight t z (v+(s : ℂ))
  let B := 8*(30005*Real.exp (-4*w.re+4))*r^2+8192*K*r^4+2/(t*w.re^3*r)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hnum : ‖L-W*G‖ ≤ ‖W‖*B := by
    apply he.trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg W)
    dsimp [B]
    linarith
  have hnormal := gaussian_normalization_lower t K c w v ht hK hr hi hn hcenter hs hE hv
  change 1 ≤ 8*Real.sqrt K*‖G‖ at hnormal
  have hG : G ≠ 0 := by intro h; norm_num [h] at hnormal
  have hd := horizontal_neighbor_domain t K c w v ht hK hr hi hn hcenter hs hE hv 0 (by norm_num)
  simp only [Complex.ofReal_zero, add_zero] at hd
  have hW : W ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (kernel_ne_zero v hd.1 hd.2.1)
  have hden : W*G ≠ 0 := mul_ne_zero hW hG
  have hfrac : L/(W*G)-1=(L-W*G)/(W*G) := by field_simp
  change ‖L/(W*G)-1‖ ≤ _
  rw [hfrac, norm_div, norm_mul]
  apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hW) (norm_pos_iff.mpr hG))).mpr
  have hm := mul_le_mul_of_nonneg_left hnormal (mul_nonneg (norm_nonneg W) hB)
  change ‖L-W*G‖ ≤ (8*Real.sqrt K*B)*(‖W‖*‖G‖)
  nlinarith

end Scaled

theorem scaled_radius_square_tendsto_zero :
    Tendsto (fun Q : ℝ => Real.sqrt Q*centralRadius Q^2) atTop (nhds 0) := by
  have h := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3/8)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Q hQ
  rw [Real.sqrt_eq_rpow, centralRadius_pow Q hQ 2]
  rw [← Real.rpow_add hQ]
  norm_num

theorem scaled_gaussian_prefactor_tendsto_zero :
    Tendsto (fun Q : ℝ => Real.sqrt Q/(Q*centralRadius Q)) atTop (nhds 0) := by
  apply (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/16)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Q hQ
  simpa only [neg_div] using (gaussian_scaled_prefactor Q hQ).symm

theorem central_budget_tendsto_zero (C : ℝ) :
    Tendsto (fun Q : ℝ => 8*Real.sqrt C*Real.sqrt Q*
      (240040*centralRadius Q^2+8192*C*Q*centralRadius Q^4+2/(Q*centralRadius Q))) atTop (nhds 0) := by
  have h := (((scaled_radius_square_tendsto_zero.const_mul 240040).add
    (central_relative_tendsto_zero.const_mul (8192*C))).add
    (scaled_gaussian_prefactor_tendsto_zero.const_mul 2)).const_mul (8*Real.sqrt C)
  convert h using 1
  · ext Q
    ring
  · ring

theorem eventually_uniform_relative_central_error (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ Q : ℝ in atTop, ∀ (t K : ℝ) (c w v z : ℂ),
      1 ≤ t → 8 ≤ K → 1000 ≤ w.re → |w.im| ≤ 1/2 → ‖w‖ ≤ 2*w.re → c.im ≤ 1 →
      modelDerivative t w= -(Complex.I*c) → ‖Complex.exp (4*w)‖ ≤ K → ‖v-w‖ ≤ 1/K →
      complexSlope t v= -(Complex.I*z) → Q=t*w.re^3 → K ≤ C*Q →
      ‖(∫ s : ℝ in -(centralRadius Q)..centralRadius Q, saddleWeight t z (v+(s : ℂ)))/
        (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))-1‖ < ε := by
  have hsmall : Tendsto (fun Q : ℝ => 60010*centralRadius Q+2048*C*Q*centralRadius Q^3) atTop (nhds 0) := by
    have hp : Tendsto (fun Q : ℝ => Q*centralRadius Q^3) atTop (nhds 0) := by
      apply (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 5/16)).congr'
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with Q hQ
      simpa only [neg_div] using (central_small_error Q hQ).symm
    convert (centralRadius_tendsto_zero.const_mul 60010).add (hp.const_mul (2048*C)) using 1 <;>
      first | (ext Q; ring) | ring
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    centralRadius_tendsto_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/16)),
    hsmall.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    (central_budget_tendsto_zero C).eventually (gt_mem_nhds hε)] with Q hQ hrCap hsm hbudget
  intro t K c w v z ht hK hr hi hn hcenter hs hE hv hstat hQid hratio
  have hr0 : 0 < centralRadius Q := Real.rpow_pos_of_pos hQ _
  have heps : 30005*Real.exp (-4*w.re+4) ≤ 30005 := by
    have he : Real.exp (-4*w.re+4) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have hsmall' : 2*(30005*Real.exp (-4*w.re+4))*centralRadius Q+2048*K*centralRadius Q^3 ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_right heps hr0.le
    have h2 := mul_le_mul_of_nonneg_right hratio (pow_nonneg hr0.le 3)
    nlinarith
  have h := relative_local_error_bound t K c w v ht hK hr hi hn hcenter hs hE hv z hstat
    (centralRadius Q) hr0 hrCap hsmall'
  rw [← hQid] at h
  have hroot : Real.sqrt K ≤ Real.sqrt C*Real.sqrt Q := by
    rw [← Real.sqrt_mul hC.le]
    exact Real.sqrt_le_sqrt hratio
  have h1 := mul_le_mul_of_nonneg_right heps (sq_nonneg (centralRadius Q))
  have h2 := mul_le_mul_of_nonneg_right hratio (pow_nonneg hr0.le 4)
  have hB : 0 ≤ 8*(30005*Real.exp (-4*w.re+4))*centralRadius Q^2+
      8192*K*centralRadius Q^4+2/(Q*centralRadius Q) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hroot hB
  have hweight := mul_le_mul_of_nonneg_left (show
      8*(30005*Real.exp (-4*w.re+4))*centralRadius Q^2+8192*K*centralRadius Q^4+2/(Q*centralRadius Q) ≤
      240040*centralRadius Q^2+8192*C*Q*centralRadius Q^4+2/(Q*centralRadius Q) by nlinarith)
    (show 0 ≤ Real.sqrt C*Real.sqrt Q by positivity)
  nlinarith

theorem moving_scale_ratio_bound (t u M : ℝ) (w : ℂ)
    (ht : 1 ≤ t) (hM : 0 ≤ M) (hu : 65536*(M+7) ≤ u)
    (hs : RiemannQuarticSaddleTimes.phaseSlope t u=0) (hw : ‖w-(u : ℂ)‖ ≤ M+7) :
    (M+8)*RiemannQuarticTransitionSaddle.realScale u ≤ 128*(M+8)*(t*w.re^3) := by
  have hu1 : 1 ≤ u := by linarith
  have hc := (Complex.abs_re_le_norm (w-(u : ℂ))).trans hw
  simp only [Complex.sub_re, Complex.ofReal_re] at hc
  have haU := (abs_le.mp hc).1
  have huA : u ≤ 2*w.re := by linarith
  have hB : RiemannQuarticTransitionSaddle.realScale u ≤ 4*t*u^3+12 := by
    have hh := (RiemannQuarticCurvature.stationary_scale_bounds t u hu1 hs).1
    unfold RiemannQuarticTransitionSaddle.realScale
    linarith
  have htu : 1 ≤ t*u^3 := by
    have hh : 1 ≤ u^3 := one_le_pow₀ hu1
    nlinarith
  have hcube := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith : 0 ≤ u) huA 3)
    (show 0 ≤ t by linarith)
  have hcomp : RiemannQuarticTransitionSaddle.realScale u ≤ 128*(t*w.re^3) := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hcomp (show 0 ≤ M+8 by linarith)
  nlinarith

theorem eventually_actual_relative_central_error (M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∃ u : ℝ, 65536*(M+7) ≤ u ∧ RiemannQuarticSaddleTimes.phaseSlope t u=0 ∧
      ∀ z : ℂ, z.im ≤ 1 → ‖z‖ ≤ M*RiemannQuarticTransitionSaddle.realScale u →
        ∃ w v : ℂ, w ∈ closedBall (RiemannQuarticTransitionSaddle.movingAnchor u z) (1/1024) ∧
          modelDerivative t w= -(Complex.I*z) ∧
          ‖v-w‖ ≤ 1/((M+8)*RiemannQuarticTransitionSaddle.realScale u) ∧
          complexSlope t v= -(Complex.I*z) ∧
          ‖(∫ s : ℝ in -(centralRadius (t*w.re^3))..centralRadius (t*w.re^3), saddleWeight t z (v+(s : ℂ)))/
            (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))-1‖ < ε := by
  let C := 128*(M+8)
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨U,hU⟩ := eventually_atTop.1 (eventually_uniform_relative_central_error C ε hC hε)
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
  have hQ : U ≤ t*w.re^3 := by
    have hp : 1 ≤ w.re^3 := one_le_pow₀ (by linarith [hd.2.1] : 1 ≤ w.re)
    have hh := mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ t)
    linarith [(le_max_left U 1).trans htU]
  have he := hU (t*w.re^3) hQ t K z w v z ht hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1
    hy hw.2 hd.2.2.2.2.1 hvdist hv.2 rfl hratio
  exact ⟨w,v,hw.1,hw.2,hvdist,hv.2,he⟩

end OperatorDerivativeRewrite.Foundation.RiemannQuarticTransitionGaussian
