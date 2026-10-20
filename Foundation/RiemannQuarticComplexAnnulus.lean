import Foundation.RiemannQuarticComplexGaussian
import Foundation.RiemannQuarticFarGaussianFixed
/-! Signed annular cancellation and fixed horizontal neighborhoods at actual
complex-frequency quartic saddles. Generic integration by parts and Gaussian
normalization are reused. Farther contour tails and global zeros remain open. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticComplexAnnulus
open RiemannQuarticSaddleTheta RiemannQuarticSaddleBranch RiemannQuarticFarModelSaddle
open RiemannQuarticFrequencyBranch RiemannThetaComplexKernel
open RiemannQuarticFarSignedIntegral RiemannQuarticFarAnnulus
open RiemannQuarticComplexGaussian RiemannQuarticErrorLimits

theorem model_slope_quadratic_remainder (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c‖)
    (w v : ℂ) (hr : 64 ≤ w.re)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖) (u : ℂ) (hu : ‖u‖ ≤ 1/16) :
    ‖modelDerivative t (v+u)-modelDerivative t v-deriv (modelDerivative t) v*u‖ ≤
      2048*‖c‖*‖u‖^2 := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 ≤ ‖c‖ := by linarith
  have he := exponential_quadratic_remainder u hu
  have hE := corrected_exp_norm t c hcenter ht0 hx w v hs hp hv
  have hP := corrected_polynomial_scale t c hcenter ht hx w v hr hp hv
  have hid : modelDerivative t (v+u)-modelDerivative t v-deriv (modelDerivative t) v*u=
      (t : ℂ)*(12*v+4*u)*u^2-4*(Real.pi : ℂ)*Complex.exp (4*v)*(Complex.exp (4*u)-1-4*u) := by
    rw [(modelDerivative_hasDerivAt t v).deriv]
    unfold modelDerivative
    rw [show 4*(v+u)=4*v+4*u by ring,Complex.exp_add]
    ring
  rw [hid]
  have htri := norm_sub_le ((t : ℂ)*(12*v+4*u)*u^2)
    (4*(Real.pi : ℂ)*Complex.exp (4*v)*(Complex.exp (4*u)-1-4*u))
  have hadd := norm_add_le (12*v) (4*u)
  simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ht0,abs_of_pos Real.pi_pos] at htri hadd
  have hpoly : t*‖12*v+4*u‖ ≤ 4*‖c‖ := by
    have hm := mul_le_mul_of_nonneg_left hadd ht0
    nlinarith
  have hpoly2 := mul_le_mul_of_nonneg_right hpoly (sq_nonneg ‖u‖)
  have hpe := mul_le_mul Real.pi_lt_four.le hE (norm_nonneg _) (by norm_num : (0 : ℝ)≤4)
  have hrem := mul_le_mul hpe he (norm_nonneg _) (by positivity : 0 ≤ 4*(2*‖c‖))
  nlinarith [sq_nonneg ‖u‖]



theorem annulus_slope_lower (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 10000 ≤ ‖c‖)
    (w v : ℂ) (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖)
    (z : ℂ) (hz : complexSlope t v= -(Complex.I*z))
    (s : ℝ) (hsr : |s| ≤ 1/8192)
    (heps : 30005*Real.exp (-4*w.re+4) ≤ ‖c‖*|s|/2) :
    ‖c‖*|s| ≤ ‖modelDerivative t (v+(s : ℂ))+Complex.I*z‖ := by
  have ht0 : 0 ≤ t := by linarith
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hmul := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 4*t*‖w‖^3+9 ≤ ‖c‖ := by nlinarith [pow_nonneg (norm_nonneg w) 3]
  have hn := (gaussian_coefficient_norm_bounds t c hcenter ht hx w v hp hs hv).1
  rw [norm_div,norm_neg,Complex.norm_ofNat] at hn
  have he := horizontal_neighbor_error t c hcenter ht (by linarith) w v (by linarith) hi hs hp0 hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at he
  have hc : ‖modelDerivative t v+Complex.I*z‖ ≤ 30005*Real.exp (-4*w.re+4) := by
    have hid : modelDerivative t v+Complex.I*z= -(complexSlope t v-modelDerivative t v) := by rw [hz]; ring
    rw [hid,norm_neg]
    exact he
  have hq := model_slope_quadratic_remainder t c hcenter ht (by linarith) w v hr hs hp0 hv (s : ℂ)
    (by simpa only [Complex.norm_real,Real.norm_eq_abs] using hsr.trans (by norm_num : (1/8192 : ℝ)≤1/16))
  simp only [Complex.norm_real,Real.norm_eq_abs] at hq
  have htri := norm_sub_le (modelDerivative t (v+(s : ℂ))+Complex.I*z)
    (modelDerivative t (v+(s : ℂ))-modelDerivative t v-deriv (modelDerivative t) v*(s : ℂ))
  have hid : modelDerivative t (v+(s : ℂ))+Complex.I*z-
      (modelDerivative t (v+(s : ℂ))-modelDerivative t v-deriv (modelDerivative t) v*(s : ℂ))=
      deriv (modelDerivative t) v*(s : ℂ)+(modelDerivative t v+Complex.I*z) := by ring
  rw [hid] at htri
  have hlow := norm_sub_le (deriv (modelDerivative t) v*(s : ℂ)+(modelDerivative t v+Complex.I*z))
    (modelDerivative t v+Complex.I*z)
  rw [add_sub_cancel_right,norm_mul,Complex.norm_real,Real.norm_eq_abs] at hlow
  have hscale := mul_le_mul_of_nonneg_right hn (abs_nonneg s)
  have hs2 := mul_le_mul_of_nonneg_left hsr (by positivity : 0 ≤ 2048*‖c‖*|s|)
  nlinarith [abs_nonneg s]




theorem annulus_slope_derivative_upper (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 10000 ≤ ‖c‖)
    (w v : ℂ) (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖)
    (s : ℝ) (hsr : |s| ≤ 1/8192) :
    ‖deriv (modelDerivative t) (v+(s : ℂ))‖ ≤ 512*‖c‖ := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 < ‖c‖ := by linarith
  let M := ‖w‖+1
  have hM : 1 ≤ M := by dsimp [M]; linarith [norm_nonneg w]
  have hM0 : 0 ≤ M := by linarith
  have hM23 : M^2 ≤ M^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hM) (sq_nonneg M)]
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hmul := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 4*t*‖w‖^3+9 ≤ ‖c‖ := by nlinarith [pow_nonneg (norm_nonneg w) 3]
  have hE := corrected_exp_norm t c hcenter ht0 (by linarith) w v hs hp0 hv
  have hv1 : ‖v-w‖ ≤ 1 := hv.trans ((div_le_iff₀ hx0).mpr (by linarith))
  have htri := norm_add_le (v-w) w
  rw [sub_add_cancel] at htri
  have hvM : ‖v‖ ≤ M := by dsimp [M]; linarith
  have hvs := norm_add_le v (s : ℂ)
  simp only [Complex.norm_real,Real.norm_eq_abs] at hvs
  have hq : ‖v+(s : ℂ)‖ ≤ 2*M := by linarith
  have hq2 := pow_le_pow_left₀ (norm_nonneg (v+(s : ℂ))) hq 2
  have hpoly : t*‖v+(s : ℂ)‖^2 ≤ ‖c‖ := by
    have hm := mul_le_mul_of_nonneg_left hq2 ht0
    have hm2 := mul_le_mul_of_nonneg_left hM23 ht0
    change 100*(t*M^3+1) ≤ ‖c‖ at hp
    nlinarith [mul_nonneg ht0 (pow_nonneg hM0 3)]
  have hsmall : ‖4*(s : ℂ)‖ ≤ 1/4 := by
    rw [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs]
    linarith
  have hexp : ‖Complex.exp (4*(s : ℂ))‖ ≤ 2 := by
    rw [Complex.norm_exp]
    apply (Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hsmall)).trans
    exact RiemannQuarticSaddleNeighborhood.quarter_exp_bounds.2.trans (by norm_num)
  have heq : Complex.exp (4*(v+(s : ℂ)))=Complex.exp (4*v)*Complex.exp (4*(s : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hEq : ‖Complex.exp (4*(v+(s : ℂ)))‖ ≤ 4*‖c‖ := by
    rw [heq,norm_mul]
    have hm := mul_le_mul hE hexp (norm_nonneg _) (by positivity : 0 ≤ 2*‖c‖)
    nlinarith
  rw [(modelDerivative_hasDerivAt t _).deriv]
  have hn := norm_sub_le (12*(t : ℂ)*(v+(s : ℂ))^2)
    (16*(Real.pi : ℂ)*Complex.exp (4*(v+(s : ℂ))))
  simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ht0,abs_of_pos Real.pi_pos] at hn
  have hm := mul_le_mul Real.pi_lt_four.le hEq (norm_nonneg _) (by norm_num : (0 : ℝ)≤4)
  nlinarith


/-- Finite signed integration by parts, retaining the inverse-square gain. -/


theorem signed_model_annulus_bound (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 10000 ≤ ‖c‖)
    (w v : ℂ) (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖)
    (z : ℂ) (hz : complexSlope t v= -(Complex.I*z))
    (r R σ : ℝ) (hr0 : 0 < r) (hrR : r ≤ R) (hR : R ≤ 1/8192) (hσ : |σ|=1)
    (heps : 30005*Real.exp (-4*w.re+4) ≤ ‖c‖*r/2)
    (hsmall : (30005*Real.exp (-4*w.re+4))*R ≤ 1) :
    ‖∫ s : ℝ in r..R, Complex.exp (leadingPhase t z v ((σ*s : ℝ) : ℂ))‖ ≤ 1542/(‖c‖*r) := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 < ‖c‖ := by linarith
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hmul := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 4*t*‖w‖^3+9 ≤ ‖c‖ := by nlinarith [pow_nonneg (norm_nonneg w) 3]
  let E := fun s : ℝ => Complex.exp (leadingPhase t z v ((σ*s : ℝ) : ℂ))
  let H := fun s : ℝ => (σ : ℂ)*(modelDerivative t (v+((σ*s : ℝ) : ℂ))+Complex.I*z)
  let K := fun s : ℝ => (σ : ℂ)^2*deriv (modelDerivative t) (v+((σ*s : ℝ) : ℂ))
  have hσn : ‖(σ : ℂ)‖=1 := by simpa only [Complex.norm_real,Real.norm_eq_abs] using hσ
  have habs (s : ℝ) (h : s ∈ Icc r R) : |σ*s|=s := by
    rw [abs_mul,hσ,one_mul,abs_of_pos (hr0.trans_le h.1)]
  have hEs (s : ℝ) : HasDerivAt E (H s*E s) s := by
    have hd := ((leadingPhase_hasDerivAt t z v ((σ : ℂ)*(s : ℂ))).comp (s : ℂ)
      ((hasDerivAt_id (s : ℂ)).const_mul (σ : ℂ))).cexp.comp_ofReal
    convert hd using 1 <;> dsimp [E,H] <;> simp only [Complex.ofReal_mul] <;> ring
  have hHs (s : ℝ) : HasDerivAt H (K s) s := by
    have hm := modelDerivative_hasDerivAt t (v+((σ : ℂ)*(s : ℂ)))
    have hc := (hm.comp ((σ : ℂ)*(s : ℂ)) ((hasDerivAt_id _).const_add v)).add_const (Complex.I*z)
    have hc' : HasDerivAt (fun u : ℂ => modelDerivative t (v+u)+Complex.I*z)
        (deriv (modelDerivative t) (v+((σ : ℂ)*(s : ℂ)))) ((σ : ℂ)*(s : ℂ)) := by
      convert hc using 1 <;> first | rfl | simp only [hm.deriv,mul_one]
    have hd := ((hc'.comp (s : ℂ) ((hasDerivAt_id (s : ℂ)).const_mul (σ : ℂ))).const_mul (σ : ℂ)).comp_ofReal
    convert hd using 1 <;> dsimp [H,K] <;> simp only [Complex.ofReal_mul] <;> ring
  apply finite_nonstationary_bound E H K ‖c‖ r R hx0 hr0 hrR
    (fun s _ => hEs s) (fun s _ => hHs s)
  · dsimp [K]
    simp_rw [(modelDerivative_hasDerivAt t _).deriv]
    fun_prop
  · intro s h
    have hab := habs s h
    have he := leadingPhase_re_le t c hcenter ht (by linarith) w v hr hi hs hp0 hv z hz (σ*s)
      (by rw [hab]; linarith [h.2])
    have hss := mul_le_mul_of_nonneg_left h.2 (by positivity : 0 ≤ 30005*Real.exp (-4*w.re+4))
    dsimp [E]
    rw [Complex.norm_exp]
    apply (Real.exp_le_exp.mpr (he.trans ?_)).trans Real.exp_one_lt_three.le
    rw [hab]
    linarith
  · intro s h
    dsimp [H]
    rw [norm_mul,hσn,one_mul]
    have hab := habs s h
    have he := mul_le_mul_of_nonneg_left h.1 hx0.le
    have hn := annulus_slope_lower t c hcenter ht hx w v hr hi hs hp hv z hz (σ*s)
      (by rw [hab]; exact h.2.trans hR) (by rw [hab]; linarith)
    simpa only [hab] using hn
  · intro s h
    dsimp [K]
    rw [norm_mul,norm_pow,hσn,one_pow,one_mul]
    apply annulus_slope_derivative_upper t c hcenter ht hx w v hs hp hv (σ*s)
    rw [habs s h]
    exact h.2.trans hR




theorem signed_actual_annulus_bound (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 10000 ≤ ‖c‖)
    (w v : ℂ) (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖)
    (z : ℂ) (hz : complexSlope t v= -(Complex.I*z))
    (r R σ : ℝ) (hr0 : 0 < r) (hrR : r ≤ R) (hR : R ≤ 1/8192) (hσ : |σ|=1)
    (heps : 30005*Real.exp (-4*w.re+4) ≤ ‖c‖*r/2)
    (hsmall : (30005*Real.exp (-4*w.re+4))*R ≤ 1) :
    ‖∫ s : ℝ in r..R, saddleWeight t z (v+((σ*s : ℝ) : ℂ))‖ ≤
      ‖saddleWeight t z v‖*(1542/(‖c‖*r)+180030*Real.exp (-4*w.re+4)*R^2) := by
  have ht0 : 0 ≤ t := by linarith
  have hR0 : 0 < R := hr0.trans_le hrR
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hmul := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 4*t*‖w‖^3+9 ≤ ‖c‖ := by nlinarith [pow_nonneg (norm_nonneg w) 3]
  let A := fun s : ℝ => saddleWeight t z (v+((σ*s : ℝ) : ℂ))
  let E := fun s : ℝ => Complex.exp (leadingPhase t z v ((σ*s : ℝ) : ℂ))
  let W := saddleWeight t z v
  have habs (s : ℝ) (h : s ∈ Icc r R) : |σ*s|=s := by
    rw [abs_mul,hσ,one_mul,abs_of_pos (hr0.trans_le h.1)]
  have hEc : Continuous E := by dsimp [E,leadingPhase]; fun_prop
  have hAc : ContinuousOn A (Icc r R) := by
    intro s h
    have hsr : |σ*s| ≤ 1/16 := by rw [habs s h]; linarith [h.2]
    have hd := horizontal_neighbor_domain t c hcenter ht (by linarith) w v (by linarith) hi hs hp0 hv (σ*s) hsr
    have hk := RiemannThetaComplexKernel.kernelComplex_analyticAt (v+((σ*s : ℝ) : ℂ))
      (by linarith [hd.2.1])
    have hw : AnalyticAt ℂ (saddleWeight t z) (v+((σ*s : ℝ) : ℂ)) := by
      unfold saddleWeight
      apply AnalyticAt.mul
      · fun_prop
      · exact hk
    have hc : ContinuousAt A s := ContinuousAt.comp (g := saddleWeight t z)
      (f := fun s : ℝ => v+((σ*s : ℝ) : ℂ)) hw.continuousAt (by fun_prop)
    exact hc.continuousWithinAt
  have hAi : IntervalIntegrable A volume r R :=
    (hAc.mono (by rw [uIcc_of_le hrR])).intervalIntegrable
  have hEi : IntervalIntegrable (fun s => W*E s) volume r R :=
    (hEc.const_mul W).intervalIntegrable r R
  have herr : ‖(∫ s : ℝ in r..R, A s)-W*(∫ s : ℝ in r..R, E s)‖ ≤
      (180030*Real.exp (-4*w.re+4))*R^2*‖W‖ := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := r) (b := R) (f := fun s => A s-W*E s)
      (C := (180030*Real.exp (-4*w.re+4))*R*‖W‖) ?_
    · rw [intervalIntegral.integral_sub hAi hEi,intervalIntegral.integral_const_mul,
        abs_of_nonneg (sub_nonneg.mpr hrR)] at h
      have hm := mul_le_mul_of_nonneg_left (by linarith : R-r ≤ R)
        (by positivity : 0 ≤ (180030*Real.exp (-4*w.re+4))*R*‖W‖)
      nlinarith
    · intro s h
      rw [uIoc_of_le hrR] at h
      have hscc : s ∈ Icc r R := ⟨h.1.le,h.2⟩
      have hab := habs s hscc
      have hss := mul_le_mul_of_nonneg_left h.2 (by positivity : 0 ≤ 30005*Real.exp (-4*w.re+4))
      have he := actual_weight_leading_absolute_error t c hcenter ht (by linarith) w v hr hi hs hp0 hv z hz (σ*s)
        (by rw [hab]; linarith [h.2]) (by rw [hab]; linarith)
      change ‖A s-W*E s‖ ≤ _ at he
      rw [hab] at he
      have hm := mul_le_mul_of_nonneg_right h.2
        (by positivity : 0 ≤ (180030*Real.exp (-4*w.re+4))*‖W‖)
      nlinarith
  have hmodel := signed_model_annulus_bound t c hcenter ht hx w v hr hi hs hp hv z hz r R σ hr0 hrR hR hσ heps hsmall
  change ‖∫ s : ℝ in r..R, E s‖ ≤ _ at hmodel
  have ht := norm_add_le ((∫ s : ℝ in r..R, A s)-W*(∫ s : ℝ in r..R, E s))
    (W*(∫ s : ℝ in r..R, E s))
  rw [sub_add_cancel,norm_mul] at ht
  have hm := mul_le_mul_of_nonneg_left hmodel (norm_nonneg W)
  change ‖∫ s : ℝ in r..R, A s‖ ≤ _
  nlinarith




theorem relative_actual_annulus_bound (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 10000 ≤ ‖c‖)
    (w v : ℂ) (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖)
    (z : ℂ) (hz : complexSlope t v= -(Complex.I*z))
    (r R σ : ℝ) (hr0 : 0 < r) (hrR : r ≤ R) (hR : R ≤ 1/8192) (hσ : |σ|=1)
    (heps : 30005*Real.exp (-4*w.re+4) ≤ ‖c‖*r/2)
    (hsmall : (30005*Real.exp (-4*w.re+4))*R ≤ 1) :
    ‖(∫ s : ℝ in r..R, saddleWeight t z (v+((σ*s : ℝ) : ℂ)))/
      (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤
      2*Real.sqrt ‖c‖*(1542/(‖c‖*r)+180030*Real.exp (-4*w.re+4)*R^2) := by
  have ht0 : 0 ≤ t := by linarith
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hmul := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 4*t*‖w‖^3+9 ≤ ‖c‖ := by nlinarith [pow_nonneg (norm_nonneg w) 3]
  have he := signed_actual_annulus_bound t c hcenter ht hx w v hr hi hs hp hv z hz r R σ hr0 hrR hR hσ heps hsmall
  let W := saddleWeight t z v
  let G := ∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)
  let B := 1542/(‖c‖*r)+180030*Real.exp (-4*w.re+4)*R^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hnormal := gaussian_normalization_lower t c hcenter ht hx w v hr hi hp hs hv
  change 1 ≤ 2*Real.sqrt ‖c‖*‖G‖ at hnormal
  have hG : G ≠ 0 := by intro h; norm_num [h] at hnormal
  have hd := horizontal_neighbor_domain t c hcenter ht (by linarith) w v (by linarith) hi hs hp0 hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hd
  have hW : W ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _)
    (RiemannThetaComplexKernel.kernel_ne_zero v hd.1 hd.2.1)
  change ‖(∫ s : ℝ in r..R, saddleWeight t z (v+((σ*s : ℝ) : ℂ)))/(W*G)‖ ≤ 2*Real.sqrt ‖c‖*B
  rw [norm_div,norm_mul]
  apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hW) (norm_pos_iff.mpr hG))).mpr
  have hm := mul_le_mul_of_nonneg_left hnormal (mul_nonneg (norm_nonneg W) hB)
  change ‖(∫ s : ℝ in r..R, saddleWeight t z (v+((σ*s : ℝ) : ℂ)))‖ ≤
    (2*Real.sqrt ‖c‖*B)*(‖W‖*‖G‖)
  change ‖(∫ s : ℝ in r..R, saddleWeight t z (v+((σ*s : ℝ) : ℂ)))‖ ≤ ‖W‖*B at he
  nlinarith


open RiemannQuarticErrorLimits



private theorem annulus_budget_identity (R x : ℝ) (hx : 0 < x) :
    2*Real.sqrt x*(1542/(x*centralRadius x)+6*(100000000/x)*R^2)=annulusBudget R x := by
  have hpre : Real.sqrt x/x=x^(-1/2 : ℝ) := by
    calc
      _ = x^(1/2 : ℝ)/x^(1 : ℝ) := by rw [Real.sqrt_eq_rpow,Real.rpow_one]
      _ = x^((1/2 : ℝ)-1) := (Real.rpow_sub hx _ _).symm
      _ = _ := by norm_num
  dsimp [annulusBudget]
  calc
    _ = 3084*(Real.sqrt x/(x*centralRadius x))+1200000000*R^2*(Real.sqrt x/x) := by ring
    _ = _ := by rw [gaussian_scaled_prefactor x hx,hpre]



private theorem actual_weight_continuousOn (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c‖)
    (w v : ℂ) (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖) (z : ℂ)
    (R : ℝ) (hR : R < 1/16) :
    ContinuousOn (fun s : ℝ => saddleWeight t z (v+(s : ℂ))) (Icc (-R) R) := by
  intro s h
  have hd := horizontal_neighbor_domain t c hcenter ht hx w v hr hi hs hp hv s
    ((abs_le.mpr h).trans hR.le)
  have hk := RiemannThetaComplexKernel.kernelComplex_analyticAt (v+(s : ℂ))
    (by linarith [hd.2.1])
  have hw : AnalyticAt ℂ (saddleWeight t z) (v+(s : ℂ)) := by
    unfold saddleWeight
    apply AnalyticAt.mul
    · fun_prop
    · exact hk
  have hc : ContinuousAt (fun a : ℝ => saddleWeight t z (v+(a : ℂ))) s :=
    ContinuousAt.comp (g := saddleWeight t z) (f := fun a : ℝ => v+(a : ℂ))
      hw.continuousAt (by fun_prop)
  exact hc.continuousWithinAt



theorem actual_neighborhood_split (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖c‖)
    (w v : ℂ) (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖) (z : ℂ)
    (r R : ℝ) (hr0 : 0 ≤ r) (hrR : r ≤ R) (hR : R < 1/16) :
    (∫ s : ℝ in -R..R, saddleWeight t z (v+(s : ℂ)))=
      (∫ s : ℝ in -r..r, saddleWeight t z (v+(s : ℂ)))+
      (∫ s : ℝ in r..R, saddleWeight t z (v+((-s : ℝ) : ℂ)))+
      (∫ s : ℝ in r..R, saddleWeight t z (v+(s : ℂ))) := by
  let f := fun s : ℝ => saddleWeight t z (v+(s : ℂ))
  have hc := actual_weight_continuousOn t c hcenter ht hx w v hr hi hs hp hv z R hR
  have hf (a b : ℝ) (ha : a ∈ Icc (-R) R) (hb : b ∈ Icc (-R) R) :
      IntervalIntegrable f volume a b :=
    (hc.mono (uIcc_subset_Icc ha hb)).intervalIntegrable
  have hR0 : 0 ≤ R := hr0.trans hrR
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hf (-R) (-r) ⟨le_rfl,by linarith⟩ ⟨by linarith,by linarith⟩)
    (hf (-r) r ⟨by linarith,by linarith⟩ ⟨by linarith,hrR⟩)
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (hf (-R) r ⟨le_rfl,by linarith⟩ ⟨by linarith,hrR⟩)
    (hf r R ⟨by linarith,hrR⟩ ⟨by linarith,le_rfl⟩)
  have hneg := intervalIntegral.integral_comp_neg (a := r) (b := R) f
  change (∫ s : ℝ in -R..R, f s)=(∫ s : ℝ in -r..r, f s)+
    (∫ s : ℝ in r..R, f (-s))+(∫ s : ℝ in r..R, f s)
  linear_combination -h2-h1-hneg


theorem uniform_relative_annulus (R η : ℝ) (hR0 : 0 < R)
    (hR : R ≤ 1/8192) (hη : 0 < η) :
    ∃ N : ℝ, ∀ c : ℂ, c.im ≤ 0 → N ≤ ‖c‖ → ∀ t : ℝ, 1 ≤ t → ∀ w v : ℂ,
      64 ≤ w.re → |w.im| ≤ 1/2 → 100*(t*(‖w‖+1)^3+1) ≤ ‖c‖ →
      modelDerivative t w = -(Complex.I*c) → ‖v-w‖ ≤ 1/‖c‖ →
      ∀ z : ℂ, complexSlope t v = -(Complex.I*z) → ∀ σ : ℝ, |σ| = 1 →
      ‖(∫ s : ℝ in centralRadius ‖c‖..R, saddleWeight t z (v+((σ*s : ℝ) : ℂ)))/
        (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤ η := by
  have hgrow : Tendsto (fun x : ℝ => x*centralRadius x) atTop atTop := by
    apply (tendsto_rpow_atTop (by norm_num : (0 : ℝ)<9/16)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    dsimp [centralRadius]
    calc
      _ = x^((1 : ℝ)+(-7/16)) := by norm_num
      _ = _ := by rw [Real.rpow_add hx,Real.rpow_one]
  have hb : ∀ᶠ x : ℝ in atTop, 200000000 ≤ x ∧ centralRadius x < R ∧
      1 ≤ x*centralRadius x ∧ annulusBudget R x < η := by
    filter_upwards [eventually_ge_atTop (200000000 : ℝ),
      centralRadius_tendsto_zero.eventually (gt_mem_nhds hR0),
      hgrow.eventually (eventually_ge_atTop (1 : ℝ)),
      (annulusBudget_tendsto_zero R).eventually (gt_mem_nhds hη)] with x hx hr hg hbudget
    exact ⟨hx,hr,hg,hbudget⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp hb
  refine ⟨N,?_⟩
  intro c hc hlarge t ht w v hrw hi hp hs hv z hz σ hσ
  obtain ⟨hx,hr,hg,hbudget⟩ := hN ‖c‖ hlarge
  have hx0 : 0 < ‖c‖ := by linarith
  have he := arithmetic_error_frequency_bound t c hc ht (by linarith) w hp hs
  have hehalf : 100000000/‖c‖ ≤ (1/2 : ℝ) := (div_le_iff₀ hx0).mpr (by linarith)
  have hrpos : 0 < centralRadius ‖c‖ := Real.rpow_pos_of_pos hx0 _
  have hsmall : (30005*Real.exp (-4*w.re+4))*R ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_right (he.trans hehalf) hR0.le
    linarith
  have hbound := relative_actual_annulus_bound t c hc ht (by linarith) w v hrw hi hs hp hv z hz
    (centralRadius ‖c‖) R σ hrpos hr.le hR hσ (by linarith) hsmall
  apply hbound.trans
  apply le_trans _ hbudget.le
  rw [← annulus_budget_identity R ‖c‖ hx0]
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2*Real.sqrt ‖c‖)
  have hm := mul_le_mul_of_nonneg_right he (sq_nonneg R)
  linarith

theorem uniform_fixed_gaussian_error (R η : ℝ) (hR0 : 0 < R)
    (hR : R ≤ 1/8192) (hη : 0 < η) :
    ∃ N : ℝ, ∀ c : ℂ, c.im ≤ 0 → N ≤ ‖c‖ → ∀ t : ℝ, 1 ≤ t → ∀ w v : ℂ,
      64 ≤ w.re → |w.im| ≤ 1/2 → 100*(t*(‖w‖+1)^3+1) ≤ ‖c‖ →
      modelDerivative t w = -(Complex.I*c) → ‖v-w‖ ≤ 1/‖c‖ →
      ∀ z : ℂ, complexSlope t v = -(Complex.I*z) →
      ‖(∫ s : ℝ in -R..R, saddleWeight t z (v+(s : ℂ)))/
        (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))-1‖ ≤ η := by
  obtain ⟨N₁,hN₁⟩ := uniform_local_gaussian_error (η/4) (by positivity)
  obtain ⟨N₂,hN₂⟩ := uniform_relative_annulus R (η/4) hR0 hR (by positivity)
  obtain ⟨N₃,hN₃⟩ := eventually_atTop.mp
    (centralRadius_tendsto_zero.eventually (gt_mem_nhds hR0))
  refine ⟨max (max N₁ N₂) (max N₃ 10000),?_⟩
  intro c hc hlarge t ht w v hr hi hp hs hv z hz
  have hNc : max N₁ N₂ ≤ ‖c‖ := (le_max_left _ _).trans hlarge
  have hN₁c : N₁ ≤ ‖c‖ := (le_max_left _ _).trans hNc
  have hN₂c : N₂ ≤ ‖c‖ := (le_max_right _ _).trans hNc
  have hNx : max N₃ 10000 ≤ ‖c‖ := (le_max_right _ _).trans hlarge
  have hx : 10000 ≤ ‖c‖ := (le_max_right _ _).trans hNx
  have hradius : centralRadius ‖c‖ < R := hN₃ ‖c‖ ((le_max_left _ _).trans hNx)
  have ht0 : 0 ≤ t := by linarith
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hmul := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 4*t*‖w‖^3+9 ≤ ‖c‖ := by nlinarith [pow_nonneg (norm_nonneg w) 3]
  have hspl := actual_neighborhood_split t c hc ht (by linarith) w v (by linarith) hi hs hp0 hv z
    (centralRadius ‖c‖) R (Real.rpow_pos_of_pos (by linarith : 0 < ‖c‖) _).le hradius.le (by linarith)
  have hlocal := hN₁ c hc hN₁c t ht w v hr hi hp hs hv z hz
  have hl := hN₂ c hc hN₂c t ht w v hr hi hp hs hv z hz (-1) (by norm_num)
  have hu := hN₂ c hc hN₂c t ht w v hr hi hp hs hv z hz 1 (by norm_num)
  simp only [neg_one_mul,one_mul] at hl hu
  let D := saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2))
  let C := ∫ s : ℝ in -(centralRadius ‖c‖)..centralRadius ‖c‖, saddleWeight t z (v+(s : ℂ))
  let L := ∫ s : ℝ in centralRadius ‖c‖..R, saddleWeight t z (v+((-s : ℝ) : ℂ))
  let U := ∫ s : ℝ in centralRadius ‖c‖..R, saddleWeight t z (v+(s : ℂ))
  change ‖C/D-1‖ ≤ η/4 at hlocal
  change ‖L/D‖ ≤ η/4 at hl
  change ‖U/D‖ ≤ η/4 at hu
  rw [hspl]
  change ‖(C+L+U)/D-1‖ ≤ η
  have hid : (C+L+U)/D-1=(C/D-1)+L/D+U/D := by ring
  rw [hid]
  have h1 := norm_add_le (C/D-1) (L/D)
  have h2 := norm_add_le ((C/D-1)+L/D) (U/D)
  linarith

theorem eventually_actual_fixed_gaussian (t : ℝ) (ht : 1 ≤ t) (R η : ℝ)
    (hR0 : 0 < R) (hR : R ≤ 1/8192) (hη : 0 < η) :
    ∀ᶠ a : ℝ in atTop, ∀ c : ℂ, c.im ≤ 0 → ‖c‖ = 4*Real.pi*Real.exp (4*a) →
      ∃ v : ℂ, complexSlope t v = -(Complex.I*c) ∧
        1 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ kernelComplex v ≠ 0 ∧
        ‖(∫ s : ℝ in -R..R, saddleWeight t c (v+(s : ℂ)))/
          (saddleWeight t c v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))-1‖ ≤ η := by
  obtain ⟨N,hN⟩ := uniform_fixed_gaussian_error R η hR0 hR hη
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

theorem far_actual_fixed_gaussian (t : ℝ) (ht : 1 ≤ t) (R η : ℝ)
    (hR0 : 0 < R) (hR : R ≤ 1/8192) (hη : 0 < η) (hη1 : η < 1) :
    ∃ X : ℝ, 0 < X ∧ ∀ c : ℂ, X ≤ ‖c‖ → c.im ≤ 0 → ∃ v : ℂ,
      complexSlope t v = -(Complex.I*c) ∧
      1 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ kernelComplex v ≠ 0 ∧
      ‖(∫ s : ℝ in -R..R, saddleWeight t c (v+(s : ℂ)))/
        (saddleWeight t c v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))-1‖ ≤ η ∧
      (∫ s : ℝ in -R..R, saddleWeight t c (v+(s : ℂ))) ≠ 0 := by
  obtain ⟨A,hA⟩ := eventually_atTop.mp (eventually_actual_fixed_gaussian t ht R η hR0 hR hη)
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
  obtain ⟨v,hroot,hr,hi,hkn,hrel⟩ := hA a hAa c him hn
  refine ⟨v,hroot,hr,hi,hkn,hrel,?_⟩
  intro hz
  rw [hz,zero_div,zero_sub,norm_neg,norm_one] at hrel
  linarith

end OperatorDerivativeRewrite.Foundation.RiemannQuarticComplexAnnulus
