import Foundation.RiemannSixthFarGaussianLimit
import Foundation.RiemannQuarticFarAnnulus
/-! Signed actual A6 annular estimates using verified nonstationary
integration by parts. The actual-saddle model mismatch is retained. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthFarAnnulus
open RiemannSixthFarGaussianLocal RiemannSixthFarGaussianLimit
open RiemannSixthFarCorrection RiemannSixthFarRemainder RiemannSixthFarSignedIntegral
open RiemannEvenModelPhase RiemannEvenSaddleBranch RiemannEvenComplexWeight
open RiemannQuarticErrorLimits
open RiemannQuarticFarAnnulus (exponential_quadratic_remainder finite_nonstationary_bound
  annulusBudget annulusBudget_tendsto_zero)

theorem model_slope_quadratic_remainder (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x)
    (w v : ℂ) (hr : 4096 ≤ w.re)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
    (hp : 6*t*‖w‖^5+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x) (u : ℂ) (hu : ‖u‖ ≤ 1/16) :
    ‖modelDerivative 3 t (v+u)-modelDerivative 3 t v-deriv (modelDerivative 3 t) v*u‖ ≤
      2048*x*‖u‖^2 := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 ≤ x := by linarith
  have he := exponential_quadratic_remainder u hu
  have hE := corrected_exp_norm t x ht0 hx w v hs hp hv
  have hP := corrected_polynomial_scale t x ht hx w v hr hp hv
  have hid : modelDerivative 3 t (v+u)-modelDerivative 3 t v-deriv (modelDerivative 3 t) v*u=
      (t : ℂ)*(60*v^3+60*v^2*u+30*v*u^2+6*u^3)*u^2-
        4*(Real.pi : ℂ)*Complex.exp (4*v)*(Complex.exp (4*u)-1-4*u) := by
    rw [(modelDerivative_hasDerivAt 3 t v).deriv]
    unfold modelDerivative
    rw [show 4*(v+u)=4*v+4*u by ring,Complex.exp_add]
    ring
  rw [hid]
  have htri := norm_sub_le ((t : ℂ)*(60*v^3+60*v^2*u+30*v*u^2+6*u^3)*u^2)
    (4*(Real.pi : ℂ)*Complex.exp (4*v)*(Complex.exp (4*u)-1-4*u))
  simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ht0,abs_of_pos Real.pi_pos] at htri
  have hadd1 := norm_add_le (60*v^3) (60*v^2*u)
  have hadd2 := norm_add_le (60*v^3+60*v^2*u) (30*v*u^2)
  have hadd3 := norm_add_le (60*v^3+60*v^2*u+30*v*u^2) (6*u^3)
  simp only [norm_mul,norm_pow,Complex.norm_ofNat] at hadd1 hadd2 hadd3
  have hunit : ‖u‖ ≤ 1 := by linarith
  have hu2 : ‖u‖^2 ≤ 1 := pow_le_one₀ (norm_nonneg u) hunit
  have hu3 : ‖u‖^3 ≤ 1 := pow_le_one₀ (norm_nonneg u) hunit
  have hm1 := mul_le_mul_of_nonneg_left hunit (by positivity : 0 ≤ 60*‖v‖^2)
  have hm2 := mul_le_mul_of_nonneg_left hu2 (by positivity : 0 ≤ 30*‖v‖)
  have hfac : ‖60*v^3+60*v^2*u+30*v*u^2+6*u^3‖ ≤ 156*(‖v‖+1)^3 := by
    nlinarith [norm_nonneg v,pow_nonneg (norm_nonneg v) 3,sq_nonneg ‖v‖]
  have hpoly : t*‖60*v^3+60*v^2*u+30*v*u^2+6*u^3‖ ≤ 4*x := by
    have hm := mul_le_mul_of_nonneg_left hfac ht0
    nlinarith [mul_nonneg ht0 (pow_nonneg (by positivity : 0 ≤ ‖v‖+1) 3)]
  have hpoly2 := mul_le_mul_of_nonneg_right hpoly (sq_nonneg ‖u‖)
  have hpe := mul_le_mul Real.pi_lt_four.le hE (norm_nonneg _) (by norm_num : (0 : ℝ)≤4)
  have hrem := mul_le_mul hpe he (norm_nonneg _) (by positivity : 0 ≤ 4*(2*x))
  nlinarith [sq_nonneg ‖u‖]

theorem annulus_slope_lower (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x)
    (w v : ℂ) (hr : 4096 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
    (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hz : complexSlope 3 t v= -(Complex.I*z))
    (s : ℝ) (hsr : |s| ≤ 1/8192)
    (heps : 30005*Real.exp (-4*w.re+4) ≤ x*|s|/2) :
    x*|s| ≤ ‖modelDerivative 3 t (v+(s : ℂ))+Complex.I*z‖ := by
  have ht0 : 0 ≤ t := by linarith
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 5
  have hmul := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 6*t*‖w‖^5+9 ≤ x := by nlinarith [pow_nonneg (norm_nonneg w) 5]
  have hn := (gaussian_coefficient_norm_bounds t x ht hx w v hp hs hv).1
  rw [norm_div,norm_neg,Complex.norm_ofNat] at hn
  have he := horizontal_neighbor_error t x ht (by linarith) w v (by linarith) hi hs hp0 hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at he
  have hc : ‖modelDerivative 3 t v+Complex.I*z‖ ≤ 30005*Real.exp (-4*w.re+4) := by
    have hid : modelDerivative 3 t v+Complex.I*z= -(complexSlope 3 t v-modelDerivative 3 t v) := by rw [hz]; ring
    rw [hid,norm_neg]
    exact he
  have hq := model_slope_quadratic_remainder t x ht (by linarith) w v hr hs hp0 hv (s : ℂ)
    (by simpa only [Complex.norm_real,Real.norm_eq_abs] using hsr.trans (by norm_num : (1/8192 : ℝ)≤1/16))
  simp only [Complex.norm_real,Real.norm_eq_abs] at hq
  have htri := norm_sub_le (modelDerivative 3 t (v+(s : ℂ))+Complex.I*z)
    (modelDerivative 3 t (v+(s : ℂ))-modelDerivative 3 t v-deriv (modelDerivative 3 t) v*(s : ℂ))
  have hid : modelDerivative 3 t (v+(s : ℂ))+Complex.I*z-
      (modelDerivative 3 t (v+(s : ℂ))-modelDerivative 3 t v-deriv (modelDerivative 3 t) v*(s : ℂ))=
      deriv (modelDerivative 3 t) v*(s : ℂ)+(modelDerivative 3 t v+Complex.I*z) := by ring
  rw [hid] at htri
  have hlow := norm_sub_le (deriv (modelDerivative 3 t) v*(s : ℂ)+(modelDerivative 3 t v+Complex.I*z))
    (modelDerivative 3 t v+Complex.I*z)
  rw [add_sub_cancel_right,norm_mul,Complex.norm_real,Real.norm_eq_abs] at hlow
  have hscale := mul_le_mul_of_nonneg_right hn (abs_nonneg s)
  have hs2 := mul_le_mul_of_nonneg_left hsr (by positivity : 0 ≤ 2048*x*|s|)
  nlinarith [abs_nonneg s]


theorem annulus_slope_derivative_upper (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x)
    (w v : ℂ) (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
    (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (s : ℝ) (hsr : |s| ≤ 1/8192) :
    ‖deriv (modelDerivative 3 t) (v+(s : ℂ))‖ ≤ 512*x := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 < x := by linarith
  let M := ‖w‖+1
  have hM : 1 ≤ M := by dsimp [M]; linarith [norm_nonneg w]
  have hM0 : 0 ≤ M := by linarith
  have hM45 : M^4 ≤ M^5 := pow_le_pow_right₀ hM (by norm_num)
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 5
  have hmul := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 6*t*‖w‖^5+9 ≤ x := by nlinarith [pow_nonneg (norm_nonneg w) 5]
  have hE := corrected_exp_norm t x ht0 (by linarith) w v hs hp0 hv
  have hv1 : ‖v-w‖ ≤ 1 := hv.trans ((div_le_iff₀ hx0).mpr (by linarith))
  have htri := norm_add_le (v-w) w
  rw [sub_add_cancel] at htri
  have hvM : ‖v‖ ≤ M := by dsimp [M]; linarith
  have hvs := norm_add_le v (s : ℂ)
  simp only [Complex.norm_real,Real.norm_eq_abs] at hvs
  have hq : ‖v+(s : ℂ)‖ ≤ 2*M := by linarith
  have hq4 := pow_le_pow_left₀ (norm_nonneg (v+(s : ℂ))) hq 4
  have hpoly : t*‖v+(s : ℂ)‖^4 ≤ x := by
    have hm := mul_le_mul_of_nonneg_left hq4 ht0
    have hm2 := mul_le_mul_of_nonneg_left hM45 ht0
    change 10000*(t*M^5+1) ≤ x at hp
    nlinarith [mul_nonneg ht0 (pow_nonneg hM0 5)]
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
  have hEq : ‖Complex.exp (4*(v+(s : ℂ)))‖ ≤ 4*x := by
    rw [heq,norm_mul]
    have hm := mul_le_mul hE hexp (norm_nonneg _) (by positivity : 0 ≤ 2*x)
    nlinarith
  have hder : deriv (modelDerivative 3 t) (v+(s : ℂ)) =
      30*(t : ℂ)*(v+(s : ℂ))^4-16*(Real.pi : ℂ)*Complex.exp (4*(v+(s : ℂ))) := by
    rw [(modelDerivative_hasDerivAt 3 t _).deriv]
    norm_num
  rw [hder]
  have hn := norm_sub_le (30*(t : ℂ)*(v+(s : ℂ))^4)
    (16*(Real.pi : ℂ)*Complex.exp (4*(v+(s : ℂ))))
  simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ht0,abs_of_pos Real.pi_pos] at hn
  have hm := mul_le_mul Real.pi_lt_four.le hEq (norm_nonneg _) (by norm_num : (0 : ℝ)≤4)
  nlinarith


theorem signed_model_annulus_bound (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x)
    (w v : ℂ) (hr : 4096 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
    (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hz : complexSlope 3 t v= -(Complex.I*z))
    (r R σ : ℝ) (hr0 : 0 < r) (hrR : r ≤ R) (hR : R ≤ 1/8192) (hσ : |σ|=1)
    (heps : 30005*Real.exp (-4*w.re+4) ≤ x*r/2)
    (hsmall : (30005*Real.exp (-4*w.re+4))*R ≤ 1) :
    ‖∫ s : ℝ in r..R, Complex.exp (leadingPhase t z v ((σ*s : ℝ) : ℂ))‖ ≤ 1542/(x*r) := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 < x := by linarith
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 5
  have hmul := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 6*t*‖w‖^5+9 ≤ x := by nlinarith [pow_nonneg (norm_nonneg w) 5]
  let E := fun s : ℝ => Complex.exp (leadingPhase t z v ((σ*s : ℝ) : ℂ))
  let H := fun s : ℝ => (σ : ℂ)*(modelDerivative 3 t (v+((σ*s : ℝ) : ℂ))+Complex.I*z)
  let K := fun s : ℝ => (σ : ℂ)^2*deriv (modelDerivative 3 t) (v+((σ*s : ℝ) : ℂ))
  have hσn : ‖(σ : ℂ)‖=1 := by simpa only [Complex.norm_real,Real.norm_eq_abs] using hσ
  have habs (s : ℝ) (h : s ∈ Icc r R) : |σ*s|=s := by
    rw [abs_mul,hσ,one_mul,abs_of_pos (hr0.trans_le h.1)]
  have hEs (s : ℝ) : HasDerivAt E (H s*E s) s := by
    have hd := ((leadingPhase_hasDerivAt t z v ((σ : ℂ)*(s : ℂ))).comp (s : ℂ)
      ((hasDerivAt_id (s : ℂ)).const_mul (σ : ℂ))).cexp.comp_ofReal
    convert hd using 1 <;> dsimp [E,H] <;> simp only [Complex.ofReal_mul] <;> ring
  have hHs (s : ℝ) : HasDerivAt H (K s) s := by
    have hm := modelDerivative_hasDerivAt 3 t (v+((σ : ℂ)*(s : ℂ)))
    have hc := (hm.comp ((σ : ℂ)*(s : ℂ)) ((hasDerivAt_id _).const_add v)).add_const (Complex.I*z)
    have hc' : HasDerivAt (fun u : ℂ => modelDerivative 3 t (v+u)+Complex.I*z)
        (deriv (modelDerivative 3 t) (v+((σ : ℂ)*(s : ℂ)))) ((σ : ℂ)*(s : ℂ)) := by
      convert hc using 1 <;> first | rfl | simp only [hm.deriv,mul_one]
    have hd := ((hc'.comp (s : ℂ) ((hasDerivAt_id (s : ℂ)).const_mul (σ : ℂ))).const_mul (σ : ℂ)).comp_ofReal
    convert hd using 1 <;> dsimp [H,K] <;> simp only [Complex.ofReal_mul] <;> ring
  apply finite_nonstationary_bound E H K x r R hx0 hr0 hrR
    (fun s _ => hEs s) (fun s _ => hHs s)
  · dsimp [K]
    simp_rw [(modelDerivative_hasDerivAt 3 t _).deriv]
    fun_prop
  · intro s h
    have hab := habs s h
    have he := leadingPhase_re_le t x ht (by linarith) w v hr hi hs hp0 hv z hz (σ*s)
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
    have hn := annulus_slope_lower t x ht hx w v hr hi hs hp hv z hz (σ*s)
      (by rw [hab]; exact h.2.trans hR) (by rw [hab]; linarith)
    simpa only [hab] using hn
  · intro s h
    dsimp [K]
    rw [norm_mul,norm_pow,hσn,one_pow,one_mul]
    apply annulus_slope_derivative_upper t x ht hx w v hs hp hv (σ*s)
    rw [habs s h]
    exact h.2.trans hR


theorem signed_actual_annulus_bound (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x)
    (w v : ℂ) (hr : 4096 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
    (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hz : complexSlope 3 t v= -(Complex.I*z))
    (r R σ : ℝ) (hr0 : 0 < r) (hrR : r ≤ R) (hR : R ≤ 1/8192) (hσ : |σ|=1)
    (heps : 30005*Real.exp (-4*w.re+4) ≤ x*r/2)
    (hsmall : (30005*Real.exp (-4*w.re+4))*R ≤ 1) :
    ‖∫ s : ℝ in r..R, weight 3 t z (v+((σ*s : ℝ) : ℂ))‖ ≤
      ‖weight 3 t z v‖*(1542/(x*r)+180030*Real.exp (-4*w.re+4)*R^2) := by
  have ht0 : 0 ≤ t := by linarith
  have hR0 : 0 < R := hr0.trans_le hrR
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 5
  have hmul := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 6*t*‖w‖^5+9 ≤ x := by nlinarith [pow_nonneg (norm_nonneg w) 5]
  let A := fun s : ℝ => weight 3 t z (v+((σ*s : ℝ) : ℂ))
  let E := fun s : ℝ => Complex.exp (leadingPhase t z v ((σ*s : ℝ) : ℂ))
  let W := weight 3 t z v
  have habs (s : ℝ) (h : s ∈ Icc r R) : |σ*s|=s := by
    rw [abs_mul,hσ,one_mul,abs_of_pos (hr0.trans_le h.1)]
  have hEc : Continuous E := by dsimp [E,leadingPhase]; fun_prop
  have hAc : ContinuousOn A (Icc r R) := by
    intro s h
    have hsr : |σ*s| ≤ 1/16 := by rw [habs s h]; linarith [h.2]
    have hd := horizontal_neighbor_domain t x ht (by linarith) w v (by linarith) hi hs hp0 hv (σ*s) hsr
    have hk := RiemannThetaComplexKernel.kernelComplex_analyticAt (v+((σ*s : ℝ) : ℂ))
      (by linarith [hd.2.1])
    have hw : AnalyticAt ℂ (weight 3 t z) (v+((σ*s : ℝ) : ℂ)) := by
      unfold weight
      apply AnalyticAt.mul
      · fun_prop
      · exact hk
    have hc : ContinuousAt A s := ContinuousAt.comp (g := weight 3 t z)
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
      have he := actual_weight_leading_absolute_error t x ht (by linarith) w v hr hi hs hp0 hv z hz (σ*s)
        (by rw [hab]; linarith [h.2]) (by rw [hab]; linarith)
      change ‖A s-W*E s‖ ≤ _ at he
      rw [hab] at he
      have hm := mul_le_mul_of_nonneg_right h.2
        (by positivity : 0 ≤ (180030*Real.exp (-4*w.re+4))*‖W‖)
      nlinarith
  have hmodel := signed_model_annulus_bound t x ht hx w v hr hi hs hp hv z hz r R σ hr0 hrR hR hσ heps hsmall
  change ‖∫ s : ℝ in r..R, E s‖ ≤ _ at hmodel
  have ht := norm_add_le ((∫ s : ℝ in r..R, A s)-W*(∫ s : ℝ in r..R, E s))
    (W*(∫ s : ℝ in r..R, E s))
  rw [sub_add_cancel,norm_mul] at ht
  have hm := mul_le_mul_of_nonneg_left hmodel (norm_nonneg W)
  change ‖∫ s : ℝ in r..R, A s‖ ≤ _
  nlinarith


theorem relative_actual_annulus_bound (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x)
    (w v : ℂ) (hr : 4096 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
    (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hz : complexSlope 3 t v= -(Complex.I*z))
    (r R σ : ℝ) (hr0 : 0 < r) (hrR : r ≤ R) (hR : R ≤ 1/8192) (hσ : |σ|=1)
    (heps : 30005*Real.exp (-4*w.re+4) ≤ x*r/2)
    (hsmall : (30005*Real.exp (-4*w.re+4))*R ≤ 1) :
    ‖(∫ s : ℝ in r..R, weight 3 t z (v+((σ*s : ℝ) : ℂ)))/
      (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))‖ ≤
      2*Real.sqrt x*(1542/(x*r)+180030*Real.exp (-4*w.re+4)*R^2) := by
  have ht0 : 0 ≤ t := by linarith
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 5
  have hmul := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 6*t*‖w‖^5+9 ≤ x := by nlinarith [pow_nonneg (norm_nonneg w) 5]
  have he := signed_actual_annulus_bound t x ht hx w v hr hi hs hp hv z hz r R σ hr0 hrR hR hσ heps hsmall
  let W := weight 3 t z v
  let G := ∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)
  let B := 1542/(x*r)+180030*Real.exp (-4*w.re+4)*R^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hnormal := gaussian_normalization_lower t x ht hx w v hr hi hp hs hv
  change 1 ≤ 2*Real.sqrt x*‖G‖ at hnormal
  have hG : G ≠ 0 := by intro h; norm_num [h] at hnormal
  have hd := horizontal_neighbor_domain t x ht (by linarith) w v (by linarith) hi hs hp0 hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hd
  have hW : W ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _)
    (RiemannThetaComplexKernel.kernel_ne_zero v hd.1 hd.2.1)
  change ‖(∫ s : ℝ in r..R, weight 3 t z (v+((σ*s : ℝ) : ℂ)))/(W*G)‖ ≤ 2*Real.sqrt x*B
  rw [norm_div,norm_mul]
  apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hW) (norm_pos_iff.mpr hG))).mpr
  have hm := mul_le_mul_of_nonneg_left hnormal (mul_nonneg (norm_nonneg W) hB)
  change ‖(∫ s : ℝ in r..R, weight 3 t z (v+((σ*s : ℝ) : ℂ)))‖ ≤
    (2*Real.sqrt x*B)*(‖W‖*‖G‖)
  change ‖(∫ s : ℝ in r..R, weight 3 t z (v+((σ*s : ℝ) : ℂ)))‖ ≤ ‖W‖*B at he
  nlinarith


theorem annulus_budget_identity (R x : ℝ) (hx : 0 < x) :
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

theorem eventually_uniform_relative_annulus (R η : ℝ) (hR0 : 0 < R)
    (hR : R ≤ 1/8192) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, 1 ≤ t → ∀ w v : ℂ,
      4096 ≤ w.re → |w.im| ≤ 1/2 → 10000*(t*(‖w‖+1)^5+1) ≤ x →
      modelDerivative 3 t w= -(Complex.I*(x : ℂ)) → ‖v-w‖ ≤ 1/x →
      ∀ z : ℂ, complexSlope 3 t v= -(Complex.I*z) → ∀ σ : ℝ, |σ|=1 →
      ‖(∫ s : ℝ in centralRadius x..R, weight 3 t z (v+((σ*s : ℝ) : ℂ)))/
        (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))‖ ≤ η := by
  have hgrow : Tendsto (fun x : ℝ => x*centralRadius x) atTop atTop := by
    apply (tendsto_rpow_atTop (by norm_num : (0 : ℝ)<9/16)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    dsimp [centralRadius]
    calc
      _ = x^((1 : ℝ)+(-7/16)) := by norm_num
      _ = _ := by rw [Real.rpow_add hx,Real.rpow_one]
  filter_upwards [eventually_ge_atTop (200000000 : ℝ),
    centralRadius_tendsto_zero.eventually (gt_mem_nhds hR0),
    hgrow.eventually (eventually_ge_atTop (1 : ℝ)),
    (annulusBudget_tendsto_zero R).eventually (gt_mem_nhds hη)] with x hx hr hg hbudget
  intro t ht w v hrw hi hp hs hv z hz σ hσ
  have hx0 : 0 < x := by linarith
  have he := arithmetic_error_frequency_bound t x ht (by linarith) w hp hs
  have hehalf : 100000000/x ≤ (1/2 : ℝ) := (div_le_iff₀ hx0).mpr (by linarith)
  have hrpos : 0 < centralRadius x := Real.rpow_pos_of_pos hx0 _
  have hsmall : (30005*Real.exp (-4*w.re+4))*R ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_right (he.trans hehalf) hR0.le
    linarith
  have hbound := relative_actual_annulus_bound t x ht (by linarith) w v hrw hi hs hp hv z hz
    (centralRadius x) R σ hrpos hr.le hR hσ (by linarith) hsmall
  apply hbound.trans
  apply le_trans _ hbudget.le
  rw [← annulus_budget_identity R x hx0]
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2*Real.sqrt x)
  have hm := mul_le_mul_of_nonneg_right he (sq_nonneg R)
  linarith

end OperatorDerivativeRewrite.Foundation.RiemannSixthFarAnnulus
