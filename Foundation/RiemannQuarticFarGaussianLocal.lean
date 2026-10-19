import Foundation.RiemannQuarticFarSignedIntegral
/-! Quantitative actual far-saddle comparison with a full complex Gaussian.
Leading-model linear mismatch at an actual saddle is retained explicitly.
Actual complementary contour tails and global zero control remain separate. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticFarGaussianLocal
open RiemannQuarticFarCorrection RiemannQuarticFarRemainder RiemannQuarticFarSignedIntegral
open RiemannQuarticFarModelSaddle RiemannQuarticSaddleTheta RiemannQuarticSaddleBranch
open RiemannQuarticFrequencyBranch

theorem exponential_cubic_remainder (u : ℂ) (hu : ‖u‖ ≤ 1/16) :
    ‖Complex.exp (4*u)-1-4*u-8*u^2‖ ≤ 128*‖u‖^3 := by
  have he := Complex.norm_exp_sub_sum_le_norm_mul_exp (4*u) 3
  have hsum : (∑ m ∈ Finset.range 3, (4*u)^m/(m.factorial : ℂ))=1+4*u+8*u^2 := by
    norm_num [Finset.sum_range_succ]
    ring
  rw [hsum] at he
  have hid : Complex.exp (4*u)-1-4*u-8*u^2=Complex.exp (4*u)-(1+4*u+8*u^2) := by ring
  rw [hid]
  apply he.trans
  have hnorm : ‖4*u‖ ≤ (1/4 : ℝ) := by rw [norm_mul,Complex.norm_ofNat]; linarith
  have hexp : Real.exp ‖4*u‖ ≤ 2 :=
    ((Real.exp_le_exp.mpr hnorm).trans RiemannQuarticSaddleNeighborhood.quarter_exp_bounds.2).trans (by norm_num)
  rw [norm_mul,Complex.norm_ofNat]
  have hm := mul_le_mul_of_nonneg_left hexp (pow_nonneg (by positivity : 0 ≤ ‖4*u‖) 3)
  rw [norm_mul,Complex.norm_ofNat] at hm
  nlinarith [pow_nonneg (norm_nonneg u) 3]

theorem corrected_exp_norm (t x : ℝ) (ht : 0 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (hp : 4*t*‖w‖^3+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x) :
    ‖Complex.exp (4*v)‖ ≤ 2*x := by
  have hx0 : 0 < x := by linarith
  have hE := model_exp_norm_le_frequency t x ht hx0 w hp hs
  have hq : 1/x ≤ (1/4 : ℝ) := (div_le_iff₀ hx0).mpr (by linarith)
  have hsmall : 4*‖v-w‖ ≤ 1 := by linarith
  have he := exp4_difference_bound w v hsmall
  have hm := mul_le_mul hE hv (norm_nonneg _) hx0.le
  have hcancel : x*(1/x)=1 := by field_simp
  have he8 : ‖Complex.exp (4*v)-Complex.exp (4*w)‖ ≤ 8 := by nlinarith
  have htri := norm_add_le (Complex.exp (4*v)-Complex.exp (4*w)) (Complex.exp (4*w))
  rw [sub_add_cancel] at htri
  linarith

theorem corrected_polynomial_scale (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 64 ≤ w.re) (hp : 4*t*‖w‖^3+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x) :
    t*(4*‖v‖+1) ≤ x := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 < x := by linarith
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

theorem leadingPhase_cubic_bound (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 64 ≤ w.re) (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (hp : 4*t*‖w‖^3+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x) (z u : ℂ) (hu : ‖u‖ ≤ 1/16) :
    ‖leadingPhase t z v u-(modelDerivative t v+Complex.I*z)*u-
      deriv (modelDerivative t) v*u^2/2‖ ≤ 2048*x*‖u‖^3 := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 ≤ x := by linarith
  have he := exponential_cubic_remainder u hu
  have hE := corrected_exp_norm t x ht0 hx w v hs hp hv
  have hP := corrected_polynomial_scale t x ht hx w v hr hp hv
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
  have hpoly : t*‖4*v+u‖ ≤ x := by
    have hm := mul_le_mul_of_nonneg_left (by linarith : ‖4*v+u‖ ≤ 4*‖v‖+1) ht0
    exact hm.trans hP
  have hpoly3 := mul_le_mul_of_nonneg_right hpoly (pow_nonneg (norm_nonneg u) 3)
  have hpe := mul_le_mul Real.pi_lt_four.le hE (norm_nonneg _) (by norm_num : (0 : ℝ)≤4)
  have hrem := mul_le_mul hpe he (norm_nonneg _) (by positivity : 0 ≤ 4*(2*x))
  nlinarith [pow_nonneg (norm_nonneg u) 3]


theorem model_gaussian_coefficient_pos (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (hp : 4*t*‖w‖^3+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x) :
    0 < (-(deriv (modelDerivative t) v)/2).re := by
  have h := horizontal_model_curvature t x ht hx w v hr hi hs hp hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at h
  simp only [Complex.div_ofNat_re,Complex.neg_re]
  have ht0 : 0 < t := by linarith
  have hr0 : 0 < w.re := by linarith
  have hp0 : 0 < t*w.re^3 := by positivity
  linarith

theorem quadratic_norm_le_one (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (hp : 4*t*‖w‖^3+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x) (s : ℝ) :
    ‖Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)‖ ≤ 1 := by
  have h := GaussianOscillatoryTail.gaussian_norm_le_one (-(deriv (modelDerivative t) v)/2)
    (model_gaussian_coefficient_pos t x ht hx w v hr hi hs hp hv).le s
  convert h using 1 <;> congr 1 <;> ring

theorem leadingPhase_quadratic_bound (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (hp : 4*t*‖w‖^3+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hstat : complexSlope t v= -(Complex.I*z)) (s : ℝ) (hsr : |s| ≤ 1/16) :
    ‖leadingPhase t z v (s : ℂ)-deriv (modelDerivative t) v*(s : ℂ)^2/2‖ ≤
      (30005*Real.exp (-4*w.re+4))*|s|+2048*x*|s|^3 := by
  have hc := leadingPhase_cubic_bound t x ht hx w v hr hs hp hv z (s : ℂ) (by simpa using hsr)
  simp only [Complex.norm_real,Real.norm_eq_abs] at hc
  have he := horizontal_neighbor_error t x ht hx w v (by linarith) hi hs hp hv 0 (by norm_num)
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

theorem leading_quadratic_weight_error (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (hp : 4*t*‖w‖^3+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hstat : complexSlope t v= -(Complex.I*z)) (s : ℝ) (hsr : |s| ≤ 1/16)
    (hsmall : (30005*Real.exp (-4*w.re+4))*|s|+2048*x*|s|^3 ≤ 1) :
    ‖Complex.exp (leadingPhase t z v (s : ℂ))-Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)‖ ≤
      2*((30005*Real.exp (-4*w.re+4))*|s|+2048*x*|s|^3) := by
  let P := leadingPhase t z v (s : ℂ)
  let Q := deriv (modelDerivative t) v*(s : ℂ)^2/2
  have he := Complex.norm_exp_sub_one_le
    ((leadingPhase_quadratic_bound t x ht hx w v hr hi hs hp hv z hstat s hsr).trans hsmall)
  have hQ := quadratic_norm_le_one t x ht hx w v hr hi hs hp hv s
  have hid : Complex.exp P-Complex.exp Q=Complex.exp Q*(Complex.exp (P-Q)-1) := by
    rw [mul_sub,mul_one,← Complex.exp_add]
    congr 1
    ring
  change ‖Complex.exp P-Complex.exp Q‖ ≤ _
  rw [hid,norm_mul]
  have hpq := leadingPhase_quadratic_bound t x ht hx w v hr hi hs hp hv z hstat s hsr
  change ‖Complex.exp (P-Q)-1‖ ≤ 2*‖P-Q‖ at he
  change ‖Complex.exp Q‖ ≤ 1 at hQ
  have hmul := mul_le_mul_of_nonneg_right hQ (norm_nonneg (Complex.exp (P-Q)-1))
  nlinarith

theorem leading_local_quadratic_error (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (hp : 4*t*‖w‖^3+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hstat : complexSlope t v= -(Complex.I*z)) (r : ℝ) (hr0 : 0 ≤ r) (hrr : r < 1/16)
    (hsmall : (30005*Real.exp (-4*w.re+4))*r+2048*x*r^3 ≤ 1) :
    ‖(∫ s : ℝ in -r..r, Complex.exp (leadingPhase t z v (s : ℂ)))-
      (∫ s : ℝ in -r..r, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2))‖ ≤
      4*(30005*Real.exp (-4*w.re+4))*r^2+8192*x*r^4 := by
  have hf : IntervalIntegrable (fun s : ℝ => Complex.exp (leadingPhase t z v (s : ℂ))) volume (-r) r := by
    apply Continuous.intervalIntegrable
    unfold leadingPhase
    fun_prop
  have hg : IntervalIntegrable (fun s : ℝ => Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)) volume (-r) r :=
    (by fun_prop : Continuous (fun s : ℝ => Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2))).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub hf hg]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := -r) (b := r)
    (f := fun s : ℝ => Complex.exp (leadingPhase t z v (s : ℂ))-Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2))
    (C := 2*((30005*Real.exp (-4*w.re+4))*r+2048*x*r^3)) (fun s hsi => ?_)
  · rw [show r-(-r)=2*r by ring,abs_of_nonneg (by positivity : 0 ≤ 2*r)] at hb
    convert hb using 1 <;> ring
  · rw [uIoc_of_le (by linarith : -r ≤ r)] at hsi
    have habs : |s| ≤ r := abs_le.mpr ⟨hsi.1.le,hsi.2⟩
    have hpow := pow_le_pow_left₀ (abs_nonneg s) habs 3
    have h1 := mul_le_mul_of_nonneg_left habs (by positivity : 0 ≤ 30005*Real.exp (-4*w.re+4))
    have h2 := mul_le_mul_of_nonneg_left hpow (by linarith : 0 ≤ 2048*x)
    have hsm : (30005*Real.exp (-4*w.re+4))*|s|+2048*x*|s|^3 ≤ 1 := by linarith
    exact (leading_quadratic_weight_error t x ht hx w v hr hi hs hp hv z hstat s
      (habs.trans hrr.le) hsm).trans (by linarith)


theorem actual_local_quadratic_error (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (hp : 4*t*‖w‖^3+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hstat : complexSlope t v= -(Complex.I*z)) (r : ℝ) (hr0 : 0 ≤ r) (hrr : r < 1/16)
    (hsmall : (30005*Real.exp (-4*w.re+4))*r+2048*x*r^3 ≤ 1) :
    ‖(∫ s : ℝ in -r..r, saddleWeight t z (v+(s : ℂ)))-
      saddleWeight t z v*(∫ s : ℝ in -r..r, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2))‖ ≤
      (16*(30005*Real.exp (-4*w.re+4))*r^2+8192*x*r^4)*‖saddleWeight t z v‖ := by
  have hx0 : 0 ≤ x := by linarith
  have heps : (30005*Real.exp (-4*w.re+4))*r ≤ 1 := by
    nlinarith [mul_nonneg hx0 (pow_nonneg hr0 3)]
  have ha := signed_local_leading_error t x ht hx w v hr hi hs hp hv z hstat r hr0 hrr heps
  have hl := leading_local_quadratic_error t x ht hx w v hr hi hs hp hv z hstat r hr0 hrr hsmall
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

theorem actual_local_full_gaussian_error (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (hp : 4*t*‖w‖^3+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hstat : complexSlope t v= -(Complex.I*z)) (r : ℝ) (hr0 : 0 < r) (hrr : r < 1/16)
    (hsmall : (30005*Real.exp (-4*w.re+4))*r+2048*x*r^3 ≤ 1) :
    ‖(∫ s : ℝ in -r..r, saddleWeight t z (v+(s : ℂ)))-
      saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2))‖ ≤
      ‖saddleWeight t z v‖*(16*(30005*Real.exp (-4*w.re+4))*r^2+8192*x*r^4+
        2/(‖-(deriv (modelDerivative t) v)/2‖*r)) := by
  let b := -(deriv (modelDerivative t) v)/2
  have hb : 0 < b.re := model_gaussian_coefficient_pos t x ht hx w v hr hi hs hp hv
  have htail := GaussianOscillatoryTail.full_minus_truncated_bound b hb r hr0
  have hfun : (fun s : ℝ => Complex.exp (-b*(s : ℂ)^2))=
      (fun s : ℝ => Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)) := by
    funext s
    congr 1
    dsimp [b]
    ring
  rw [hfun] at htail
  have hl := actual_local_quadratic_error t x ht hx w v hr hi hs hp hv z hstat r hr0.le hrr hsmall
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

theorem full_gaussian_formula (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (hp : 4*t*‖w‖^3+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x) :
    (∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2))=
      ((Real.pi : ℂ)/(-(deriv (modelDerivative t) v)/2))^(1/2 : ℂ) := by
  have h := integral_gaussian_complex (model_gaussian_coefficient_pos t x ht hx w v hr hi hs hp hv)
  convert h using 1 <;> congr 1 <;> ring

end OperatorDerivativeRewrite.Foundation.RiemannQuarticFarGaussianLocal
