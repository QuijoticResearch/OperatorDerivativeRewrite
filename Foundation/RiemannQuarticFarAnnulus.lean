import Foundation.RiemannQuarticFarGaussianLimit
/-! Nonstationarity on horizontal annuli at actual far Xi saddles.
The model slope is used only after retaining its actual-saddle mismatch.
The signed actual annuli have vanishing Gaussian-relative norm; farther tails remain open. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticFarAnnulus
open RiemannQuarticFarGaussianLocal RiemannQuarticFarGaussianLimit
open RiemannQuarticFarCorrection RiemannQuarticFarRemainder RiemannQuarticFarSignedIntegral
open RiemannQuarticFarModelSaddle RiemannQuarticSaddleTheta RiemannQuarticSaddleBranch
open RiemannQuarticFrequencyBranch

theorem exponential_quadratic_remainder (u : ℂ) (hu : ‖u‖ ≤ 1/16) :
    ‖Complex.exp (4*u)-1-4*u‖ ≤ 32*‖u‖^2 := by
  have he := Complex.norm_exp_sub_sum_le_norm_mul_exp (4*u) 2
  have hsum : (∑ m ∈ Finset.range 2, (4*u)^m/(m.factorial : ℂ))=1+4*u := by
    norm_num [Finset.sum_range_succ]
  rw [hsum] at he
  have hid : Complex.exp (4*u)-1-4*u=Complex.exp (4*u)-(1+4*u) := by ring
  rw [hid]
  apply he.trans
  have hn : ‖4*u‖ ≤ (1/4 : ℝ) := by rw [norm_mul,Complex.norm_ofNat]; linarith
  have hx : Real.exp ‖4*u‖ ≤ 2 :=
    ((Real.exp_le_exp.mpr hn).trans RiemannQuarticSaddleNeighborhood.quarter_exp_bounds.2).trans (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hx (sq_nonneg ‖4*u‖)
  rw [norm_mul,Complex.norm_ofNat] at hm ⊢
  norm_num at *
  nlinarith

theorem model_slope_quadratic_remainder (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x)
    (w v : ℂ) (hr : 64 ≤ w.re)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (hp : 4*t*‖w‖^3+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x) (u : ℂ) (hu : ‖u‖ ≤ 1/16) :
    ‖modelDerivative t (v+u)-modelDerivative t v-deriv (modelDerivative t) v*u‖ ≤
      2048*x*‖u‖^2 := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 ≤ x := by linarith
  have he := exponential_quadratic_remainder u hu
  have hE := corrected_exp_norm t x ht0 hx w v hs hp hv
  have hP := corrected_polynomial_scale t x ht hx w v hr hp hv
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
  have hpoly : t*‖12*v+4*u‖ ≤ 4*x := by
    have hm := mul_le_mul_of_nonneg_left hadd ht0
    nlinarith
  have hpoly2 := mul_le_mul_of_nonneg_right hpoly (sq_nonneg ‖u‖)
  have hpe := mul_le_mul Real.pi_lt_four.le hE (norm_nonneg _) (by norm_num : (0 : ℝ)≤4)
  have hrem := mul_le_mul hpe he (norm_nonneg _) (by positivity : 0 ≤ 4*(2*x))
  nlinarith [sq_nonneg ‖u‖]

theorem annulus_slope_lower (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x)
    (w v : ℂ) (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hz : complexSlope t v= -(Complex.I*z))
    (s : ℝ) (hsr : |s| ≤ 1/8192)
    (heps : 30005*Real.exp (-4*w.re+4) ≤ x*|s|/2) :
    x*|s| ≤ ‖modelDerivative t (v+(s : ℂ))+Complex.I*z‖ := by
  have ht0 : 0 ≤ t := by linarith
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hmul := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 4*t*‖w‖^3+9 ≤ x := by nlinarith [pow_nonneg (norm_nonneg w) 3]
  have hn := (gaussian_coefficient_norm_bounds t x ht hx w v hp hs hv).1
  rw [norm_div,norm_neg,Complex.norm_ofNat] at hn
  have he := horizontal_neighbor_error t x ht (by linarith) w v (by linarith) hi hs hp0 hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at he
  have hc : ‖modelDerivative t v+Complex.I*z‖ ≤ 30005*Real.exp (-4*w.re+4) := by
    have hid : modelDerivative t v+Complex.I*z= -(complexSlope t v-modelDerivative t v) := by rw [hz]; ring
    rw [hid,norm_neg]
    exact he
  have hq := model_slope_quadratic_remainder t x ht (by linarith) w v hr hs hp0 hv (s : ℂ)
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
  have hs2 := mul_le_mul_of_nonneg_left hsr (by positivity : 0 ≤ 2048*x*|s|)
  nlinarith [abs_nonneg s]


theorem annulus_slope_derivative_upper (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x)
    (w v : ℂ) (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (s : ℝ) (hsr : |s| ≤ 1/8192) :
    ‖deriv (modelDerivative t) (v+(s : ℂ))‖ ≤ 512*x := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 < x := by linarith
  let M := ‖w‖+1
  have hM : 1 ≤ M := by dsimp [M]; linarith [norm_nonneg w]
  have hM0 : 0 ≤ M := by linarith
  have hM23 : M^2 ≤ M^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hM) (sq_nonneg M)]
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hmul := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 4*t*‖w‖^3+9 ≤ x := by nlinarith [pow_nonneg (norm_nonneg w) 3]
  have hE := corrected_exp_norm t x ht0 (by linarith) w v hs hp0 hv
  have hv1 : ‖v-w‖ ≤ 1 := hv.trans ((div_le_iff₀ hx0).mpr (by linarith))
  have htri := norm_add_le (v-w) w
  rw [sub_add_cancel] at htri
  have hvM : ‖v‖ ≤ M := by dsimp [M]; linarith
  have hvs := norm_add_le v (s : ℂ)
  simp only [Complex.norm_real,Real.norm_eq_abs] at hvs
  have hq : ‖v+(s : ℂ)‖ ≤ 2*M := by linarith
  have hq2 := pow_le_pow_left₀ (norm_nonneg (v+(s : ℂ))) hq 2
  have hpoly : t*‖v+(s : ℂ)‖^2 ≤ x := by
    have hm := mul_le_mul_of_nonneg_left hq2 ht0
    have hm2 := mul_le_mul_of_nonneg_left hM23 ht0
    change 100*(t*M^3+1) ≤ x at hp
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
  have hEq : ‖Complex.exp (4*(v+(s : ℂ)))‖ ≤ 4*x := by
    rw [heq,norm_mul]
    have hm := mul_le_mul hE hexp (norm_nonneg _) (by positivity : 0 ≤ 2*x)
    nlinarith
  rw [(modelDerivative_hasDerivAt t _).deriv]
  have hn := norm_sub_le (12*(t : ℂ)*(v+(s : ℂ))^2)
    (16*(Real.pi : ℂ)*Complex.exp (4*(v+(s : ℂ))))
  simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ht0,abs_of_pos Real.pi_pos] at hn
  have hm := mul_le_mul Real.pi_lt_four.le hEq (norm_nonneg _) (by norm_num : (0 : ℝ)≤4)
  nlinarith


/-- Finite signed integration by parts, retaining the inverse-square gain. -/
theorem finite_nonstationary_bound (E H K : ℝ → ℂ) (x a b : ℝ)
    (hx : 0 < x) (ha : 0 < a) (hab : a ≤ b)
    (hE : ∀ s ∈ Icc a b, HasDerivAt E (H s*E s) s)
    (hH : ∀ s ∈ Icc a b, HasDerivAt H (K s) s)
    (hK : ContinuousOn K (Icc a b))
    (hEn : ∀ s ∈ Icc a b, ‖E s‖ ≤ 3)
    (hHn : ∀ s ∈ Icc a b, x*s ≤ ‖H s‖)
    (hKn : ∀ s ∈ Icc a b, ‖K s‖ ≤ 512*x) :
    ‖∫ s : ℝ in a..b, E s‖ ≤ 1542/(x*a) := by
  have hspos (s : ℝ) (hs : s ∈ Icc a b) : 0 < s := ha.trans_le hs.1
  have hH0 (s : ℝ) (hs : s ∈ Icc a b) : H s ≠ 0 :=
    norm_pos_iff.mp ((mul_pos hx (hspos s hs)).trans_le (hHn s hs))
  have hEc : ContinuousOn E (Icc a b) := fun s hs => (hE s hs).continuousAt.continuousWithinAt
  have hHc : ContinuousOn H (Icc a b) := fun s hs => (hH s hs).continuousAt.continuousWithinAt
  let J := fun s : ℝ => E s*K s/(H s)^2
  have hJ : ContinuousOn J (Icc a b) := (hEc.mul hK).div (hHc.pow 2)
    (fun s hs => pow_ne_zero 2 (hH0 s hs))
  have hd (s : ℝ) (hs : s ∈ uIcc a b) :
      HasDerivAt (fun s => E s/H s) (E s-J s) s := by
    rw [uIcc_of_le hab] at hs
    have h := (hE s hs).div (hH s hs) (hH0 s hs)
    convert h using 1
    dsimp [J]
    field_simp [hH0 s hs]
  have hi : IntervalIntegrable (fun s => E s-J s) volume a b := by
    rw [← uIcc_of_le hab] at hEc hJ
    exact (hEc.sub hJ).intervalIntegrable
  have hid := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  have hEi : IntervalIntegrable E volume a b := by
    exact (hEc.mono (by rw [uIcc_of_le hab])).intervalIntegrable
  have hJi : IntervalIntegrable J volume a b := by
    exact (hJ.mono (by rw [uIcc_of_le hab])).intervalIntegrable
  rw [intervalIntegral.integral_sub hEi hJi] at hid
  have hgn (s : ℝ) (hs : s ∈ Icc a b) : ‖J s‖ ≤ (1536/x)*(s^2)⁻¹ := by
    have hs0 := hspos s hs
    have hden : 0 < ‖H s‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (hH0 s hs))
    have hl := pow_le_pow_left₀ (mul_pos hx hs0).le (hHn s hs) 2
    have hm := mul_le_mul (hEn s hs) (hKn s hs) (norm_nonneg _) (by norm_num : (0 : ℝ)≤3)
    dsimp [J]
    rw [norm_div,norm_mul,norm_pow]
    calc
      _ ≤ (3*(512*x))/(x*s)^2 := div_le_div₀ (by positivity) hm (by positivity) hl
      _ = _ := by field_simp; ring
  have hgc : ContinuousOn (fun s : ℝ => (1536/x)*(s^2)⁻¹) (Icc a b) := by
    exact continuousOn_const.mul ((continuousOn_id.pow 2).inv₀ (fun s hs => pow_ne_zero 2 (hspos s hs).ne'))
  have hgi : IntervalIntegrable (fun s : ℝ => (1536/x)*(s^2)⁻¹) volume a b :=
    (hgc.mono (by rw [uIcc_of_le hab])).intervalIntegrable
  have hjb := intervalIntegral.norm_integral_le_of_norm_le hab
    (Filter.Eventually.of_forall (fun s hs => hgn s ⟨hs.1.le,hs.2⟩)) hgi
  have hgder (s : ℝ) (hs : s ∈ uIcc a b) :
      HasDerivAt (fun s : ℝ => -(1536/x)/s) ((1536/x)*(s^2)⁻¹) s := by
    rw [uIcc_of_le hab] at hs
    convert (hasDerivAt_const s (-(1536/x))).div (hasDerivAt_id s) (hspos s hs).ne' using 1
    · funext y; rfl
    · simp only [id_eq]
      ring
  have hgint := intervalIntegral.integral_eq_sub_of_hasDerivAt hgder hgi
  rw [hgint] at hjb
  simp only [neg_div,sub_neg_eq_add] at hjb
  have hboundary (s : ℝ) (hs : s ∈ Icc a b) : ‖E s/H s‖ ≤ 3/(x*a) := by
    rw [norm_div]
    apply div_le_div₀ (by norm_num) (hEn s hs) (mul_pos hx ha)
    exact (mul_le_mul_of_nonneg_left hs.1 hx.le).trans (hHn s hs)
  have hb := hboundary b ⟨hab,le_rfl⟩
  have ha' := hboundary a ⟨le_rfl,hab⟩
  have ht := norm_add_le (E b/H b-E a/H a) (∫ s : ℝ in a..b, J s)
  have hsub := norm_sub_le (E b/H b) (E a/H a)
  have heq : (∫ s : ℝ in a..b, E s)=E b/H b-E a/H a+(∫ s : ℝ in a..b, J s) := by
    linear_combination hid
  rw [heq]
  have hb0 : 0 < b := ha.trans_le hab
  have hc0 : 0 ≤ (1536/x)/b := by positivity
  have hc : (1536/x)/a=1536/(x*a) := by field_simp
  have hc' : 3/(x*a)+3/(x*a)+1536/(x*a)=1542/(x*a) := by ring
  linarith


theorem signed_model_annulus_bound (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x)
    (w v : ℂ) (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hz : complexSlope t v= -(Complex.I*z))
    (r R σ : ℝ) (hr0 : 0 < r) (hrR : r ≤ R) (hR : R ≤ 1/8192) (hσ : |σ|=1)
    (heps : 30005*Real.exp (-4*w.re+4) ≤ x*r/2)
    (hsmall : (30005*Real.exp (-4*w.re+4))*R ≤ 1) :
    ‖∫ s : ℝ in r..R, Complex.exp (leadingPhase t z v ((σ*s : ℝ) : ℂ))‖ ≤ 1542/(x*r) := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 < x := by linarith
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hmul := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 4*t*‖w‖^3+9 ≤ x := by nlinarith [pow_nonneg (norm_nonneg w) 3]
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
  apply finite_nonstationary_bound E H K x r R hx0 hr0 hrR
    (fun s _ => hEs s) (fun s _ => hHs s)
  · dsimp [K]
    simp_rw [(modelDerivative_hasDerivAt t _).deriv]
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
    (w v : ℂ) (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hz : complexSlope t v= -(Complex.I*z))
    (r R σ : ℝ) (hr0 : 0 < r) (hrR : r ≤ R) (hR : R ≤ 1/8192) (hσ : |σ|=1)
    (heps : 30005*Real.exp (-4*w.re+4) ≤ x*r/2)
    (hsmall : (30005*Real.exp (-4*w.re+4))*R ≤ 1) :
    ‖∫ s : ℝ in r..R, saddleWeight t z (v+((σ*s : ℝ) : ℂ))‖ ≤
      ‖saddleWeight t z v‖*(1542/(x*r)+180030*Real.exp (-4*w.re+4)*R^2) := by
  have ht0 : 0 ≤ t := by linarith
  have hR0 : 0 < R := hr0.trans_le hrR
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hmul := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 4*t*‖w‖^3+9 ≤ x := by nlinarith [pow_nonneg (norm_nonneg w) 3]
  let A := fun s : ℝ => saddleWeight t z (v+((σ*s : ℝ) : ℂ))
  let E := fun s : ℝ => Complex.exp (leadingPhase t z v ((σ*s : ℝ) : ℂ))
  let W := saddleWeight t z v
  have habs (s : ℝ) (h : s ∈ Icc r R) : |σ*s|=s := by
    rw [abs_mul,hσ,one_mul,abs_of_pos (hr0.trans_le h.1)]
  have hEc : Continuous E := by dsimp [E,leadingPhase]; fun_prop
  have hAc : ContinuousOn A (Icc r R) := by
    intro s h
    have hsr : |σ*s| ≤ 1/16 := by rw [habs s h]; linarith [h.2]
    have hd := horizontal_neighbor_domain t x ht (by linarith) w v (by linarith) hi hs hp0 hv (σ*s) hsr
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
    (w v : ℂ) (hr : 64 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hz : complexSlope t v= -(Complex.I*z))
    (r R σ : ℝ) (hr0 : 0 < r) (hrR : r ≤ R) (hR : R ≤ 1/8192) (hσ : |σ|=1)
    (heps : 30005*Real.exp (-4*w.re+4) ≤ x*r/2)
    (hsmall : (30005*Real.exp (-4*w.re+4))*R ≤ 1) :
    ‖(∫ s : ℝ in r..R, saddleWeight t z (v+((σ*s : ℝ) : ℂ)))/
      (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤
      2*Real.sqrt x*(1542/(x*r)+180030*Real.exp (-4*w.re+4)*R^2) := by
  have ht0 : 0 ≤ t := by linarith
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hmul := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 4*t*‖w‖^3+9 ≤ x := by nlinarith [pow_nonneg (norm_nonneg w) 3]
  have he := signed_actual_annulus_bound t x ht hx w v hr hi hs hp hv z hz r R σ hr0 hrR hR hσ heps hsmall
  let W := saddleWeight t z v
  let G := ∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)
  let B := 1542/(x*r)+180030*Real.exp (-4*w.re+4)*R^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hnormal := gaussian_normalization_lower t x ht hx w v hr hi hp hs hv
  change 1 ≤ 2*Real.sqrt x*‖G‖ at hnormal
  have hG : G ≠ 0 := by intro h; norm_num [h] at hnormal
  have hd := horizontal_neighbor_domain t x ht (by linarith) w v (by linarith) hi hs hp0 hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hd
  have hW : W ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _)
    (RiemannThetaComplexKernel.kernel_ne_zero v hd.1 hd.2.1)
  change ‖(∫ s : ℝ in r..R, saddleWeight t z (v+((σ*s : ℝ) : ℂ)))/(W*G)‖ ≤ 2*Real.sqrt x*B
  rw [norm_div,norm_mul]
  apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hW) (norm_pos_iff.mpr hG))).mpr
  have hm := mul_le_mul_of_nonneg_left hnormal (mul_nonneg (norm_nonneg W) hB)
  change ‖(∫ s : ℝ in r..R, saddleWeight t z (v+((σ*s : ℝ) : ℂ)))‖ ≤
    (2*Real.sqrt x*B)*(‖W‖*‖G‖)
  change ‖(∫ s : ℝ in r..R, saddleWeight t z (v+((σ*s : ℝ) : ℂ)))‖ ≤ ‖W‖*B at he
  nlinarith


open RiemannQuarticErrorLimits

def annulusBudget (R x : ℝ) : ℝ :=
  3084*x^(-1/16 : ℝ)+1200000000*R^2*x^(-1/2 : ℝ)

theorem annulusBudget_tendsto_zero (R : ℝ) : Tendsto (annulusBudget R) atTop (nhds 0) := by
  change Tendsto (fun x : ℝ => 3084*x^(-1/16 : ℝ)+1200000000*R^2*x^(-1/2 : ℝ)) atTop (nhds 0)
  have h1 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/16)).const_mul (3084 : ℝ)
  have h2 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/2)).const_mul (1200000000*R^2)
  simpa only [mul_zero,zero_add,neg_div] using h1.add h2

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

theorem eventually_uniform_relative_annulus (R η : ℝ) (hR0 : 0 < R)
    (hR : R ≤ 1/8192) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, 1 ≤ t → ∀ w v : ℂ,
      64 ≤ w.re → |w.im| ≤ 1/2 → 100*(t*(‖w‖+1)^3+1) ≤ x →
      modelDerivative t w= -(Complex.I*(x : ℂ)) → ‖v-w‖ ≤ 1/x →
      ∀ z : ℂ, complexSlope t v= -(Complex.I*z) → ∀ σ : ℝ, |σ|=1 →
      ‖(∫ s : ℝ in centralRadius x..R, saddleWeight t z (v+((σ*s : ℝ) : ℂ)))/
        (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤ η := by
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

end OperatorDerivativeRewrite.Foundation.RiemannQuarticFarAnnulus
