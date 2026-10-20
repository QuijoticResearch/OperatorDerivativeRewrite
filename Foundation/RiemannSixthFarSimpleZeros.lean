import Foundation.RiemannSixthFarCosinePhase
import Foundation.RiemannSixthFarRealZeros
import Foundation.RiemannQuarticLocalCosineZeros
/-! Actual A6 far-strip reality and simplicity from the existing local
cosine-zero theorem, on the verified buffered analytic disks. -/
noncomputable section
open Set Metric Complex Filter
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthFarSimpleZeros
open RiemannSixthFarCosinePhase RiemannSixthFarAnalyticBranch RiemannSixthFarPairing
open RiemannSixthFarGaussianPhase RiemannEvenModelPhase
open RiemannQuarticFarCosinePhase (envelope phase phase_real envelope_ne_zero)

private theorem exp_two_le_nine : Real.exp (2 : ℝ) ≤ 9 := by
  calc
    _ = Real.exp (1 : ℝ)^2 := by simpa using Real.exp_nat_mul (1 : ℝ) 2
    _ ≤ 3^2 := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le 2
    _ = _ := by norm_num

private theorem cosh_le_nine (y : ℝ) (hy : |y| ≤ 2) : Real.cosh y ≤ 9 := by
  have h1 := (Real.exp_le_exp.mpr (abs_le.mp hy).2).trans exp_two_le_nine
  have h2 := (Real.exp_le_exp.mpr (by linarith [(abs_le.mp hy).1] : -y ≤ 2)).trans exp_two_le_nine
  rw [Real.cosh_eq]
  linarith

private theorem cos_lipschitz_two (a : ℝ) (u v : ℂ)
    (hu : u ∈ closedBall (a : ℂ) 2) (hv : v ∈ closedBall (a : ℂ) 2) :
    ‖Complex.cos v-Complex.cos u‖ ≤ 9*‖v-u‖ := by
  apply Convex.norm_image_sub_le_of_norm_deriv_le (fun y _ => Complex.differentiableAt_cos) ?_
    (convex_closedBall (a : ℂ) 2) hu hv
  intro y hy
  have hn : ‖y-(a : ℂ)‖ ≤ 2 := by simpa only [mem_closedBall,dist_eq_norm] using hy
  have him := (Complex.abs_im_le_norm (y-(a : ℂ))).trans hn
  simp only [Complex.sub_im,Complex.ofReal_im,sub_zero] at him
  rw [Complex.deriv_cos,norm_neg]
  exact (RiemannQuarticCosineLocalZeros.norm_sin_le_exp_abs_im y).trans
    ((Real.exp_le_exp.mpr him).trans exp_two_le_nine)

section FarData
variable (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x) (w : ℂ)
  (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
  (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x)
  (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
  (P : ℂ → ℂ) (hP0 : P (x : ℂ)=0)
  (hP : ∀ z ∈ ball (x : ℂ) 1, HasDerivAt P (phaseSlope t x ht hx w hr hi hp hs z) z)
include ht hx hr hi hp hs hP0 hP
local notation "B" => RiemannSixthFarAnalyticBranch.branch t x ht hx w hr hi hp hs
local notation "A₀" => modelGaussianAmplitude t (x : ℂ) (B (x : ℂ))
local notation "E" => envelope A₀ P
local notation "Φ" => phase A₀ P

theorem actual_real_simple_zero
    (herror : ∀ y : ℂ, ‖y-(x : ℂ)‖ < 1 →
      ‖RiemannEvenFlow.flow 3 t y/E y-Complex.cos (Φ y)‖ ≤ (1/1000000)*Real.cosh (Φ y).im)
    (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1/2) (hzero : RiemannEvenFlow.flow 3 t z=0) :
    z.im=0 ∧ deriv (RiemannEvenFlow.flow 3 t) z ≠ 0 := by
  let p := z.re
  let a := (Φ (p : ℂ)).re
  let s := w.re
  let L := fun q : ℂ => (p : ℂ)+(q-(a : ℂ))/(s : ℂ)
  let F := fun y : ℂ => RiemannEvenFlow.flow 3 t y/E y
  let f := fun q : ℂ => F (L q)
  let q₀ := (a : ℂ)+(s : ℂ)*(z-(p : ℂ))
  have hspos : 0 < s := by dsimp [s]; linarith
  have hsn : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hspos.ne'
  have hxpos : 0 < x := by linarith
  have hslarge : 120020 ≤ s := hr
  have hsmall : 1/s ≤ 1/1000 := (div_le_iff₀ hspos).mpr (by linarith)
  have hpcenter : ‖(p : ℂ)-(x : ℂ)‖ < 1/2 := by
    have h := (Complex.abs_re_le_norm (z-(x : ℂ))).trans_lt hz
    simpa only [Complex.sub_re,Complex.ofReal_re,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using h
  have hinside (y : ℂ) (hy : y ∈ closedBall (p : ℂ) (1/s)) : ‖y-(x : ℂ)‖ < 1 := by
    have hy' : ‖y-(p : ℂ)‖ ≤ 1/s := by simpa only [mem_closedBall,dist_eq_norm] using hy
    have h := norm_add_le (y-(p : ℂ)) ((p : ℂ)-(x : ℂ))
    rw [sub_add_sub_cancel] at h
    linarith
  have hLmem (q : ℂ) (hq : q ∈ closedBall (a : ℂ) 1) : L q ∈ closedBall (p : ℂ) (1/s) := by
    have hq' : ‖q-(a : ℂ)‖ ≤ 1 := by simpa only [mem_closedBall,dist_eq_norm] using hq
    rw [mem_closedBall,dist_eq_norm]
    dsimp [L]
    rw [add_sub_cancel_left,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hspos]
    exact div_le_div_of_nonneg_right hq' hspos.le
  have hphasep : Φ (p : ℂ)=(a : ℂ) := by
    apply Complex.ext
    · rfl
    · exact phase_real A₀ P p
  have hlinear (q : ℂ) (hq : q ∈ closedBall (a : ℂ) 1) : ‖Φ (L q)-q‖ ≤ 1/1000000 := by
    have hd : ∀ y ∈ closedBall (p : ℂ) (1/s),
        DifferentiableAt ℂ (fun y => Φ y-(s : ℂ)*y) y := by
      intro y hy
      exact (phase_analyticAt t x ht hx w hr hi hp hs P hP0 hP y (hinside y hy)).differentiableAt.sub
        ((hasDerivAt_id y).const_mul (s : ℂ)).differentiableAt
    have hb : ∀ y ∈ closedBall (p : ℂ) (1/s),
        ‖deriv (fun y => Φ y-(s : ℂ)*y) y‖ ≤ 513/x := by
      intro y hy
      have hd' : HasDerivAt (fun u => Φ u-(s : ℂ)*u) (deriv Φ y-(s : ℂ)) y := by
        convert ((phase_analyticAt t x ht hx w hr hi hp hs P hP0 hP y
          (hinside y hy)).differentiableAt.hasDerivAt).sub ((hasDerivAt_id y).const_mul (s : ℂ)) using 1
        · funext u; rfl
        · simp only [mul_one]
      rw [hd'.deriv]
      exact phase_deriv_model_bound t x ht hx w hr hi hp hs P hP0 hP y (hinside y hy)
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_closedBall (p : ℂ) (1/s))
      (mem_closedBall_self (by positivity)) (hLmem q hq)
    have hid : Φ (L q)-(s : ℂ)*L q-(Φ (p : ℂ)-(s : ℂ)*(p : ℂ))=Φ (L q)-q := by
      rw [hphasep]
      dsimp [L]
      field_simp [hsn] <;> ring
    rw [hid] at h
    have hm := mul_le_mul_of_nonneg_left (show ‖L q-(p : ℂ)‖ ≤ 1/s by
      simpa only [mem_closedBall,dist_eq_norm] using hLmem q hq) (by positivity : 0 ≤ 513/x)
    have hbound : (513/x)*(1/s) ≤ 1/1000000 := by
      rw [show (513/x)*(1/s)=513/(x*s) by ring]
      apply (div_le_iff₀ (mul_pos hxpos hspos)).mpr
      have hprod := mul_le_mul hx hslarge (by norm_num : (0 : ℝ) ≤ 120020) hxpos.le
      nlinarith
    exact h.trans (hm.trans hbound)
  have hf : ∀ q ∈ closedBall (a : ℂ) 1, DifferentiableAt ℂ f q := by
    intro q hq
    exact (normalized_flow_analyticAt t x ht hx w hr hi hp hs P hP0 hP (L q)
      (hinside (L q) (hLmem q hq))).differentiableAt.comp q (by dsimp [L]; fun_prop)
  have hconj : ∀ q, f (conj q)=conj (f q) := by
    intro q
    have hLc : L (conj q)=conj (L q) := by
      simp only [L,map_add,map_div₀,map_sub,Complex.conj_ofReal]
    dsimp only [f]
    rw [hLc]
    exact normalized_flow_conj t A₀ P (L q)
  have hclose : ∀ q ∈ closedBall (a : ℂ) 1, ‖f q-Complex.cos q‖ ≤ 1/1000 := by
    intro q hq
    have hlin := hlinear q hq
    have hqnorm : ‖q-(a : ℂ)‖ ≤ 1 := by simpa only [mem_closedBall,dist_eq_norm] using hq
    have hphi : Φ (L q) ∈ closedBall (a : ℂ) 2 := by
      have ht := norm_add_le (Φ (L q)-q) (q-(a : ℂ))
      rw [sub_add_sub_cancel] at ht
      rw [mem_closedBall,dist_eq_norm]
      linarith
    have him : |(Φ (L q)).im| ≤ 2 := by
      have h := (Complex.abs_im_le_norm (Φ (L q)-(a : ℂ))).trans
        (show ‖Φ (L q)-(a : ℂ)‖ ≤ 2 by simpa only [mem_closedBall,dist_eq_norm] using hphi)
      simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using h
    have hcos := cos_lipschitz_two a q (Φ (L q))
      (closedBall_subset_closedBall (by norm_num) hq) hphi
    have he := herror (L q) (hinside (L q) (hLmem q hq))
    have hcosh := cosh_le_nine (Φ (L q)).im him
    have htri := norm_add_le (F (L q)-Complex.cos (Φ (L q))) (Complex.cos (Φ (L q))-Complex.cos q)
    rw [sub_add_sub_cancel] at htri
    change ‖F (L q)-Complex.cos (Φ (L q))‖ ≤ _ at he
    change ‖F (L q)-Complex.cos q‖ ≤ _
    nlinarith
  have hLq : L q₀=z := by dsimp [L,q₀]; field_simp [hsn] <;> ring
  have hzeroF : f q₀=0 := by dsimp [f,F]; rw [hLq,hzero,zero_div]
  have hphasezero : |(Φ z).im| ≤ 2*(1/1000000) := by
    have he := herror z (by linarith)
    rw [hzero,zero_div,zero_sub,norm_neg] at he
    exact RiemannQuarticZeroStrip.small_cos_im (Φ z) (1/1000000) (by norm_num) (by norm_num) he
  have hgeom := phase_im_lower_bound t x ht hx w hr hi hp hs P hP0 hP z (by linarith)
  have hqsmall : q₀ ∈ closedBall (a : ℂ) (1/1000) := by
    have hzre : z-(p : ℂ)=(z.im : ℂ)*Complex.I := by apply Complex.ext <;> simp [p]
    have hqn : ‖q₀-(a : ℂ)‖=s*|z.im| := by
      dsimp [q₀]
      rw [add_sub_cancel_left,norm_mul,hzre,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos hspos,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
    rw [mem_closedBall,dist_eq_norm]
    rw [hqn]
    change s*|z.im| ≤ _ at hgeom
    nlinarith
  have hlocal := RiemannQuarticLocalCosineZeros.real_simple_zero f a hf hconj hclose q₀ hqsmall hzeroF
  have himq : q₀.im=s*z.im := by simp [q₀,Complex.mul_im]
  have hzreal : z.im=0 := by
    rw [himq] at hlocal
    exact (mul_eq_zero.mp hlocal.1).resolve_left hspos.ne'
  refine ⟨hzreal,?_⟩
  intro hbad
  have hFn : HasDerivAt (RiemannEvenFlow.flow 3 t) 0 z := by
    simpa only [hbad] using (RiemannEvenFlow.flow_differentiable 3 t z).hasDerivAt
  have hEn : E z ≠ 0 := by
    apply envelope_ne_zero
    exact modelGaussianAmplitude_ne_zero t x ht hx w (B (x : ℂ)) hr hi hp hs
      (by simpa only [mem_closedBall,dist_eq_norm] using
        (branch_spec t x ht hx w hr hi hp hs (x : ℂ) (by simp)).1) (x : ℂ)
  have hEd := (envelope_analyticAt t x ht hx w hr hi hp hs P hP0 hP z (by linarith)).differentiableAt.hasDerivAt
  have hF0 : HasDerivAt F 0 z := by
    convert hFn.div hEd hEn using 1 <;>
      simp only [hzero,zero_mul,mul_zero,sub_zero,zero_div]
  have hLd : HasDerivAt L (1/(s : ℂ)) q₀ := by
    exact (((hasDerivAt_id q₀).sub_const (a : ℂ)).div_const (s : ℂ)).const_add (p : ℂ)
  rw [← hLq] at hF0
  have hcomp := hF0.comp q₀ hLd
  have hfc : HasDerivAt f 0 q₀ := by
    convert hcomp using 1
    · funext y; rfl
    · simp only [zero_mul]
  exact hlocal.2 hfc.deriv

end FarData
theorem eventually_uniform_real_simple_zeros :
    ∀ᶠ x : ℝ in atTop, ∀ (t : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x) (w : ℂ)
      (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
      (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x) (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
      (z : ℂ), ‖z-(x : ℂ)‖ < 1/2 → RiemannEvenFlow.flow 3 t z=0 →
        z.im=0 ∧ deriv (RiemannEvenFlow.flow 3 t) z ≠ 0 := by
  filter_upwards [eventually_uniform_normalized_cosine_error (1/1000000) (by norm_num)] with x he
  intro t ht hx w hr hi hp hs z hz hzero
  obtain ⟨P,hP0,hP⟩ := exists_normalized_amplitude_phase t x ht hx w hr hi hp hs
  exact actual_real_simple_zero t x ht hx w hr hi hp hs P hP0 hP
    (he t ht hx w hr hi hp hs P hP0 hP) z hz hzero

theorem exists_uniform_actual_far_real_simple_disks :
    ∃ K : ℝ, 0 < K ∧ ∃ X : ℝ, ∀ t u x : ℝ,
      1 ≤ t → 120021 ≤ u → RiemannEvenRealSaddle.phaseSlope 3 t u = 0 →
      max X (K*RiemannQuarticTransitionSaddle.realScale u) ≤ x →
      ∀ z : ℂ, ‖z-(x : ℂ)‖ < 1/2 → RiemannEvenFlow.flow 3 t z=0 →
        z.im=0 ∧ deriv (RiemannEvenFlow.flow 3 t) z ≠ 0 := by
  obtain ⟨K,hK,hC⟩ := RiemannSixthUniformFarSaddles.exists_uniform_actual_far_frequency_disks
  obtain ⟨X,hX⟩ := eventually_atTop.mp eventually_uniform_real_simple_zeros
  refine ⟨K,hK,X,?_⟩
  intro t u x ht hu hstat hx
  obtain ⟨w,hxl,hr,hi,hp,hs,hroots⟩ := hC t u x ht hu hstat ((le_max_right _ _).trans hx)
  exact hX x ((le_max_left _ _).trans hx) t ht hxl w hr hi hp hs

theorem exists_uniform_actual_far_real_simple_strip :
    ∃ K : ℝ, 0 < K ∧ ∃ X : ℝ, ∀ t u : ℝ,
      1 ≤ t → 120021 ≤ u → RiemannEvenRealSaddle.phaseSlope 3 t u = 0 →
      ∀ z : ℂ, max X (K*RiemannQuarticTransitionSaddle.realScale u) ≤ z.re →
        |z.im| < 1/2 → RiemannEvenFlow.flow 3 t z=0 →
        z.im=0 ∧ deriv (RiemannEvenFlow.flow 3 t) z ≠ 0 := by
  obtain ⟨K,hK,X,hX⟩ := exists_uniform_actual_far_real_simple_disks
  refine ⟨K,hK,X,?_⟩
  intro t u ht hu hs z hx him hzero
  have hz : ‖z-(z.re : ℂ)‖ < 1/2 := by
    have he : z-(z.re : ℂ)=(z.im : ℂ)*Complex.I := by apply Complex.ext <;> simp
    rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
    exact him
  exact hX t u z.re ht hu hs hx z hz hzero

theorem eventually_far_strip_real_simple :
    ∀ᶠ t : ℝ in atTop, ∃ X : ℝ, ∀ z : ℂ, X ≤ z.re → |z.im| < 1/2 →
      RiemannEvenFlow.flow 3 t z=0 → z.im=0 ∧ deriv (RiemannEvenFlow.flow 3 t) z ≠ 0 := by
  obtain ⟨K,hK,X,hX⟩ := exists_uniform_actual_far_real_simple_strip
  filter_upwards [RiemannEvenRealSaddle.maxima_escape 3 (by norm_num) 120021 (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with t he ht
  obtain ⟨u,hu,hmax⟩ := RiemannEvenRealSaddle.exists_global_max 3 t
  have hlarge := he u hu hmax
  have hs := RiemannEvenRealSaddle.max_real_stationary 3 t u (by linarith) hmax
  exact ⟨max X (K*RiemannQuarticTransitionSaddle.realScale u),hX t u ht hlarge.le hs⟩

theorem eventually_arbitrarily_large_actual_simple_real_zero :
    ∀ᶠ t : ℝ in atTop, ∀ R : ℝ, ∃ y : ℝ, R < y ∧ RiemannEvenFlow.flow 3 t (y : ℂ)=0 ∧
      deriv (RiemannEvenFlow.flow 3 t) (y : ℂ) ≠ 0 := by
  filter_upwards [eventually_far_strip_real_simple,
    RiemannSixthFarRealZeros.eventually_arbitrarily_large_actual_real_zero] with t hstrip hreal
  obtain ⟨X,hX⟩ := hstrip
  intro R
  obtain ⟨y,hy,hzero⟩ := hreal (max X R)
  have hXy : X ≤ y := (le_max_left _ _).trans hy.le
  exact ⟨y,lt_of_le_of_lt (le_max_right _ _) hy,hzero,
    (hX (y : ℂ) (by simpa using hXy) (by norm_num) hzero).2⟩

theorem eventually_infinitely_many_actual_simple_real_zeros :
    ∀ᶠ t : ℝ in atTop, {y : ℝ | RiemannEvenFlow.flow 3 t (y : ℂ)=0 ∧
      deriv (RiemannEvenFlow.flow 3 t) (y : ℂ) ≠ 0}.Infinite := by
  filter_upwards [eventually_arbitrarily_large_actual_simple_real_zero] with t he
  apply Set.infinite_of_not_bddAbove
  rintro ⟨R,hR⟩
  obtain ⟨y,hy,hzero⟩ := he R
  exact (not_lt_of_ge (hR hzero)) hy

end OperatorDerivativeRewrite.Foundation.RiemannSixthFarSimpleZeros
