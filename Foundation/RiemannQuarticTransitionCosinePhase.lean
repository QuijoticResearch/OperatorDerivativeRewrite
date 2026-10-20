import Foundation.RiemannQuarticTransitionComplexPairing
import Foundation.RiemannQuarticFarCosinePhase
/-! Analytic paired cosine phases on actual bounded-transition branches.
The full signed contour approximation includes its vertical endpoint error. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticTransitionCosinePhase
open RiemannQuarticTransitionAnalyticBranch RiemannQuarticTransitionGaussianPhase
open RiemannQuarticFarCosinePhase (envelope phase pair_identity pair_norm_identity
  envelope_ne_zero phase_conj)
open RiemannQuarticFarPairing RiemannQuarticTransitionComplexPairing
open RiemannQuarticSaddleTheta RiemannQuarticSaddleBranch

private theorem conjugate_disk (x r : ℝ) (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    ‖conj z-(x : ℂ)‖ < r := by
  have he : conj z-(x : ℂ)=conj (z-(x : ℂ)) := by simp
  rw [he,norm_conj]
  exact hz

section Scaled
variable (t K x r : ℝ) (w : ℂ)
  (ht : 1 ≤ t) (hK : 8 ≤ K) (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
  (hnorm : ‖w‖ ≤ 2*w.re) (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
  (hE : ‖Complex.exp (4*w)‖ ≤ K)
  (hsmall : (30005*Real.exp (-w.re))*K ≤ t*w.re^3/4)
  (hrpos : 0 < r) (hradius : r ≤ t*w.re^3/K)
  (P : ℂ → ℂ) (hP0 : P (x : ℂ)=0)
  (hP : ∀ z ∈ ball (x : ℂ) r, HasDerivAt P (phaseSlope t K x r w ht hK hr hi hnorm hs hE hsmall hradius z) z)
include ht hK hr hi hnorm hs hE hsmall hrpos hradius hP0 hP
local notation "B" => RiemannQuarticTransitionAnalyticBranch.branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius
local notation "A₀" => modelGaussianAmplitude t (x : ℂ) (B (x : ℂ))

private theorem center_ne_zero : A₀ ≠ 0 :=
  mul_ne_zero (actual_weight_ne_zero t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius (x : ℂ) (by simp; positivity))
    (gaussian_ne_zero t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius (x : ℂ) (by simp; positivity))

private theorem reflected_hasDerivAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    HasDerivAt (fun y => conj (P (conj y))) (conj (phaseSlope t K x r w ht hK hr hi hnorm hs hE hsmall hradius (conj z))) z := by
  have hz' : conj z ∈ ball (x : ℂ) r := by
    simpa only [mem_ball,dist_eq_norm] using conjugate_disk x r z hz
  have h := (hP (conj z) hz').conj_conj
  simpa only [Function.comp_def,Complex.conj_conj] using h

theorem actual_pair_identity (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    (modelGaussianAmplitude t z (B z)+conj (modelGaussianAmplitude t (conj z) (B (conj z))))/2=
      envelope A₀ P z*Complex.cos (phase A₀ P z) := by
  rw [amplitude_eq_exp_phase t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius P hP0 hP z hz,
    amplitude_eq_exp_phase t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius P hP0 hP (conj z) (conjugate_disk x r z hz),
    map_mul,← Complex.exp_conj]
  exact pair_identity A₀ P z

theorem actual_pair_norm_identity (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    ‖modelGaussianAmplitude t z (B z)‖+‖modelGaussianAmplitude t (conj z) (B (conj z))‖=
      2*‖envelope A₀ P z‖*Real.cosh (phase A₀ P z).im := by
  rw [amplitude_eq_exp_phase t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius P hP0 hP z hz,
    amplitude_eq_exp_phase t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius P hP0 hP (conj z) (conjugate_disk x r z hz)]
  simpa only [Complex.exp_conj,← map_mul,norm_conj] using pair_norm_identity A₀ P z

theorem phase_hasDerivAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    HasDerivAt (phase A₀ P)
      ((phaseSlope t K x r w ht hK hr hi hnorm hs hE hsmall hradius z-conj (phaseSlope t K x r w ht hK hr hi hnorm hs hE hsmall hradius (conj z)))/
        (2*Complex.I)) z := by
  have hz' : z ∈ ball (x : ℂ) r := by simpa only [mem_ball,dist_eq_norm] using hz
  have h := (hasDerivAt_const z ((A₀).arg : ℂ)).add
    (((hP z hz').sub (reflected_hasDerivAt t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius P hP0 hP z hz)).div_const (2*Complex.I))
  convert h using 1
  · funext y
    rfl
  · simp only [zero_add]

theorem envelope_analyticAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) : AnalyticAt ℂ (envelope A₀ P) z := by
  have hd : DifferentiableOn ℂ (envelope A₀ P) (ball (x : ℂ) r) := by
    intro y hy
    have hy' : ‖y-(x : ℂ)‖ < r := by simpa only [mem_ball,dist_eq_norm] using hy
    have h := ((((hP y hy).add (reflected_hasDerivAt t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius P hP0 hP y hy')).div_const
      (2 : ℂ)).cexp.const_mul (‖A₀‖ : ℂ)).differentiableAt
    exact h.differentiableWithinAt
  exact hd.analyticAt (isOpen_ball.mem_nhds (by simpa only [mem_ball,dist_eq_norm] using hz))

theorem phase_analyticAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) : AnalyticAt ℂ (phase A₀ P) z := by
  have hd : DifferentiableOn ℂ (phase A₀ P) (ball (x : ℂ) r) := by
    intro y hy
    exact (phase_hasDerivAt t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius P hP0 hP y
      (by simpa only [mem_ball,dist_eq_norm] using hy)).differentiableAt.differentiableWithinAt
  exact hd.analyticAt (isOpen_ball.mem_nhds (by simpa only [mem_ball,dist_eq_norm] using hz))

theorem normalized_flow_analyticAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    AnalyticAt ℂ (fun y => RiemannQuarticFlow.flow t y/envelope A₀ P y) z :=
  ((RiemannQuarticFlow.flow_differentiable t).analyticAt z).div
    (envelope_analyticAt t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius P hP0 hP z hz)
    (envelope_ne_zero A₀ (center_ne_zero t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius P hP0 hP) P z)

theorem phase_deriv_model_bound (C : ℝ) (hC : 0 ≤ C) (hscale : K ≤ C*(t*w.re^3)) (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    ‖deriv (phase A₀ P) z-(w.re : ℂ)‖ ≤ 1/K+(9+64*C)/(t*w.re^3) := by
  have hS (y : ℂ) (hy : ‖y-(x : ℂ)‖ < r) :
      ‖phaseSlope t K x r w ht hK hr hi hnorm hs hE hsmall hradius y-Complex.I*w‖ ≤ 1/K+(9+64*C)/(t*w.re^3) :=
    phaseSlope_model_bound t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius C hC hscale y hy
  rw [(phase_hasDerivAt t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius P hP0 hP z hz).deriv]
  have hid : (phaseSlope t K x r w ht hK hr hi hnorm hs hE hsmall hradius z-conj (phaseSlope t K x r w ht hK hr hi hnorm hs hE hsmall hradius (conj z)))/
      (2*Complex.I)-(w.re : ℂ)=
      ((phaseSlope t K x r w ht hK hr hi hnorm hs hE hsmall hradius z-Complex.I*w)-
        conj (phaseSlope t K x r w ht hK hr hi hnorm hs hE hsmall hradius (conj z)-Complex.I*w))/(2*Complex.I) := by
    rw [Complex.re_eq_add_conj]
    simp only [map_sub,map_mul,Complex.conj_I]
    field_simp <;> ring
  rw [hid,norm_div,norm_mul,Complex.norm_ofNat,Complex.norm_I,mul_one]
  have htri := norm_sub_le (phaseSlope t K x r w ht hK hr hi hnorm hs hE hsmall hradius z-Complex.I*w)
    (conj (phaseSlope t K x r w ht hK hr hi hnorm hs hE hsmall hradius (conj z)-Complex.I*w))
  rw [norm_conj] at htri
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  linarith [hS z hz,hS (conj z) (conjugate_disk x r z hz)]


end Scaled

theorem eventually_uniform_normalized_cosine_error (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ Q : ℝ in atTop, ∀ (t K x r : ℝ) (w : ℂ)
      (ht : 1 ≤ t) (hK : 8 ≤ K) (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
      (hnorm : ‖w‖ ≤ 2*w.re) (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
      (hE : ‖Complex.exp (4*w)‖ ≤ K)
      (hsmall : (30005*Real.exp (-w.re))*K ≤ t*w.re^3/4)
      (hrpos : 0 < r) (hradius : r ≤ t*w.re^3/K)
      (P : ℂ → ℂ) (hP0 : P (x : ℂ)=0)
      (hP : ∀ z ∈ ball (x : ℂ) r,
        HasDerivAt P (phaseSlope t K x r w ht hK hr hi hnorm hs hE hsmall hradius z) z),
      r ≤ 1 → (|x|+r)*r ≤ 2*Q → Q=t*w.re^3 → K ≤ C*Q →
      let a := modelGaussianAmplitude t (x : ℂ)
        (RiemannQuarticTransitionAnalyticBranch.branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius (x : ℂ))
      ∀ z : ℂ, ‖z-(x : ℂ)‖ < r →
        ‖RiemannQuarticFlow.flow t z/envelope a P z-Complex.cos (phase a P z)‖ ≤ ε*Real.cosh (phase a P z).im := by
  filter_upwards [eventually_uniform_complex_pair_error C (ε/2) hC (by positivity)] with Q he
  intro t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius P hP0 hP hr1 hfreq hQid hscale
  dsimp only
  intro z hz
  let B := RiemannQuarticTransitionAnalyticBranch.branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius
  let a := modelGaussianAmplitude t (x : ℂ) (B (x : ℂ))
  have han := center_ne_zero t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius P hP0 hP
  have hEn := envelope_ne_zero a han P z
  have hpair := actual_pair_identity t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius P hP0 hP z hz
  have hnormpair := actual_pair_norm_identity t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius P hP0 hP z hz
  have h := he t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius hr1 hfreq hQid hscale z hz.le
  rw [hpair,hnormpair] at h
  have hfrac : RiemannQuarticFlow.flow t z/envelope a P z-Complex.cos (phase a P z)=
      (RiemannQuarticFlow.flow t z-envelope a P z*Complex.cos (phase a P z))/envelope a P z := by field_simp
  change ‖RiemannQuarticFlow.flow t z/envelope a P z-Complex.cos (phase a P z)‖ ≤ ε*Real.cosh (phase a P z).im
  rw [hfrac,norm_div]
  apply (div_le_iff₀ (norm_pos_iff.mpr hEn)).mpr
  exact h.trans_eq (by ring)

theorem eventually_actual_cosine_disks (M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ u : ℝ, 65536*(M+7) ≤ u →
      RiemannQuarticSaddleTimes.phaseSlope t u=0 → ∀ x : ℝ,
      |x| ≤ M*RiemannQuarticTransitionSaddle.realScale u →
      ∃ E Φ : ℂ → ℂ,
        (∀ z : ℂ, E z ≠ 0 ∧ E (conj z)=conj (E z) ∧ Φ (conj z)=conj (Φ z)) ∧
        ∀ z : ℂ, ‖z-(x : ℂ)‖ < 1/(128*(M+8)) →
          AnalyticAt ℂ E z ∧ AnalyticAt ℂ Φ z ∧
          ‖deriv Φ z-(u : ℂ)‖ ≤ M+8 ∧
          ‖RiemannQuarticFlow.flow t z/E z-Complex.cos (Φ z)‖ ≤ ε*Real.cosh (Φ z).im := by
  let C := 128*(M+8)
  let r := 1/C
  have hC : 0 < C := by dsimp [C]; positivity
  have hC1 : 1 ≤ C := by dsimp [C]; linarith
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by dsimp [r]; exact (div_le_iff₀ hC).mpr (by linarith)
  obtain ⟨U,hU⟩ := eventually_atTop.1 (eventually_uniform_normalized_cosine_error C ε hC hε)
  filter_upwards [eventually_ge_atTop (max U (max 1 (2*(9+64*C))))] with t htU
  intro u hu hstationary x hx
  have ht : 1 ≤ t := (le_max_left 1 _).trans ((le_max_right U _).trans htU)
  have hxnorm : ‖(x : ℂ)‖ ≤ M*RiemannQuarticTransitionSaddle.realScale u := by simpa using hx
  obtain ⟨w,hw,_⟩ := RiemannQuarticTransitionSaddle.existsUnique_transition_model_saddle
    t u M (x : ℂ) ht hM hu hstationary (by simp) hxnorm
  have hg := RiemannQuarticTransitionSaddle.transition_model_geometry t u M (x : ℂ) w
    ht hM hu hstationary (by simp) hxnorm hw.1 hw.2
  have hd := RiemannQuarticTransitionCorrection.transition_scale_data t u M (x : ℂ) w
    ht hM hu hstationary (by simp) hxnorm hw.1 hw.2
  let K := (M+8)*RiemannQuarticTransitionSaddle.realScale u
  let Q := t*w.re^3
  have hK : 8 ≤ K := hd.1
  have hK0 : 0 < K := by linarith
  have hnorm := hd.2.2.2.1
  have hE := hd.2.2.2.2.1
  have hsmall := hd.2.2.2.2.2
  have hcoord := (Complex.abs_re_le_norm (w-(u : ℂ))).trans hg.1
  simp only [Complex.sub_re,Complex.ofReal_re] at hcoord
  have hr : 120020 ≤ w.re := by linarith [(abs_le.mp hcoord).1]
  have hQtime : t ≤ Q := by
    have hp := one_le_pow₀ (by linarith : 1 ≤ w.re) (n := 3)
    dsimp [Q]
    nlinarith
  have hQ0 : 0 < Q := by dsimp [Q]; positivity
  have hscale : K ≤ C*Q :=
    RiemannQuarticTransitionGaussian.moving_scale_ratio_bound t u M w ht hM hu hstationary hg.1
  have hradius : r ≤ t*w.re^3/K := by
    apply (le_div_iff₀ hK0).mpr
    have hh : K/C ≤ Q := (div_le_iff₀ hC).mpr (by nlinarith)
    simpa only [r,one_div,div_eq_mul_inv,mul_comm,one_mul] using hh
  have hxK : |x| ≤ K := hx.trans (by
    dsimp [K]
    nlinarith [RiemannQuarticTransitionSaddle.realScale_pos u])
  have hfreq : (|x|+r)*r ≤ 2*Q := by
    have hxr : |x| *r ≤ Q := by
      dsimp [r]
      rw [mul_one_div]
      exact (div_le_iff₀ hC).mpr (by nlinarith [hxK,hscale])
    nlinarith [sq_nonneg r,mul_nonneg hrpos.le (sub_nonneg.mpr hr1)]
  let B := RiemannQuarticTransitionAnalyticBranch.branch t K x r w ht hK hr hd.2.2.1 hnorm hw.2 hE hsmall hradius
  obtain ⟨P,hP0,hP⟩ := exists_normalized_amplitude_phase t K x r w ht hK hr hd.2.2.1 hnorm hw.2 hE hsmall hrpos hradius
  let a := modelGaussianAmplitude t (x : ℂ) (B (x : ℂ))
  have han : a ≠ 0 := center_ne_zero t K x r w ht hK hr hd.2.2.1 hnorm hw.2 hE hsmall hrpos hradius P hP0 hP
  refine ⟨envelope a P,phase a P,?_,?_⟩
  · intro z
    exact ⟨envelope_ne_zero a han P z,RiemannQuarticFarCosinePhase.envelope_conj a P z,phase_conj a P z⟩
  · intro z hz
    have he := hU Q (((le_max_left U _).trans htU).trans hQtime) t K x r w ht hK hr hd.2.2.1
      hnorm hw.2 hE hsmall hrpos hradius P hP0 hP hr1 hfreq rfl hscale z hz
    have hder := phase_deriv_model_bound t K x r w ht hK hr hd.2.2.1 hnorm hw.2 hE hsmall hrpos hradius
      P hP0 hP C hC.le hscale z hz
    have hQlarge : 2*(9+64*C) ≤ Q :=
      ((le_max_right 1 _).trans ((le_max_right U _).trans htU)).trans hQtime
    have hdelta : 1/K+(9+64*C)/Q ≤ 1 := by
      have h1 : 1/K ≤ 1/2 := (div_le_iff₀ hK0).mpr (by linarith)
      have h2 : (9+64*C)/Q ≤ 1/2 := (div_le_iff₀ hQ0).mpr (by linarith)
      linarith
    have hwu : ‖(w.re : ℂ)-(u : ℂ)‖ ≤ M+7 := by
      simpa only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hcoord
    have htri := norm_add_le (deriv (phase a P) z-(w.re : ℂ)) ((w.re : ℂ)-(u : ℂ))
    rw [sub_add_sub_cancel] at htri
    refine ⟨envelope_analyticAt t K x r w ht hK hr hd.2.2.1 hnorm hw.2 hE hsmall hrpos hradius P hP0 hP z hz,
      phase_analyticAt t K x r w ht hK hr hd.2.2.1 hnorm hw.2 hE hsmall hrpos hradius P hP0 hP z hz,
      htri.trans (by linarith),he⟩

end OperatorDerivativeRewrite.Foundation.RiemannQuarticTransitionCosinePhase
