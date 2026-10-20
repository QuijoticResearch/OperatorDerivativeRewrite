import Foundation.RiemannQuarticTransitionSimpleZeros
import Foundation.RiemannQuarticReflectedDominance
/-! Explicit uniform comparison of actual stationary scales with far-saddle
cubic hypotheses. No interchange of fixed-time and late-time limits is used. -/
noncomputable section
open Set Metric Complex Filter
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticUniformFarScale
open RiemannQuarticTransitionSaddle RiemannQuarticFarModelSaddle
open RiemannQuarticSaddleTimes RiemannQuarticSaddleTheta

theorem exp_gap_cubic (d : ℝ) (hd : 16 ≤ d) :
    20000*(1+d)^3 ≤ Real.exp (4*d) := by
  have hd0 : 0 ≤ d := by linarith
  have hp := Real.pow_div_factorial_le_exp (2*d) (by positivity : 0 ≤ 2*d) 3
  norm_num at hp
  have hcube : d^3 ≤ Real.exp (2*d) := by nlinarith [pow_nonneg hd0 3]
  have hn := Real.pow_div_factorial_le_exp (32 : ℝ) (by norm_num) 5
  norm_num at hn
  have hlarge : 200000 ≤ Real.exp (2*d) := by
    have hm := Real.exp_le_exp.mpr (show (32 : ℝ) ≤ 2*d by linarith)
    linarith
  have hprod := mul_le_mul hlarge hcube (pow_nonneg hd0 3) (Real.exp_pos _).le
  have hpoly := pow_le_pow_left₀ (by linarith : 0 ≤ 1+d) (show 1+d ≤ 2*d by linarith) 3
  have heq : Real.exp (2*d)*Real.exp (2*d)=Real.exp (4*d) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq] at hprod
  nlinarith [pow_nonneg hd0 3]

theorem stationary_far_cubic_scale (t u a : ℝ) (ht : 1 ≤ t) (hu : 16 ≤ u)
    (hs : phaseSlope t u=0) (ha : u+16 ≤ a) :
    10000*(t+1)*(a+4)^3 ≤ realScale a := by
  let d := a-u
  have hd : 16 ≤ d := by dsimp [d]; linarith
  have hd0 : 0 ≤ d := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hlinear : a+4 ≤ u*(1+d) := by
    have hm := mul_le_mul_of_nonneg_right hu hd0
    dsimp [d] at *
    nlinarith
  have hpoly : (a+4)^3 ≤ u^3*(1+d)^3 := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ a+4) hlinear 3
    simpa only [mul_pow] using h
  have hbase : t*u^3 ≤ realScale u := by
    have h := (RiemannQuarticCurvature.stationary_scale_bounds t u (by linarith) hs).2
    dsimp [realScale]
    nlinarith [Real.pi_pos,Real.exp_pos (4*u)]
  have htime : 10000*(t+1) ≤ 20000*t := by linarith
  have hexp := exp_gap_cubic d hd
  calc
    _ ≤ (20000*t)*(u^3*(1+d)^3) :=
      mul_le_mul htime hpoly (pow_nonneg (by linarith : 0 ≤ a+4) 3) (by positivity)
    _ ≤ realScale u*(20000*(1+d)^3) := by
      have hm := mul_le_mul_of_nonneg_right hbase (show 0 ≤ 20000*(1+d)^3 by positivity)
      nlinarith
    _ ≤ realScale u*Real.exp (4*d) := mul_le_mul_of_nonneg_left hexp (realScale_pos u).le
    _ = realScale a := by
      unfold realScale
      rw [mul_assoc,← Real.exp_add]
      congr 2
      dsimp [d]
      ring

theorem far_parameter (u x : ℝ) (hx : Real.exp 64*realScale u ≤ x) :
    ∃ a : ℝ, u+16 ≤ a ∧ x=realScale a := by
  have hx0 : 0 < x := lt_of_lt_of_le (mul_pos (Real.exp_pos _) (realScale_pos u)) hx
  let a := Real.log (x/(4*Real.pi))/4
  have hxarg : 0 < x/(4*Real.pi) := by positivity
  have hid : x=realScale a := by
    dsimp [realScale,a]
    rw [show 4*(Real.log (x/(4*Real.pi))/4)=Real.log (x/(4*Real.pi)) by ring,Real.exp_log hxarg]
    field_simp
  have hstart : Real.exp (4*(u+16)) ≤ x/(4*Real.pi) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*Real.pi)).mpr
    have heq : Real.exp (4*(u+16))*(4*Real.pi)=Real.exp 64*realScale u := by
      unfold realScale
      rw [show 4*(u+16)=4*u+64 by ring,Real.exp_add]
      ring
    rw [heq]
    exact hx
  have hlog := Real.log_le_log (Real.exp_pos _) hstart
  rw [Real.log_exp] at hlog
  exact ⟨a,by dsimp [a]; linarith,hid⟩

theorem uniform_actual_far_saddles (t u : ℝ) (ht : 1 ≤ t) (hu : 120021 ≤ u)
    (hs : phaseSlope t u=0) (z : ℂ) (hz : z.im ≤ 0)
    (hcut : Real.exp 64*realScale u ≤ ‖z‖) :
    ∃ w v : ℂ, 120020 ≤ w.re ∧ |w.im| ≤ 1/2 ∧
      100*(t*(‖w‖+1)^3+1) ≤ ‖z‖ ∧ modelDerivative t w= -(Complex.I*z) ∧
      ‖v-w‖ ≤ 1/‖z‖ ∧ RiemannQuarticSaddleBranch.complexSlope t v= -(Complex.I*z) := by
  obtain ⟨a,ha,hn⟩ := far_parameter u ‖z‖ hcut
  have ha4 : 4 ≤ a := by linarith
  have hscale := stationary_far_cubic_scale t u a ht (by linarith) hs ha
  have hpoly : 10000*(t+1)*(a+2)^3 ≤ realScale a := by
    apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith : 0 ≤ a+2)
      (show a+2 ≤ a+4 by linarith) 3) (show 0 ≤ 10000*(t+1) by positivity)).trans hscale
  obtain ⟨w,hw,hroot,_,_,_⟩ := RiemannQuarticComplexModelSaddle.lower_half_circle_saddle t a
    (by linarith) ha4 hpoly z hz hn
  have hg := RiemannQuarticComplexModelSaddle.complexAnchor_geometry a (by linarith) z hz hn
  have hd : ‖w-RiemannQuarticComplexModelSaddle.complexAnchor z‖ ≤ (1/1024 : ℝ) := by
    simpa only [mem_closedBall,dist_eq_norm] using hw
  have hreal := (Complex.abs_re_le_norm (w-RiemannQuarticComplexModelSaddle.complexAnchor z)).trans hd
  simp only [Complex.sub_re,hg.1] at hreal
  have hr : 120020 ≤ w.re := by linarith [(abs_le.mp hreal).1]
  have hnorm : ‖w‖+1 ≤ a+3 := by
    have hb := norm_add_le (w-RiemannQuarticComplexModelSaddle.complexAnchor z)
      (RiemannQuarticComplexModelSaddle.complexAnchor z)
    rw [sub_add_cancel] at hb
    linarith [hg.2.2]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ ‖w‖+1) (hnorm.trans (by linarith : a+3 ≤ a+4)) 3
  have ha1 : 1 ≤ (a+4)^3 := one_le_pow₀ (by linarith : 1 ≤ a+4)
  have hps : 100*(t*(‖w‖+1)^3+1) ≤ ‖z‖ := by
    have hm := mul_le_mul_of_nonneg_left hpow (show 0 ≤ t by linarith)
    rw [← hn] at hscale
    nlinarith [pow_nonneg (by linarith : 0 ≤ a+4) 3]
  have hi : |w.im| ≤ 1/2 := by
    have hh := abs_add_le (w.im-(RiemannQuarticComplexModelSaddle.complexAnchor z).im)
      (RiemannQuarticComplexModelSaddle.complexAnchor z).im
    rw [sub_add_cancel] at hh
    have hdiff := (Complex.abs_im_le_norm (w-RiemannQuarticComplexModelSaddle.complexAnchor z)).trans hd
    simp only [Complex.sub_im] at hdiff
    linarith [hg.2.1,Real.pi_lt_d2]
  have hx : 10000 ≤ ‖z‖ := by
    have hh := mul_le_mul_of_nonneg_left ha1 (show 0 ≤ 10000*(t+1) by positivity)
    rw [← hn] at hscale
    nlinarith
  obtain ⟨v,hv,_⟩ := RiemannQuarticComplexCorrection.actual_far_saddle t z hz ht hx w hr hi hps hroot
  exact ⟨w,v,hr,hi,hps,hroot,by simpa only [mem_closedBall,dist_eq_norm] using hv.1,hv.2⟩

theorem uniform_far_zeros_real :
    ∃ N : ℝ, ∀ (t u : ℝ), 1 ≤ t → 120021 ≤ u → phaseSlope t u=0 → N ≤ u →
      ∀ z : ℂ, 2*Real.exp 64*realScale u ≤ ‖z‖ → RiemannQuarticFlow.flow t z=0 → z.im=0 := by
  obtain ⟨N,hN⟩ := RiemannQuarticReflectedDominance.uniform_nonzero_below_unit_strip
  obtain ⟨X,hX⟩ := eventually_atTop.1
    (RiemannQuarticFarCosinePhase.eventually_uniform_zero_strip (1/4) (by norm_num) (by norm_num))
  obtain ⟨Y,hY⟩ := eventually_atTop.1 RiemannQuarticFarSimpleZeros.eventually_uniform_real_simple_zeros
  let T := max N (max X (max Y 10000))
  refine ⟨T,?_⟩
  intro t u ht hu hs hTu z hz hzero
  let F := Real.exp 64*realScale u
  have hF : u ≤ F := by
    have he := Real.add_one_le_exp (4*u)
    have hpi := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (Real.exp_pos (4*u)).le
    have hB : u ≤ realScale u := by unfold realScale; nlinarith
    have h64 : 1 ≤ Real.exp (64 : ℝ) := by linarith [Real.add_one_le_exp (64 : ℝ)]
    exact hB.trans (by dsimp [F]; nlinarith [realScale_pos u])
  have hNF : N ≤ F := ((le_max_left _ _).trans hTu).trans hF
  have hXF : X ≤ F := ((le_max_left _ _).trans ((le_max_right _ _).trans hTu)).trans hF
  have hYF : Y ≤ F := ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hTu))).trans hF
  have h10000F : 10000 ≤ F := ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hTu))).trans hF
  have hbelow (q : ℂ) (hq : F ≤ ‖q‖) (hy : q.im ≤ -1) : RiemannQuarticFlow.flow t q ≠ 0 := by
    obtain ⟨w,v,hr,hi,hp,hmodel,hv,hroot⟩ := uniform_actual_far_saddles t u ht hu hs q (by linarith) hq
    exact hN q (by linarith) (hNF.trans hq) t ht w v hr hi hp hmodel hv q hroot hy
  have hstrip (q : ℂ) (hq : F ≤ q.re) (hy : |q.im| < 1)
      (hqzero : RiemannQuarticFlow.flow t q=0) : q.im=0 := by
    let x := q.re
    have hx : 10000 ≤ x := h10000F.trans hq
    have hx0 : 0 < x := by linarith
    have hnorm : ‖(x : ℂ)‖=x := by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx0]
    obtain ⟨w,v,hr,hi,hp,hmodel,hv,hroot⟩ := uniform_actual_far_saddles t u ht hu hs (x : ℂ)
      (by simp) (by simpa only [hnorm] using hq)
    rw [hnorm] at hp hv
    obtain ⟨P,hP0,hP⟩ := RiemannQuarticFarGaussianPhase.exists_normalized_amplitude_phase t x ht hx w hr hi hp hmodel
    have hdist : ‖q-(x : ℂ)‖=|q.im| := by
      have he : q-(x : ℂ)=(q.im : ℂ)*Complex.I := by apply Complex.ext <;> simp [x]
      rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
    have hzunit : ‖q-(x : ℂ)‖ < 1 := by rw [hdist]; exact hy
    have hthin : |q.im| ≤ 1/w.re := by
      simpa using (hX x (hXF.trans hq) t ht hx w hr hi hp hmodel P hP0 hP q hzunit hqzero).2
    have hhalf : ‖q-(x : ℂ)‖ < 1/2 := by
      rw [hdist]
      exact hthin.trans_lt ((div_lt_iff₀ (by linarith : 0 < w.re)).mpr (by linarith))
    exact (hY x (hYF.trans hq) t ht hx w hr hi hp hmodel q hhalf hqzero).1
  have hzF : F ≤ ‖z‖ := by change 2*Real.exp 64*realScale u ≤ ‖z‖ at hz; dsimp [F]; nlinarith
  by_cases him : |z.im| < 1
  · have hn := Complex.norm_le_abs_re_add_abs_im z
    have hreal : F ≤ |z.re| := by
      change 2*Real.exp 64*realScale u ≤ ‖z‖ at hz
      change Real.exp 64*realScale u ≤ |z.re|
      dsimp [F] at hF
      linarith
    rcases le_total 0 z.re with hpos | hneg
    · rw [abs_of_nonneg hpos] at hreal
      exact hstrip z hreal him hzero
    · rw [abs_of_nonpos hneg] at hreal
      have hzneg : RiemannQuarticFlow.flow t (-z)=0 := by rw [RiemannQuarticEvolution.flow_even,hzero]
      have hh := hstrip (-z) (by simpa using hreal) (by simpa using him) hzneg
      simpa using hh
  · have hab : 1 ≤ |z.im| := le_of_not_gt him
    exfalso
    rcases le_total z.im 0 with hlo | hhi
    · have hy : z.im ≤ -1 := by rw [abs_of_nonpos hlo] at hab; linarith
      exact hbelow z hzF hy hzero
    · have hy : (conj z).im ≤ -1 := by
        rw [abs_of_nonneg hhi] at hab
        simp only [Complex.conj_im]
        linarith
      have hzero' : RiemannQuarticFlow.flow t (conj z)=0 := by
        rw [RiemannQuarticNormalizedAnalytic.flow_conj,hzero]
        simp
      exact hbelow (conj z) (by simpa using hzF) hy hzero'

theorem eventually_all_zeros_real :
    ∀ᶠ t : ℝ in atTop, ∀ z : ℂ, RiemannQuarticFlow.flow t z=0 → z.im=0 := by
  obtain ⟨N,hfar⟩ := uniform_far_zeros_real
  let M := 2*Real.exp (64 : ℝ)
  let R := max N 120021
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  filter_upwards [RiemannQuarticTransitionSimpleZeros.bounded_ratio_real_simple_zeros M hM R hR,
    eventually_ge_atTop (1 : ℝ)] with t hbounded ht
  obtain ⟨u,huR,huM,hs,hzeros⟩ := hbounded
  have huN : N ≤ u := (le_max_left _ _).trans huR
  have hu : 120021 ≤ u := (le_max_right _ _).trans huR
  intro z hz
  by_cases hnorm : ‖z‖ ≤ M*realScale u
  · exact (hzeros z hnorm hz).1
  · exact hfar t u ht hu hs huN z (by dsimp [M] at hnorm; linarith) hz

end OperatorDerivativeRewrite.Foundation.RiemannQuarticUniformFarScale
