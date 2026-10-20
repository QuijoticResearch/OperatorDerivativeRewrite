import Foundation.RiemannQuarticUniformFarScale
import Foundation.RiemannQuarticThresholdZeros

/-! A single far-frequency cutoff controls all actual zeros for times in
a bounded interval above one. The cutoff depends on the upper time bound. -/
noncomputable section
open Set Metric Complex Filter
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticCompactTimeFarZeros
open RiemannQuarticFarModelSaddle RiemannQuarticSaddleBranch RiemannQuarticSaddleTheta
open RiemannQuarticComplexModelSaddle

theorem eventually_uniform_actual_far_saddles (T : ℝ) :
    ∀ᶠ a : ℝ in atTop, ∀ t : ℝ, 1 ≤ t → t ≤ T →
      ∀ z : ℂ, z.im ≤ 0 → ‖z‖ = 4*Real.pi*Real.exp (4*a) →
      ∃ w v : ℂ, 120020 ≤ w.re ∧ |w.im| ≤ 1/2 ∧
        100*(t*(‖w‖+1)^3+1) ≤ ‖z‖ ∧ modelDerivative t w = -(I*z) ∧
        ‖v-w‖ ≤ 1/‖z‖ ∧ complexSlope t v = -(I*z) := by
  filter_upwards [RiemannQuarticDomain.quartic_exponent_dominated (80000*(T+1)) 0,
    eventually_ge_atTop (240040 : ℝ)] with a hdom ha
  intro t ht htT z hz hn
  have ha0 : 0 ≤ a := by linarith
  have ht0 : 0 ≤ t := by linarith
  simp only [zero_mul,add_zero] at hdom
  have hdomt : 80000*(t+1)*a^4 ≤ Real.pi*Real.exp (4*a)/2 := by
    exact (mul_le_mul_of_nonneg_right (by linarith : 80000*(t+1) ≤ 80000*(T+1))
      (pow_nonneg ha0 4)).trans hdom
  have hp3 := pow_le_pow_left₀ (by linarith : 0 ≤ a+3) (by linarith : a+3 ≤ 2*a) 3
  have hp34 : a^3 ≤ a^4 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ a-1) (pow_nonneg ha0 3)]
  have hM : (a+3)^3 ≤ 8*a^4 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ 10000*(t+1))
  have hscale : 10000*(t+1)*(a+3)^3 ≤ ‖z‖ := by
    rw [hn]
    nlinarith [Real.pi_gt_three,Real.exp_pos (4*a)]
  have hpoly : 10000*(t+1)*(a+2)^3 ≤ 4*Real.pi*Real.exp (4*a) := by
    rw [← hn]
    exact (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith : 0 ≤ a+2) (by linarith : a+2 ≤ a+3) 3)
      (by positivity : 0 ≤ 10000*(t+1))).trans hscale
  obtain ⟨w,hw,hs,_,_,_⟩ := lower_half_circle_saddle t a ht0 (by linarith) hpoly z hz hn
  have hd : ‖w-complexAnchor z‖ ≤ (1/1024 : ℝ) := by
    simpa only [mem_closedBall,dist_eq_norm] using hw
  have hg := complexAnchor_geometry a ha0 z hz hn
  have hreal := (Complex.abs_re_le_norm (w-complexAnchor z)).trans hd
  simp only [Complex.sub_re,hg.1] at hreal
  have hr : 120020 ≤ w.re := by linarith [(abs_le.mp hreal).1]
  have hnorm : ‖w‖+1 ≤ a+3 := by
    have hb := norm_add_le (w-complexAnchor z) (complexAnchor z)
    rw [sub_add_cancel] at hb
    linarith [hg.2.2]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ ‖w‖+1) hnorm 3
  have hps : 100*(t*(‖w‖+1)^3+1) ≤ ‖z‖ := by
    have hmul := mul_le_mul_of_nonneg_left hpow ht0
    nlinarith [pow_nonneg (by linarith : 0 ≤ a+3) 3]
  have hi : |w.im| ≤ 1/2 := by
    have hh := abs_add_le (w.im-(complexAnchor z).im) (complexAnchor z).im
    simp only [sub_add_cancel] at hh
    have hdiff := (Complex.abs_im_le_norm (w-complexAnchor z)).trans hd
    simp only [Complex.sub_im] at hdiff
    linarith [hg.2.1,Real.pi_lt_d2]
  have hx : 10000 ≤ ‖z‖ := by
    have hp1 : 1 ≤ (a+3)^3 := one_le_pow₀ (by linarith : 1 ≤ a+3)
    nlinarith
  obtain ⟨v,hv,_⟩ := RiemannQuarticComplexCorrection.actual_far_saddle t z hz ht hx w hr hi hps hs
  exact ⟨w,v,hr,hi,hps,hs,by simpa only [mem_closedBall,dist_eq_norm] using hv.1,hv.2⟩

theorem uniform_actual_far_saddles (T : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ t : ℝ, 1 ≤ t → t ≤ T →
      ∀ z : ℂ, R ≤ ‖z‖ → z.im ≤ 0 →
      ∃ w v : ℂ, 120020 ≤ w.re ∧ |w.im| ≤ 1/2 ∧
        100*(t*(‖w‖+1)^3+1) ≤ ‖z‖ ∧ modelDerivative t w = -(I*z) ∧
        ‖v-w‖ ≤ 1/‖z‖ ∧ complexSlope t v = -(I*z) := by
  obtain ⟨A,hA⟩ := eventually_atTop.mp (eventually_uniform_actual_far_saddles T)
  let R := 4*Real.pi*Real.exp (4*A)
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨R,hR,?_⟩
  intro t ht htT z hlarge hz
  let a := Real.log (‖z‖/(4*Real.pi))/4
  have hnpos : 0 < ‖z‖ := hR.trans_le hlarge
  have hq : 0 < ‖z‖/(4*Real.pi) := by positivity
  have hn : ‖z‖ = 4*Real.pi*Real.exp (4*a) := by
    rw [show 4*a = Real.log (‖z‖/(4*Real.pi)) by dsimp [a]; ring,Real.exp_log hq]
    field_simp
  have hAa : A ≤ a := by
    have he : Real.exp (4*A) ≤ Real.exp (4*a) := by
      rw [hn] at hlarge
      change 4*Real.pi*Real.exp (4*A) ≤ 4*Real.pi*Real.exp (4*a) at hlarge
      exact (mul_le_mul_iff_right₀ (by positivity : 0 < 4*Real.pi)).mp hlarge
    have hh := Real.exp_le_exp.mp he
    linarith
  exact hA a hAa t ht htT z hz hn

theorem uniform_far_zeros_real (T : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ, 1 ≤ t → t ≤ T →
      ∀ z : ℂ, B ≤ ‖z‖ → RiemannQuarticFlow.flow t z = 0 → z.im = 0 := by
  obtain ⟨R,hR,hdata⟩ := uniform_actual_far_saddles T
  obtain ⟨N,hN⟩ := RiemannQuarticReflectedDominance.uniform_nonzero_below_unit_strip
  obtain ⟨X,hX⟩ := eventually_atTop.mp
    (RiemannQuarticFarCosinePhase.eventually_uniform_zero_strip (1/4) (by norm_num) (by norm_num))
  obtain ⟨Y,hY⟩ := eventually_atTop.mp
    RiemannQuarticFarSimpleZeros.eventually_uniform_real_simple_zeros
  let L := max 1 (max R (max N (max X (max Y 10000))))
  have hL1 : 1 ≤ L := by simp [L,le_max_iff]
  have hLR : R ≤ L := by simp [L,le_max_iff]
  have hLN : N ≤ L := by simp [L,le_max_iff]
  have hLX : X ≤ L := by simp [L,le_max_iff]
  have hLY : Y ≤ L := by simp [L,le_max_iff]
  have hL10000 : 10000 ≤ L := by simp [L,le_max_iff]
  refine ⟨2*L,by positivity,?_⟩
  intro t ht htT z hz hzero
  have hbelow (q : ℂ) (hq : L ≤ ‖q‖) (hy : q.im ≤ -1) :
      RiemannQuarticFlow.flow t q ≠ 0 := by
    have hq0 : q.im ≤ 0 := by linarith
    obtain ⟨w,v,hr,hi,hp,hs,hv,hroot⟩ := hdata t ht htT q (hLR.trans hq) hq0
    exact hN q hq0 (hLN.trans hq) t ht w v hr hi hp hs hv q hroot hy
  have hstrip (q : ℂ) (hq : L ≤ q.re) (hy : |q.im| < 1)
      (hzeroq : RiemannQuarticFlow.flow t q = 0) : q.im = 0 := by
    let x := q.re
    have hx : 10000 ≤ x := hL10000.trans hq
    have hx0 : 0 < x := by linarith
    have hnorm : ‖(x : ℂ)‖ = x := by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx0]
    obtain ⟨w,v,hr,hi,hp,hs,_,_⟩ := hdata t ht htT (x : ℂ)
      (by simpa only [hnorm] using hLR.trans hq) (by simp)
    rw [hnorm] at hp
    obtain ⟨P,hP0,hP⟩ :=
      RiemannQuarticFarGaussianPhase.exists_normalized_amplitude_phase t x ht hx w hr hi hp hs
    have hdist : ‖q-(x : ℂ)‖ = |q.im| := by
      have he : q-(x : ℂ) = (q.im : ℂ)*I := by apply Complex.ext <;> simp [x]
      rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
    have hzunit : ‖q-(x : ℂ)‖ < 1 := by rw [hdist]; exact hy
    have hthin : |q.im| ≤ 1/w.re := by
      simpa using (hX x (hLX.trans hq) t ht hx w hr hi hp hs P hP0 hP q hzunit hzeroq).2
    have hhalf : ‖q-(x : ℂ)‖ < 1/2 := by
      rw [hdist]
      exact hthin.trans_lt ((div_lt_iff₀ (by linarith : 0 < w.re)).mpr (by linarith))
    exact (hY x (hLY.trans hq) t ht hx w hr hi hp hs q hhalf hzeroq).1
  have hzL : L ≤ ‖z‖ := by linarith
  by_cases him : |z.im| < 1
  · have hn := Complex.norm_le_abs_re_add_abs_im z
    have hre : L ≤ |z.re| := by linarith
    rcases le_total 0 z.re with hpos | hneg
    · rw [abs_of_nonneg hpos] at hre
      exact hstrip z hre him hzero
    · rw [abs_of_nonpos hneg] at hre
      have hnegzero : RiemannQuarticFlow.flow t (-z) = 0 := by
        rw [RiemannQuarticEvolution.flow_even,hzero]
      have hh := hstrip (-z) (by simpa using hre) (by simpa using him) hnegzero
      simpa using hh
  · have hab : 1 ≤ |z.im| := le_of_not_gt him
    exfalso
    rcases le_total z.im 0 with hlo | hhi
    · have hy : z.im ≤ -1 := by rw [abs_of_nonpos hlo] at hab; linarith
      exact hbelow z hzL hy hzero
    · have hy : (conj z).im ≤ -1 := by
        rw [abs_of_nonneg hhi] at hab
        simp only [Complex.conj_im]
        linarith
      have hc : RiemannQuarticFlow.flow t (conj z) = 0 := by
        rw [RiemannQuarticNormalizedAnalytic.flow_conj,hzero]
        simp
      exact hbelow (conj z) (by simpa using hzL) hy hc

end OperatorDerivativeRewrite.Foundation.RiemannQuarticCompactTimeFarZeros
