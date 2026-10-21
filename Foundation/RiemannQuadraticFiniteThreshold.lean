import Foundation.RiemannQuadraticDensityHeat

/-! Actual finite attained quadratic Xi reality threshold. The lower-bound proof uses actual Gaussian smoothing and verified density decay, without importing a measure classification. The exact threshold and zero-time reality remain unknown. -/

noncomputable section
open MeasureTheory Filter Set Real
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuadraticFiniteThreshold
open RiemannQuarticKernel RiemannQuadraticDensitySmoothing

theorem quadratic_polynomial_lower (a b c y : ℝ) (hy : 1 ≤ y) :
    -(|a|+|b|+|c|)*y^2 ≤ a*y^2+b*y+c := by
  have ha := mul_nonneg (by linarith [neg_abs_le a] : 0 ≤ a+|a|) (sq_nonneg y)
  have hb := mul_nonneg (by linarith [neg_abs_le b] : 0 ≤ b+|b|) (by linarith : 0 ≤ y)
  have hbd := mul_nonneg (abs_nonneg b) (by nlinarith : 0 ≤ y^2-y)
  have hcd := mul_nonneg (abs_nonneg c) (by nlinarith : 0 ≤ y^2-1)
  nlinarith [neg_abs_le c]

theorem density_four_point_failure :
    let q : ℝ → ℝ := fun v => log (evenDensity (sqrt v))
    ∃ y : ℝ, 1 ≤ y ∧ ¬
      (q 1+(y-1)*(q 2-q 1)-2*(y-1)^2*(2*q (1/2)-q 0-q 1) ≤ q y) := by
  let q : ℝ → ℝ := fun v => log (evenDensity (sqrt v))
  change ∃ y : ℝ, 1 ≤ y ∧ ¬
    (q 1+(y-1)*(q 2-q 1)-2*(y-1)^2*(2*q (1/2)-q 0-q 1) ≤ q y)
  by_contra hn
  have hfour (y : ℝ) (hy : 1 ≤ y) :
      q 1+(y-1)*(q 2-q 1)-2*(y-1)^2*(2*q (1/2)-q 0-q 1) ≤ q y := by
    by_contra hbad
    exact hn ⟨y,hy,hbad⟩
  let S : ℝ := q 2-q 1
  let D : ℝ := 2*q (1/2)-q 0-q 1
  let a : ℝ := -2*D
  let b : ℝ := S+4*D
  let c : ℝ := q 1-S-2*D
  let T : ℝ := |a|+|b|+|c|
  have hlower (x : ℝ) (hx : 1 ≤ x) : -T*x^4 ≤ log (kernel x) := by
    have hx2 : 1 ≤ x^2 := by nlinarith
    have he := quadratic_polynomial_lower a b c (x^2) hx2
    have hf := hfour (x^2) hx2
    have hvalue : q (x^2) = log (kernel x) := by
      simp only [q,evenDensity,Real.sqrt_sq_eq_abs,abs_abs,abs_of_nonneg (by linarith : 0 ≤ x)]
    rw [hvalue] at hf
    dsimp only [a,b,c,S,D] at he
    change -(|a|+|b|+|c|)*x^4 ≤ _
    dsimp only [a,b,c,S,D]
    nlinarith
  have hlarge (x : ℝ) (hx : 1 ≤ x) : 1 ≤ exp (T*x^4)*kernel x := by
    have he := Real.exp_le_exp.mpr (hlower x hx)
    rw [Real.exp_log (kernel_pos x (by linarith))] at he
    have hp := mul_le_mul_of_nonneg_left he (Real.exp_pos (T*x^4)).le
    have hc : exp (T*x^4)*exp (-T*x^4) = 1 := by
      rw [← Real.exp_add,show T*x^4+-T*x^4=0 by ring,Real.exp_zero]
    rw [hc] at hp
    exact hp
  have hsmall := (RiemannEvenRealSaddle.weighted_tendsto_zero 2 T).eventually
    (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
  obtain ⟨x,hx,he⟩ := ((eventually_ge_atTop (1:ℝ)).and hsmall).exists
  have hl := hlarge x hx
  have hw : RiemannEvenDomain.weighted 2 0 T 0 x = exp (T*x^4)*kernel x := by
    norm_num [RiemannEvenDomain.weighted]
  rw [hw] at he
  linarith

end OperatorDerivativeRewrite.Foundation.RiemannQuadraticFiniteThreshold

noncomputable section
open MeasureTheory Filter Set Real
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuadraticFiniteThreshold
open RiemannQuadraticDensitySmoothing RiemannEvenRealityClosed RiemannEvenFlow
open RiemannQuadraticDensityHeat

theorem not_all_real_times :
    ¬ (∀ t : ℝ, ∀ z : ℂ, flow 1 t z = 0 → z.im = 0) := by
  intro hall
  let epsilon : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have heps : Tendsto epsilon atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let qn : ℕ → ℝ → ℝ := fun n v => log (smoothing (epsilon n) (sqrt v))
  let q : ℝ → ℝ := fun v => log (evenDensity (sqrt v))
  have hq (v : ℝ) : Tendsto (fun n => qn n v) atTop (nhds (q v)) :=
    (Real.continuousAt_log (ne_of_gt (evenDensity_pos (sqrt v)))).tendsto.comp
      (smoothing_limit epsilon heps (sqrt v))
  obtain ⟨y,hy,hbad⟩ := density_four_point_failure
  change ¬ (q 1+(y-1)*(q 2-q 1)-2*(y-1)^2*(2*q (1/2)-q 0-q 1) ≤ q y) at hbad
  apply hbad
  have hleft := ((hq 1).add (((hq 2).sub (hq 1)).const_mul (y-1))).sub
    (((((hq (1/2)).const_mul 2).sub (hq 0)).sub (hq 1)).const_mul (2*(y-1)^2))
  apply le_of_tendsto_of_tendsto hleft (hq y)
  exact Eventually.of_forall (fun n => smoothing_four_point hall (epsilon n)
    (by dsimp [epsilon]; positivity) y hy)

theorem nonreal_zero_exists : ∃ (t : ℝ) (z : ℂ), flow 1 t z = 0 ∧ z.im ≠ 0 := by
  simpa only [not_forall,not_imp,exists_prop] using not_all_real_times

theorem real_times_bddBelow : BddBelow (realTimes 1) :=
  quadratic_bddBelow_iff_nonreal_exists.mpr nonreal_zero_exists

def threshold : ℝ := sInf (realTimes 1)

theorem real_times_eq_Ici : realTimes 1 = Ici threshold :=
  quadratic_eq_Ici real_times_bddBelow

theorem real_zeros_iff (t : ℝ) :
    (∀ z : ℂ, flow 1 t z = 0 → z.im = 0) ↔ threshold ≤ t := by
  change t ∈ realTimes 1 ↔ _
  rw [real_times_eq_Ici]
  rfl

theorem nonreal_zeros_iff (t : ℝ) :
    (∃ z : ℂ, flow 1 t z = 0 ∧ z.im ≠ 0) ↔ t < threshold := by
  have he := not_congr (real_zeros_iff t)
  simpa only [not_forall,not_imp,exists_prop,not_le] using he

theorem threshold_le_half : threshold ≤ 1/2 :=
  csInf_le real_times_bddBelow RiemannQuadraticGlobalStrip.classical_half_all_real

theorem negative_time_nonreal_exists :
    ∃ t : ℝ, t < 0 ∧ ∃ z : ℂ, flow 1 t z = 0 ∧ z.im ≠ 0 := by
  refine ⟨threshold-1,by linarith [threshold_le_half],?_⟩
  exact (nonreal_zeros_iff _).mpr (by linarith)

theorem threshold_le_seven_eighths
    (hfree : ∀ w : ℂ, (7/8:ℝ) < w.re → riemannZeta w ≠ 0) : threshold ≤ 9/32 :=
  (real_zeros_iff (9/32)).mp
    (RiemannQuadraticStripEvolution.conditional_seven_eighths_real_zeros hfree (9/32) le_rfl)

theorem zero_time_reality_iff :
    (∀ z : ℂ, flow 1 0 z = 0 → z.im = 0) ↔ threshold ≤ 0 := real_zeros_iff 0

end OperatorDerivativeRewrite.Foundation.RiemannQuadraticFiniteThreshold
