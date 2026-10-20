import Foundation.RiemannSixthFarSimpleZeros
/-! The actual unit-height far strip: quantitative localization moves every
candidate zero into the buffered half-disk before the simplicity criterion. -/
noncomputable section
open Set Metric Complex Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthFarUnitStrip
open RiemannSixthFarAnalyticBranch RiemannSixthFarGaussianPhase

theorem exists_uniform_actual_far_unit_strip :
    ∃ K : ℝ, 0 < K ∧ ∃ X : ℝ, ∀ t u : ℝ,
      1 ≤ t → 120021 ≤ u → RiemannEvenRealSaddle.phaseSlope 3 t u = 0 →
      ∀ z : ℂ, max X (K*RiemannQuarticTransitionSaddle.realScale u) ≤ z.re →
        |z.im| < 1 → RiemannEvenFlow.flow 3 t z=0 →
        z.im=0 ∧ deriv (RiemannEvenFlow.flow 3 t) z ≠ 0 := by
  obtain ⟨K,hK,hC⟩ := RiemannSixthUniformFarSaddles.exists_uniform_actual_far_frequency_disks
  obtain ⟨X,hX⟩ := eventually_atTop.mp
    (RiemannSixthFarCosinePhase.eventually_uniform_zero_strip (1/4) (by norm_num) (by norm_num))
  obtain ⟨Y,hY⟩ := eventually_atTop.mp RiemannSixthFarSimpleZeros.eventually_uniform_real_simple_zeros
  refine ⟨K,hK,max X Y,?_⟩
  intro t u ht hu hstat z hcut him hzero
  let x := z.re
  have hxfar : K*RiemannQuarticTransitionSaddle.realScale u ≤ x := (le_max_right _ _).trans hcut
  have hxX : X ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hcut)
  have hxY : Y ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hcut)
  obtain ⟨w,hxl,hr,hi,hp,hs,hroots⟩ := hC t u x ht hu hstat hxfar
  obtain ⟨P,hP0,hP⟩ := exists_normalized_amplitude_phase t x ht hxl w hr hi hp hs
  have hdist : ‖z-(x : ℂ)‖=|z.im| := by
    have he : z-(x : ℂ)=(z.im : ℂ)*Complex.I := by apply Complex.ext <;> simp [x]
    rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
  have hzunit : ‖z-(x : ℂ)‖ < 1 := by rw [hdist]; exact him
  have hthin : |z.im| ≤ 1/w.re := by
    simpa using (hX x hxX t ht hxl w hr hi hp hs P hP0 hP z hzunit hzero).2
  have hzhalf : ‖z-(x : ℂ)‖ < 1/2 := by
    rw [hdist]
    exact hthin.trans_lt ((div_lt_iff₀ (by linarith : 0 < w.re)).mpr (by linarith))
  exact hY x hxY t ht hxl w hr hi hp hs z hzhalf hzero

theorem eventually_far_unit_strip_real_simple :
    ∀ᶠ t : ℝ in atTop, ∃ X : ℝ, ∀ z : ℂ, X ≤ z.re → |z.im| < 1 →
      RiemannEvenFlow.flow 3 t z=0 → z.im=0 ∧ deriv (RiemannEvenFlow.flow 3 t) z ≠ 0 := by
  obtain ⟨K,hK,X,hX⟩ := exists_uniform_actual_far_unit_strip
  filter_upwards [RiemannEvenRealSaddle.maxima_escape 3 (by norm_num) 120021 (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with t he ht
  obtain ⟨u,hu,hmax⟩ := RiemannEvenRealSaddle.exists_global_max 3 t
  have hlarge := he u hu hmax
  have hs := RiemannEvenRealSaddle.max_real_stationary 3 t u (by linarith) hmax
  exact ⟨max X (K*RiemannQuarticTransitionSaddle.realScale u),hX t u ht hlarge.le hs⟩

end OperatorDerivativeRewrite.Foundation.RiemannSixthFarUnitStrip
