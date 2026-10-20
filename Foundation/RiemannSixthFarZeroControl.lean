import Foundation.RiemannSixthComplexReflectedDominance
import Foundation.RiemannSixthFarSimpleZeros
/-! Uniform reality and simplicity of every sufficiently far actual A(6) zero.
The bounded transition region remains a separate mathematical obligation. -/
noncomputable section
open Set Metric Complex Filter
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthFarZeroControl
open RiemannEvenFlow RiemannQuarticTransitionSaddle

theorem deriv_even_flow_neg (m : ℕ) (t : ℝ) (z : ℂ) :
    deriv (flow m t) (-z) = -deriv (flow m t) z := by
  have h := ((flow_differentiable m t (-z)).hasDerivAt.comp z (hasDerivAt_neg z)).deriv
  have he : (fun q : ℂ => flow m t (-q)) = flow m t := by
    funext q
    exact RiemannEvenEvolution.flow_even m t q
  change deriv (fun q : ℂ => flow m t (-q)) z = deriv (flow m t) (-z) * -1 at h
  rw [he] at h
  linear_combination h

theorem uniform_actual_far_unit_strip :
    ∃ K : ℝ, 0 < K ∧ ∀ t u : ℝ, 1 ≤ t → 120021 ≤ u →
      RiemannEvenRealSaddle.phaseSlope 3 t u = 0 → ∀ z : ℂ,
        K*realScale u ≤ z.re → |z.im| < 1 → flow 3 t z = 0 →
          z.im = 0 ∧ deriv (flow 3 t) z ≠ 0 := by
  obtain ⟨K,hK,hC⟩ := RiemannSixthUniformFarSaddles.exists_uniform_actual_far_frequency_disks
  obtain ⟨X₁,hthin⟩ := eventually_atTop.mp
    (RiemannSixthFarCosinePhase.eventually_uniform_zero_strip (1/4) (by norm_num) (by norm_num))
  obtain ⟨X₂,hsimple⟩ := eventually_atTop.mp
    RiemannSixthFarSimpleZeros.eventually_uniform_real_simple_zeros
  let L := max K (max 10000 (max X₁ X₂))
  have hKL : K ≤ L := le_max_left _ _
  have hL : 0 < L := hK.trans_le hKL
  have hbase : max 10000 (max X₁ X₂) ≤ L := le_max_right _ _
  have h10000 : 10000 ≤ L := (le_max_left _ _).trans hbase
  have hX₁ : X₁ ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hbase)
  have hX₂ : X₂ ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hbase)
  refine ⟨L,hL,?_⟩
  intro t u ht hu hstat z hcut him hzero
  have hB : 1 ≤ realScale u := by
    unfold realScale
    have he : 1 ≤ Real.exp (4*u) := Real.one_le_exp (by linarith)
    nlinarith [Real.pi_gt_three]
  have hLx : L ≤ z.re := by nlinarith
  have hx : 10000 ≤ z.re := h10000.trans hLx
  have hKcut : K*realScale u ≤ z.re :=
    (mul_le_mul_of_nonneg_right hKL (by linarith)).trans hcut
  obtain ⟨w,hlarge,hr,hi,hp,hs,hroots⟩ := hC t u z.re ht hu hstat hKcut
  obtain ⟨P,hP0,hP⟩ := RiemannSixthFarGaussianPhase.exists_normalized_amplitude_phase
    t z.re ht hx w hr hi hp hs
  have hdist : ‖z-(z.re : ℂ)‖ = |z.im| := by
    have he : z-(z.re : ℂ)=(z.im : ℂ)*Complex.I := by apply Complex.ext <;> simp
    rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
  have hzunit : ‖z-(z.re : ℂ)‖ < 1 := by rw [hdist]; exact him
  have hbound : |z.im| ≤ 1/w.re := by
    simpa using (hthin z.re (hX₁.trans hLx) t ht hx w hr hi hp hs P hP0 hP z hzunit hzero).2
  have hhalf : |z.im| < 1/2 := hbound.trans_lt
    ((div_lt_iff₀ (by linarith : 0 < w.re)).mpr (by linarith))
  exact hsimple z.re (hX₂.trans hLx) t ht hx w hr hi hp hs z (by rw [hdist]; exact hhalf) hzero

theorem uniform_actual_far_right_half_plane :
    ∃ K : ℝ, 0 < K ∧ ∀ t u : ℝ, 1 ≤ t → 120021 ≤ u →
      RiemannEvenRealSaddle.phaseSlope 3 t u = 0 → ∀ z : ℂ,
        K*realScale u ≤ z.re → flow 3 t z = 0 →
          z.im = 0 ∧ deriv (flow 3 t) z ≠ 0 := by
  obtain ⟨K₁,hK₁,hstrip⟩ := uniform_actual_far_unit_strip
  obtain ⟨K₂,hK₂,hoff⟩ := RiemannSixthComplexReflectedDominance.uniform_actual_nonzero_off_axis
  refine ⟨max K₁ K₂,hK₁.trans_le (le_max_left _ _),?_⟩
  intro t u ht hu hstat z hcut hzero
  have hB : 0 ≤ realScale u := (realScale_pos u).le
  by_cases him : |z.im| < 1
  · exact hstrip t u ht hu hstat z
      ((mul_le_mul_of_nonneg_right (le_max_left _ _) hB).trans hcut) him hzero
  · exfalso
    exact hoff t u ht hu hstat z
      (((mul_le_mul_of_nonneg_right (le_max_right _ _) hB).trans hcut).trans (Complex.re_le_norm z))
      (le_of_not_gt him) hzero

theorem uniform_actual_far_zeros_real_simple :
    ∃ K : ℝ, 0 < K ∧ ∀ t u : ℝ, 1 ≤ t → 120021 ≤ u →
      RiemannEvenRealSaddle.phaseSlope 3 t u = 0 → ∀ z : ℂ,
        K*realScale u ≤ ‖z‖ → flow 3 t z = 0 →
          z.im = 0 ∧ deriv (flow 3 t) z ≠ 0 := by
  obtain ⟨K₁,hK₁,hright⟩ := uniform_actual_far_right_half_plane
  obtain ⟨K₂,hK₂,hoff⟩ := RiemannSixthComplexReflectedDominance.uniform_actual_nonzero_off_axis
  let M := max 1 (max K₁ K₂)
  have hM : 1 ≤ M := le_max_left _ _
  have hK₁M : K₁ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hK₂M : K₂ ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨M+1,by linarith,?_⟩
  intro t u ht hu hstat z hcut hzero
  have hB : 1 ≤ realScale u := by
    unfold realScale
    have he : 1 ≤ Real.exp (4*u) := Real.one_le_exp (by linarith)
    nlinarith [Real.pi_gt_three]
  have hB0 : 0 ≤ realScale u := by linarith
  by_cases him : |z.im| < 1
  · have hn := Complex.norm_le_abs_re_add_abs_im z
    have hcoef := mul_le_mul_of_nonneg_right hK₁M hB0
    have hre : K₁*realScale u ≤ |z.re| := by nlinarith
    rcases le_total 0 z.re with hpos | hneg
    · rw [abs_of_nonneg hpos] at hre
      exact hright t u ht hu hstat z hre hzero
    · rw [abs_of_nonpos hneg] at hre
      have hzneg : flow 3 t (-z) = 0 := by rw [RiemannEvenEvolution.flow_even,hzero]
      have h := hright t u ht hu hstat (-z) (by simpa using hre) hzneg
      refine ⟨by simpa using h.1,?_⟩
      simpa only [deriv_even_flow_neg,neg_ne_zero] using h.2
  · exfalso
    have hco : K₂ ≤ M+1 := by linarith
    exact hoff t u ht hu hstat z
      ((mul_le_mul_of_nonneg_right hco hB0).trans hcut) (le_of_not_gt him) hzero

theorem eventually_uniform_actual_far_zeros_real_simple :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ t : ℝ in atTop, ∀ u ∈ Ici (0 : ℝ),
      IsMaxOn (RiemannEvenDomain.weighted 3 0 t 0) (Ici 0) u → ∀ z : ℂ,
        K*realScale u ≤ ‖z‖ → flow 3 t z = 0 →
          z.im = 0 ∧ deriv (flow 3 t) z ≠ 0 := by
  obtain ⟨K,hK,h⟩ := uniform_actual_far_zeros_real_simple
  refine ⟨K,hK,?_⟩
  filter_upwards [RiemannEvenRealSaddle.maxima_escape 3 (by norm_num) 120021 (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with t he ht
  intro u hu hm z hz hzero
  have hul := he u hu hm
  have hs := RiemannEvenRealSaddle.max_real_stationary 3 t u (by linarith) hm
  exact h t u ht hul.le hs z hz hzero

theorem eventually_far_zeros_real_simple :
    ∀ᶠ t : ℝ in atTop, ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ,
      R ≤ ‖z‖ → flow 3 t z = 0 → z.im = 0 ∧ deriv (flow 3 t) z ≠ 0 := by
  obtain ⟨K,hK,h⟩ := eventually_uniform_actual_far_zeros_real_simple
  filter_upwards [h] with t ht
  obtain ⟨u,hu,hm⟩ := RiemannEvenRealSaddle.exists_global_max 3 t
  refine ⟨K*realScale u,mul_pos hK (realScale_pos u),?_⟩
  exact ht u hu hm

end OperatorDerivativeRewrite.Foundation.RiemannSixthFarZeroControl
