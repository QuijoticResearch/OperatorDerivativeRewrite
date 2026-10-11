import Foundation.GaussianSobolevQuantitative

/-! Global simultaneous Gaussian Sobolev graph approximation. -/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace OperatorDerivativeRewrite.Foundation.GaussianSobolevGlobalApprox

private theorem sq_sub_integrable {u v : ℝ → ℝ}
    (hu : MemLp u 2 GaussianCore.γ) (hv : MemLp v 2 GaussianCore.γ) :
    Integrable (fun x => (u x - v x) ^ 2) GaussianCore.γ := by
  exact (memLp_two_iff_integrable_sq (hu.sub hv).aestronglyMeasurable).1 (hu.sub hv)

private theorem sq_triangle_integral {u v w : ℝ → ℝ}
    (hu : MemLp u 2 GaussianCore.γ) (hv : MemLp v 2 GaussianCore.γ)
    (hw : MemLp w 2 GaussianCore.γ) :
    (∫ x, (u x - w x) ^ 2 ∂GaussianCore.γ) ≤
      2 * (∫ x, (u x - v x) ^ 2 ∂GaussianCore.γ) +
      2 * (∫ x, (v x - w x) ^ 2 ∂GaussianCore.γ) := by
  have huv := sq_sub_integrable hu hv
  have hvw := sq_sub_integrable hv hw
  calc
    (∫ x, (u x - w x) ^ 2 ∂GaussianCore.γ) ≤
        ∫ x, (2 * (u x - v x) ^ 2 + 2 * (v x - w x) ^ 2) ∂GaussianCore.γ := by
          apply integral_mono (sq_sub_integrable hu hw)
            ((huv.const_mul 2).add (hvw.const_mul 2))
          intro x
          change (u x - w x) ^ 2 ≤ 2 * (u x - v x) ^ 2 + 2 * (v x - w x) ^ 2
          nlinarith [sq_nonneg ((u x - v x) - (v x - w x))]
    _ = _ := by rw [integral_add (huv.const_mul 2) (hvw.const_mul 2)]
                simp only [integral_const_mul]

private theorem cutoff_graph_witness {f h : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (h x) x)
    (hf_sq : Integrable (fun x => f x ^ 2) GaussianCore.γ)
    (hh_sq : Integrable (fun x => h x ^ 2) GaussianCore.γ)
    (n : ℕ) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      (∫ x, (F x - GaussianSobolevCutoffs.truncated f n x) ^ 2 ∂GaussianCore.γ) <
        1 / ((n : ℝ) + 1) ∧
      (∫ x, (deriv F x - deriv (GaussianSobolevCutoffs.truncated f n) x) ^ 2
        ∂GaussianCore.γ) < 1 / ((n : ℝ) + 1) := by
  obtain ⟨R₀, hs₀⟩ := GaussianSobolevSmoothApprox.compact_support_in_Icc
    (GaussianSobolevCutoffs.truncated_compact f n)
  let R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  have hs : Function.support (GaussianSobolevCutoffs.truncated f n) ⊆ Icc (-R) R := by
    intro x hx
    have hx' := hs₀ hx
    exact ⟨by dsimp [R]; linarith [hx'.1, le_max_left R₀ 0],
      by dsimp [R]; linarith [hx'.2, le_max_left R₀ 0]⟩
  have hd' (x : ℝ) : HasDerivAt (GaussianSobolevCutoffs.truncated f n)
      (deriv (GaussianSobolevCutoffs.truncated f n) x) x := by
    convert GaussianSobolevCutoffs.hasDerivAt_truncated hd n x using 1
    exact GaussianSobolevCutoffs.deriv_truncated hd n x
  have hi := GaussianSobolevSmoothApprox.truncated_derivative_sq_integrable
    hd hf_sq hh_sq n
  exact GaussianSobolevFixedSupport.fixed_support_smooth_graph_approx R hR hd' hs hi
    (by positivity)

/-- An everywhere differentiable Gaussian Sobolev pair admits one sequence of
smooth compactly supported functions converging in both Gaussian `L²` graph
coordinates. The second coordinate is the actual derivative. -/
theorem exists_smooth_compact_graph_sequence {f h : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (h x) x)
    (hf_sq : Integrable (fun x => f x ^ 2) GaussianCore.γ)
    (hh_sq : Integrable (fun x => h x ^ 2) GaussianCore.γ) :
    ∃ F : ℕ → ℝ → ℝ,
      (∀ n, ContDiff ℝ ∞ (F n)) ∧
      (∀ n, HasCompactSupport (F n)) ∧
      Tendsto (fun n => ∫ x, (F n x - f x) ^ 2 ∂GaussianCore.γ) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ x, (deriv (F n) x - h x) ^ 2 ∂GaussianCore.γ)
        atTop (𝓝 0) := by
  let F : ℕ → ℝ → ℝ := fun n => Classical.choose (cutoff_graph_witness hd hf_sq hh_sq n)
  have hF (n : ℕ) := Classical.choose_spec (cutoff_graph_witness hd hf_sq hh_sq n)
  have hfcont : Continuous f := continuous_iff_continuousAt.mpr
    (fun x => (hd x).continuousAt)
  have hhMeas : Measurable h := by
    rw [GaussianLocalSobolev.derivative_eq_deriv hd]
    exact measurable_deriv f
  have hfLp : MemLp f 2 GaussianCore.γ :=
    (memLp_two_iff_integrable_sq hfcont.measurable.aestronglyMeasurable).2 hf_sq
  have hhLp : MemLp h 2 GaussianCore.γ :=
    (memLp_two_iff_integrable_sq hhMeas.aestronglyMeasurable).2 hh_sq
  have hgLp (n : ℕ) : MemLp (GaussianSobolevCutoffs.truncated f n) 2 GaussianCore.γ :=
    (((GaussianSobolevCutoffs.cutoff_contDiff n).continuous.mul hfcont)).memLp_of_hasCompactSupport
      (GaussianSobolevCutoffs.truncated_compact f n)
  have hkgLp (n : ℕ) : MemLp (deriv (GaussianSobolevCutoffs.truncated f n))
      2 GaussianCore.γ := by
    have hm : Measurable (deriv (GaussianSobolevCutoffs.truncated f n)) :=
      measurable_deriv _
    exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2
      (GaussianSobolevSmoothApprox.truncated_derivative_sq_integrable hd hf_sq hh_sq n)
  have hFLp (n : ℕ) : MemLp (F n) 2 GaussianCore.γ :=
    (hF n).1.continuous.memLp_of_hasCompactSupport (hF n).2.1
  have hDFLp (n : ℕ) : MemLp (deriv (F n)) 2 GaussianCore.γ :=
    ((hF n).1.continuous_deriv (by norm_num)).memLp_of_hasCompactSupport
      (hF n).2.1.deriv
  have hcut := GaussianSobolevCutoffs.simultaneous_sq_error_tendsto hd hf_sq hh_sq
  have hsmall : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨F, (fun n => (hF n).1), (fun n => (hF n).2.1), ?_, ?_⟩
  · have hupper : Tendsto (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1)) +
        2 * (∫ x, (GaussianSobolevCutoffs.truncated f n x - f x) ^ 2
          ∂GaussianCore.γ)) atTop (𝓝 0) := by
      simpa only [mul_zero, zero_add] using
        (hsmall.const_mul 2).add (hcut.1.const_mul 2)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    · intro n
      exact integral_nonneg (fun x => sq_nonneg _)
    · intro n
      exact (sq_triangle_integral (hFLp n) (hgLp n) hfLp).trans
        (add_le_add (mul_le_mul_of_nonneg_left (hF n).2.2.1.le (by norm_num)) le_rfl)
  · have hupper : Tendsto (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1)) +
        2 * (∫ x, (deriv (GaussianSobolevCutoffs.truncated f n) x - h x) ^ 2
          ∂GaussianCore.γ)) atTop (𝓝 0) := by
      simpa only [mul_zero, zero_add] using
        (hsmall.const_mul 2).add (hcut.2.const_mul 2)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    · intro n
      exact integral_nonneg (fun x => sq_nonneg _)
    · intro n
      exact (sq_triangle_integral (hDFLp n) (hkgLp n) hhLp).trans
        (add_le_add (mul_le_mul_of_nonneg_left (hF n).2.2.2.le (by norm_num)) le_rfl)

end OperatorDerivativeRewrite.Foundation.GaussianSobolevGlobalApprox
