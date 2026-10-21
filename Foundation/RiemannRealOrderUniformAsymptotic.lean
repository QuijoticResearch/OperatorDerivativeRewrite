import Foundation.RiemannRealOrderUniformTail

/-! Uniform absolute Fourier asymptotics for the actual fractional Xi flow.
The leading coefficient vanishes at the quadratic endpoint; there is no
division by it and no relative or zero-localization conclusion. -/
noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderUniformAsymptotic
open RiemannRealOrderFractionalJets RiemannRealOrderFractionalFourier
open RiemannRealOrderFractionalReconstruction RiemannRealOrderUniformTail
open RiemannRealOrderUniformCutoff RiemannRealOrderFractionalCoefficient

theorem scaled_remainder_uniform_bound (t : ℝ) : ∃ M : ℝ, 0 ≤ M ∧
    ∀ a : ℝ, 1 < a → a ≤ 5/4 → ∀ x : ℝ, 1 ≤ x →
      ‖((x^(2*a-2) : ℝ) : ℂ)*sineRemainder a t x‖ ≤ M*x^(-(1/2 : ℝ)) := by
  obtain ⟨M,hM,hbound⟩ := remainder_derivative_uniform_integral t
  refine ⟨M,hM,?_⟩
  intro a ha ha5 x hx
  have hx0 : 0 < x := by linarith
  have hs : x*‖sineRemainder a t x‖ ≤ M := by
    have h := (sineRemainder_norm_bound a t x ha (by linarith)).trans (hbound a ha ha5)
    simpa only [abs_of_pos hx0] using h
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
  calc
    _ = x^((2*a-2)-1)*(x*‖sineRemainder a t x‖) := by
      rw [Real.rpow_sub_one hx0.ne']
      field_simp
    _ ≤ x^((2*a-2)-1)*M :=
      mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hx0.le _)
    _ ≤ x^(-(1/2 : ℝ))*M :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hx (by linarith)) hM
    _ = _ := by ring

theorem scaled_remainder_uniform_limit (t : ℝ) :
    TendstoUniformlyOn (fun x a : ℝ => ((x^(2*a-2) : ℝ) : ℂ)*sineRemainder a t x)
      (fun _ : ℝ => (0 : ℂ)) atTop (Ioc 1 (5/4)) := by
  obtain ⟨M,hM,hbound⟩ := scaled_remainder_uniform_bound t
  have ht : Tendsto (fun x : ℝ => M*x^(-(1/2 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)).const_mul M
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(tendsto_order.1 ht).2 ε hε,eventually_ge_atTop (1 : ℝ)] with x he hx
  intro a ha
  rw [dist_zero_left]
  exact (hbound a ha.1 ha.2 x hx).trans_lt he

theorem actual_scaled_decomposition (a t x : ℝ) (ha : 1 < a) (ha5 : a ≤ 5/4)
    (hx : 0 < x) :
    ((x^(2*a+1) : ℝ) : ℂ)*RiemannRealOrderFlow.flow a t (x : ℂ)=
      ((x^(2*a-2) : ℝ) : ℂ)*sineRemainder a t x+
        ((x^(2*a-2) : ℝ) : ℂ)*(∫ u : ℝ in Ioi 0, cutoff a t u*(Real.sin (x*u) : ℂ)) := by
  have hd := thirdSine_decomposition a t x ha (by linarith)
  rw [← cutoff_sine_eq] at hd
  rw [← mul_add,← hd,← actual_third_identity a t x ha (by linarith),
    show 2*a+1=(2*a-2)+3 by ring,Real.rpow_add hx]
  have hp : x^(3 : ℝ)=x^(3 : ℕ) := Real.rpow_natCast x 3
  rw [hp]
  push_cast
  ring

theorem actual_flow_uniform_scaled_limit (t : ℝ) :
    TendstoUniformlyOn (fun x a : ℝ =>
      ((x^(2*a+1) : ℝ) : ℂ)*RiemannRealOrderFlow.flow a t (x : ℂ))
      (fun a : ℝ => (leading a t : ℂ)) atTop (Ioc 1 (5/4)) := by
  have h := (scaled_remainder_uniform_limit t).add (cutoff_sine_uniform_scaled_limit t)
  have hh : TendstoUniformlyOn (fun x a : ℝ =>
      ((x^(2*a-2) : ℝ) : ℂ)*sineRemainder a t x+
        ((x^(2*a-2) : ℝ) : ℂ)*(∫ u : ℝ in Ioi 0, cutoff a t u*(Real.sin (x*u) : ℂ)))
      (fun a : ℝ => (leading a t : ℂ)) atTop (Ioc 1 (5/4)) := by
    simpa only [Pi.add_def,zero_add] using h
  apply hh.congr
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  intro a ha
  exact (actual_scaled_decomposition a t x ha.1 ha.2 hx).symm

theorem actual_flow_diagonal_error (t : ℝ) (a x : ℕ → ℝ)
    (hx : Tendsto x atTop atTop) (ha : ∀ᶠ n : ℕ in atTop, a n ∈ Ioc 1 (5/4)) :
    Tendsto (fun n : ℕ => ((x n^(2*a n+1) : ℝ) : ℂ)*
      RiemannRealOrderFlow.flow (a n) t (x n : ℂ)-(leading (a n) t : ℂ)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hu := (Metric.tendstoUniformlyOn_iff.mp (actual_flow_uniform_scaled_limit t)) ε hε
  filter_upwards [hx.eventually hu,ha] with n hn han
  have h := hn (a n) han
  rw [dist_zero_right,dist_eq_norm] at *
  rwa [norm_sub_rev]

theorem actual_flow_diagonal_endpoint_limit (t : ℝ) (a x : ℕ → ℝ)
    (hx : Tendsto x atTop atTop) (ha : ∀ᶠ n : ℕ in atTop, a n ∈ Ioc 1 (5/4))
    (ha1 : Tendsto a atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => ((x n^(2*a n+1) : ℝ) : ℂ)*
      RiemannRealOrderFlow.flow (a n) t (x n : ℂ)) atTop (𝓝 0) := by
  have hl : Tendsto (fun n : ℕ => (leading (a n) t : ℂ)) atTop (𝓝 0) := by
    simpa only [Complex.ofReal_zero,Function.comp_def] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp ((leading_tendsto_zero t).comp ha1)
  simpa only [sub_add_cancel,zero_add] using (actual_flow_diagonal_error t a x hx ha).add hl

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderUniformAsymptotic
