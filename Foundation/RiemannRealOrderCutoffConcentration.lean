import Foundation.RiemannRealOrderCutoffBoundary

/-! The actual cutoff concentrates at the endpoint in Lipschitz tests.
At nonzero time it does not vanish in L1 and admits no common integrable dominator near order one. -/
noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderCutoffConcentration
open RiemannRealOrderFractionalJets RiemannRealOrderFractionalRemainder
open RiemannRealOrderCutoffBoundary

theorem cutoff_pointwise_tendsto_zero (t u : ℝ) (hu : 0 < u) :
    Tendsto (fun a : ℝ => cutoff a t u) (𝓝 1) (𝓝 0) := by
  have hf : Continuous (fun a : ℝ => falling (2*a) 3) := by
    simp only [falling,Finset.prod_range_succ,Finset.prod_range_zero]
    fun_prop
  have hp : Continuous (fun a : ℝ => u^(2*a-3)) :=
    (Real.continuous_const_rpow hu.ne').comp (by fun_prop)
  have hc : Continuous (fun a : ℝ => ((t*falling (2*a) 3*RiemannQuarticKernel.kernel 0*
      u^(2*a-3)*Real.exp (-u) : ℝ) : ℂ)) := by fun_prop
  have he : (fun a : ℝ => cutoff a t u)=(fun a : ℝ =>
      ((t*falling (2*a) 3*RiemannQuarticKernel.kernel 0*u^(2*a-3)*Real.exp (-u) : ℝ) : ℂ)) := by
    funext a
    exact cutoff_real a t u hu.le
  rw [he]
  simpa [falling,Finset.prod_range_succ] using hc.tendsto 1

theorem cutoff_norm_not_tendsto_zero (t : ℝ) (ht : t ≠ 0) :
    ¬ Tendsto (fun a : ℝ => ∫ u : ℝ in Ioi 0, ‖cutoff a t u‖) (𝓝[>] 1) (𝓝 0) := by
  intro h
  have hm : 2*t*RiemannQuarticKernel.kernel 0 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) ht)
      (RiemannQuarticKernel.kernel_pos 0 (by norm_num)).ne'
  exact (abs_ne_zero.mpr hm) (tendsto_nhds_unique (cutoff_norm_integral_tendsto t) h)

theorem no_common_integrable_majorant (t : ℝ) (ht : t ≠ 0) :
    ¬ ∃ δ : ℝ, 0 < δ ∧ ∃ g : ℝ → ℝ, IntegrableOn g (Ioi 0) ∧
      ∀ a : ℝ, 1 < a → a < 1+δ →
        ∀ᵐ u : ℝ ∂volume.restrict (Ioi 0), ‖cutoff a t u‖ ≤ g u := by
  rintro ⟨δ,hδ,g,hg,hB⟩
  have hmeas : ∀ᶠ a : ℝ in 𝓝[>] 1,
      AEStronglyMeasurable (cutoff a t) (volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact (cutoff_integrable a t ha).aestronglyMeasurable
  have hu : ∀ᶠ a : ℝ in 𝓝 (1 : ℝ), a < 1+δ := Iio_mem_nhds (by linarith)
  have hbound : ∀ᶠ a : ℝ in 𝓝[>] 1,
      ∀ᵐ u : ℝ ∂volume.restrict (Ioi 0), ‖cutoff a t u‖ ≤ g u := by
    filter_upwards [self_mem_nhdsWithin,hu.filter_mono nhdsWithin_le_nhds] with a ha hau
    exact hB a ha hau
  have hpoint : ∀ᵐ u : ℝ ∂volume.restrict (Ioi 0),
      Tendsto (fun a : ℝ => cutoff a t u) (𝓝[>] 1) (𝓝 (0 : ℂ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (cutoff_pointwise_tendsto_zero t u hu).mono_left nhdsWithin_le_nhds
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ))) (F := fun a u => cutoff a t u) (f := fun _ => (0 : ℂ))
    g hmeas hbound hg hpoint
  have hzero : Tendsto (fun a : ℝ => ∫ u : ℝ in Ioi 0, cutoff a t u)
      (𝓝[>] 1) (𝓝 (0 : ℂ)) := by simpa only [integral_zero] using hlim
  have hm : ((2*t*RiemannQuarticKernel.kernel 0 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) ht)
      (RiemannQuarticKernel.kernel_pos 0 (by norm_num)).ne')
  exact hm (tendsto_nhds_unique (cutoff_integral_tendsto t) hzero)

private theorem error_bound (a t u : ℝ) (hu : 0 < u) (L : NNReal) (f : ℝ → ℂ)
    (hf : LipschitzWith L f) :
    ‖cutoff a t u*(f u-f 0)‖ ≤ (L : ℝ)*(u*‖cutoff a t u‖) := by
  have hh : ‖f u-f 0‖ ≤ (L : ℝ)*u := by
    simpa only [dist_eq_norm,sub_zero,Real.norm_eq_abs,abs_of_pos hu] using hf.dist_le_mul u 0
  rw [norm_mul]
  calc
    _ ≤ ‖cutoff a t u‖*((L : ℝ)*u) := mul_le_mul_of_nonneg_left hh (norm_nonneg _)
    _ = _ := by ring

theorem cutoff_lipschitz_error_integrable (a t : ℝ) (ha : 1 < a) (L : NNReal)
    (f : ℝ → ℂ) (hf : LipschitzWith L f) :
    IntegrableOn (fun u : ℝ => cutoff a t u*(f u-f 0)) (Ioi 0) := by
  have hi := (cutoff_norm_moment_integrable a t ha).const_mul (L : ℝ)
  apply hi.mono' ((cutoff_integrable a t ha).aestronglyMeasurable.mul
    ((hf.continuous.sub continuous_const).aestronglyMeasurable))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact error_bound a t u hu L f hf

theorem cutoff_lipschitz_integrable (a t : ℝ) (ha : 1 < a) (L : NNReal)
    (f : ℝ → ℂ) (hf : LipschitzWith L f) :
    IntegrableOn (fun u : ℝ => cutoff a t u*f u) (Ioi 0) := by
  apply ((cutoff_lipschitz_error_integrable a t ha L f hf).add
    ((cutoff_integrable a t ha).mul_const (f 0))).congr
  filter_upwards with u
  simp only [Pi.add_apply]
  ring

theorem cutoff_lipschitz_error_bound (a t : ℝ) (ha : 1 < a) (L : NNReal)
    (f : ℝ → ℂ) (hf : LipschitzWith L f) :
    ‖(∫ u : ℝ in Ioi 0, cutoff a t u*f u)-(mass a t : ℂ)*f 0‖ ≤
      (L : ℝ)*(∫ u : ℝ in Ioi 0, u*‖cutoff a t u‖) := by
  have he : (∫ u : ℝ in Ioi 0, cutoff a t u*f u)-(mass a t : ℂ)*f 0=
      ∫ u : ℝ in Ioi 0, cutoff a t u*(f u-f 0) := by
    rw [← cutoff_integral a t ha,← integral_mul_const,← integral_sub
      (cutoff_lipschitz_integrable a t ha L f hf) ((cutoff_integrable a t ha).mul_const (f 0))]
    apply integral_congr_ae
    filter_upwards with u
    ring
  rw [he,← integral_const_mul]
  apply norm_integral_le_of_norm_le ((cutoff_norm_moment_integrable a t ha).const_mul (L : ℝ))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact error_bound a t u hu L f hf

theorem cutoff_lipschitz_tendsto (t : ℝ) (L : NNReal) (f : ℝ → ℂ) (hf : LipschitzWith L f) :
    Tendsto (fun a : ℝ => ∫ u : ℝ in Ioi 0, cutoff a t u*f u) (𝓝[>] 1)
      (𝓝 (((2*t*RiemannQuarticKernel.kernel 0 : ℝ) : ℂ)*f 0)) := by
  have herror : Tendsto (fun a : ℝ => (∫ u : ℝ in Ioi 0, cutoff a t u*f u)-
      (mass a t : ℂ)*f 0) (𝓝[>] 1) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      ((show ∀ᶠ a : ℝ in 𝓝[>] 1, 1 < a from self_mem_nhdsWithin).mono fun a ha => cutoff_lipschitz_error_bound a t ha L f hf)
      (by simpa only [mul_zero] using (cutoff_first_moment_tendsto_zero t).const_mul (L : ℝ))
  have hmass : Tendsto (fun a : ℝ => (mass a t : ℂ)*f 0) (𝓝[>] 1)
      (𝓝 (((2*t*RiemannQuarticKernel.kernel 0 : ℝ) : ℂ)*f 0)) := by
    have h := (Complex.continuous_ofReal.continuousAt.comp (mass_continuousAt_one t)).tendsto.mul_const (f 0)
    simpa only [Function.comp_def,mass_one] using h.mono_left nhdsWithin_le_nhds
  simpa only [sub_add_cancel,zero_add] using herror.add hmass

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderCutoffConcentration
