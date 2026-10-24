import Foundation.IBMSchwartzHeatDerivative

/-! Actual Bochner Gaussian heat and score semigroup laws for the nonlinear
IBM source curve. The score law follows by justified differentiation of the
value semigroup, not by assuming a time heat equation or native reconstruction. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzHeatSemigroup
open InfiniteGaussian IBMSchwartzHalfHolderHeat IBMSchwartzHeatDerivative
attribute [local irreducible] curve GaussianHalfHolderScore.score GaussianBoundedHeatDerivative.mean

theorem heatMean_bound (g : SchwartzMap ℝ ℝ) (a b v : ℝ) :
    ‖heatMean g a b v‖ ≤ SchwartzMap.seminorm ℝ 0 0 g := by
  have hi := GaussianBoundedHeatDerivative.mean_integrable (curve g a) (curve_continuous g a)
    (SchwartzMap.seminorm ℝ 0 0 g) (curve_bound g a) b (Real.sqrt v)
  unfold heatMean GaussianBoundedHeatDerivative.mean
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ _ : ℝ, SchwartzMap.seminorm ℝ 0 0 g ∂GaussianCore.γ :=
      integral_mono hi.norm (integrable_const _) (fun z => curve_bound g a _)
    _ = _ := by simp

theorem heatScore_norm (g : SchwartzMap ℝ ℝ) (a b v : ℝ) (hv : 0 < v) :
    ‖heatScore g a b v‖ ≤
      (constant g*GaussianHalfHolderScore.mass)/Real.sqrt (Real.sqrt v) :=
  GaussianHalfHolderScore.score_norm (curve g a) (curve_continuous g a)
    (constant g) (constant_nonneg g) (curve_holder g a) b (Real.sqrt v) (Real.sqrt_pos.mpr hv)

theorem value_semigroup (g : SchwartzMap ℝ ℝ) (a b : ℝ) (u v : ℝ≥0) :
    (∫ x, heatMean g a (b+x) v ∂gaussianReal 0 u) = heatMean g a b (u+v) := by
  let μ := gaussianReal 0 u
  let ν := gaussianReal 0 v
  have hi : Integrable (fun z : ℝ × ℝ => curve g a (b+z.1+z.2)) (μ.prod ν) := by
    apply (integrable_const (SchwartzMap.seminorm ℝ 0 0 g)).mono'
      ((curve_continuous g a).comp
        ((continuous_const.add continuous_fst).add continuous_snd)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun z => curve_bound g a _
  have hmap : (μ.prod ν).map (fun z : ℝ × ℝ => z.1+z.2) = gaussianReal 0 (u+v) := by
    change Measure.conv (gaussianReal 0 u) (gaussianReal 0 v) = _
    simpa only [zero_add] using (gaussianReal_conv_gaussianReal
      (m₁ := 0) (m₂ := 0) (v₁ := u) (v₂ := v))
  have hf : AEStronglyMeasurable (fun r : ℝ => curve g a (b+r))
      ((μ.prod ν).map (fun z : ℝ × ℝ => z.1+z.2)) :=
    ((curve_continuous g a).comp
      ((continuous_const : Continuous (fun _ : ℝ => b)).add continuous_id)).aestronglyMeasurable
  have hm := integral_map
    (show AEMeasurable (fun z : ℝ × ℝ => z.1+z.2) (μ.prod ν) from by fun_prop) hf
  rw [hmap] at hm
  calc
    _ = ∫ x, ∫ y, curve g a (b+x+y) ∂ν ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => heatMean_gaussian g a (b+x) v
    _ = ∫ z : ℝ × ℝ, curve g a (b+z.1+z.2) ∂μ.prod ν := (integral_prod _ hi).symm
    _ = ∫ r, curve g a (b+r) ∂gaussianReal 0 (u+v) := by
      simpa only [Function.comp_def,add_assoc] using hm.symm
    _ = _ := (heatMean_gaussian g a b (u+v)).symm

theorem gradient_semigroup (g : SchwartzMap ℝ ℝ) (a b : ℝ) (u v : ℝ≥0) (hv : 0 < v) :
    (∫ x, heatScore g a (b+x) v ∂gaussianReal 0 u) = heatScore g a b (u+v) := by
  let F : ℝ → ℝ → InfiniteGaussian.GaussianL2 := fun t x => heatMean g a (t+x) v
  let D : ℝ → ℝ → InfiniteGaussian.GaussianL2 := fun t x => heatScore g a (t+x) v
  let B : ℝ := (constant g*GaussianHalfHolderScore.mass)/Real.sqrt (Real.sqrt v)
  have hmeas (t : ℝ) : AEStronglyMeasurable (F t) (gaussianReal 0 u) :=
    ((heatMean_continuous g a).comp
      (((continuous_const : Continuous (fun _ : ℝ => t)).add continuous_id).prodMk
        continuous_const)).aestronglyMeasurable
  have hint : Integrable (F b) (gaussianReal 0 u) :=
    (integrable_const (SchwartzMap.seminorm ℝ 0 0 g)).mono' (hmeas b)
      (Filter.Eventually.of_forall fun x => heatMean_bound g a _ _)
  have hdmeas : AEStronglyMeasurable (D b) (gaussianReal 0 u) :=
    ((heatScore_stronglyMeasurable g a).comp_measurable
      (((measurable_const : Measurable (fun _ : ℝ => b)).add measurable_id).prodMk
        measurable_const)).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂gaussianReal 0 u, ∀ t ∈ (univ : Set ℝ), ‖D t x‖ ≤ B :=
    Filter.Eventually.of_forall fun x t _ => heatScore_norm g a _ _ hv
  have hdiff : ∀ᵐ x ∂gaussianReal 0 u, ∀ t ∈ (univ : Set ℝ),
      HasDerivAt (fun s => F s x) (D t x) t := by
    filter_upwards with x t _
    have hd := heatMean_hasDerivAt g a (t+x) v hv
    simpa only [Function.comp_def, id_eq, one_smul, F, D] using
      hd.scomp t ((hasDerivAt_id t).add_const x)
  obtain ⟨_,hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := D) (μ := gaussianReal 0 u) (s := univ) (x₀ := b)
    Filter.univ_mem (Filter.Eventually.of_forall hmeas) hint hdmeas hbound (integrable_const B) hdiff
  have he : (fun t => ∫ x, F t x ∂gaussianReal 0 u) = fun t => heatMean g a t (u+v) :=
    funext fun t => value_semigroup g a t u v
  rw [he] at hd
  exact hd.unique (heatMean_hasDerivAt g a b (u+v) (by
    have hv' : (0 : ℝ) < v := hv
    positivity))

end OperatorDerivativeRewrite.Foundation.IBMSchwartzHeatSemigroup
