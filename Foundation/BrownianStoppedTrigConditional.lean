import Foundation.BrownianStoppedFourier

/-! Actual conditional trigonometric observations after a bounded stopping time.
The random time weight is cancelled using conditional pull-out, with integrability. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianStoppedTrigConditional
open InfiniteGaussian IBMConstructedSources BrownianMassClockStoppingTime
open BrownianFourierMartingales BrownianStoppedFourier
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath

theorem weight_positive (u t : ℝ) : 0 < weight u t := Real.exp_pos _

theorem weight_add (u s t : ℝ) : weight u (s+t) = weight u s*weight u t := by
  unfold weight
  rw [← Real.exp_add]
  congr 1
  ring

theorem weight_monotone (u : ℝ) : Monotone (weight u) := by
  intro s t hst
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg u]

def decay (u : ℝ) (h : ℝ≥0) : ℝ := (weight u h)⁻¹

theorem decay_eq (u : ℝ) (h : ℝ≥0) : decay u h = Real.exp (-(u^2*(h : ℝ)/2)) := by
  rw [decay,weight,Real.exp_neg]

theorem cancel_weight (u s t z : ℝ) :
    (weight u (s+t))⁻¹*(weight u s*z) = (weight u t)⁻¹*z := by
  rw [weight_add,mul_inv_rev,mul_assoc,
    inv_mul_cancel_left₀ (ne_of_gt (weight_positive u s))]

variable (τ : SampleSpace → ℝ≥0)
  (hτ : IsStoppingTime augmentedPast (fun ω => (τ ω : WithTop ℝ≥0)))

theorem unweight_conditional (u : ℝ) (h : ℝ≥0) (N : ℕ) (hN : ∀ ω, τ ω ≤ N)
    (f : ℝ → ℝ) (hf : Continuous f) (hb : ∀ x, ‖f x‖ ≤ 1)
    (hsam : gaussianProduct[(fun ω => weight u (τ ω+h)*f (clockPath ω (τ ω+h))) |
      hτ.measurableSpace] =ᵐ[gaussianProduct] (fun ω => weight u (τ ω)*f (clockPath ω (τ ω)))) :
    gaussianProduct[(fun ω => f (clockPath ω (τ ω+h))) | hτ.measurableSpace]
      =ᵐ[gaussianProduct] (fun ω => decay u h*f (clockPath ω (τ ω))) := by
  let R : SampleSpace → ℝ := fun ω => (weight u (τ ω+h))⁻¹
  let Y : SampleSpace → ℝ := fun ω => weight u (τ ω+h)*f (clockPath ω (τ ω+h))
  have ht := time_measurable augmentedPast τ hτ
  have hta : Measurable τ := ht.mono hτ.measurableSpace_le le_rfl
  have hR : StronglyMeasurable[hτ.measurableSpace] R :=
    (((weight_smooth u).continuous.measurable.comp
      (continuous_subtype_val.measurable.comp (ht.add_const h))).inv).stronglyMeasurable
  have hY : Measurable Y :=
    (((weight_smooth u).continuous.measurable.comp
      (continuous_subtype_val.measurable.comp (hta.add_const h))).mul
      (hf.measurable.comp (shifted_brownian_measurable τ hτ h)))
  have hYi : Integrable Y gaussianProduct := by
    apply Integrable.of_bound hY.aestronglyMeasurable (weight u ((N : ℝ)+(h : ℝ)))
    exact Eventually.of_forall (fun ω => by
      change ‖weight u (τ ω+h)*f (clockPath ω (τ ω+h))‖ ≤ _
      rw [norm_mul,Real.norm_eq_abs,abs_of_pos (weight_positive _ _)]
      apply (mul_le_of_le_one_right (le_of_lt (weight_positive _ _)) (hb _)).trans
      apply weight_monotone u
      exact_mod_cast add_le_add (hN ω) (le_refl h))
  have hfi : Integrable (fun ω => f (clockPath ω (τ ω+h))) gaussianProduct :=
    Integrable.of_bound (hf.measurable.comp
      (shifted_brownian_measurable τ hτ h)).aestronglyMeasurable 1
      (Eventually.of_forall (fun ω => hb _))
  have he : R*Y = (fun ω => f (clockPath ω (τ ω+h))) := by
    funext ω
    exact inv_mul_cancel_left₀ (ne_of_gt (weight_positive _ _)) _
  have hp := condExp_mul_of_stronglyMeasurable_left hR
    (show Integrable (R*Y) gaussianProduct by rw [he]; exact hfi) hYi
  rw [he] at hp
  apply hp.trans
  filter_upwards [hsam] with ω hω
  change R ω*gaussianProduct[Y | hτ.measurableSpace] ω = _
  rw [hω]
  change (weight u (τ ω+h))⁻¹*(weight u (τ ω)*f (clockPath ω (τ ω))) = _
  rw [cancel_weight]
  rfl

theorem cosine_conditional (u : ℝ) (h : ℝ≥0) (N : ℕ) (hN : ∀ ω, τ ω ≤ N) :
    gaussianProduct[(fun ω => cosine u (clockPath ω (τ ω+h))) | hτ.measurableSpace]
      =ᵐ[gaussianProduct] (fun ω => decay u h*cosine u (clockPath ω (τ ω))) :=
  unweight_conditional τ hτ u h N hN (cosine u) (cosine_smooth u).continuous
    (fun x => by simpa only [one_mul,norm_one] using cosine_bound 1 u x)
    (cosine_sampling τ hτ u h N hN)

theorem sine_conditional (u : ℝ) (h : ℝ≥0) (N : ℕ) (hN : ∀ ω, τ ω ≤ N) :
    gaussianProduct[(fun ω => sine u (clockPath ω (τ ω+h))) | hτ.measurableSpace]
      =ᵐ[gaussianProduct] (fun ω => decay u h*sine u (clockPath ω (τ ω))) :=
  unweight_conditional τ hτ u h N hN (sine u) (sine_smooth u).continuous
    (fun x => by simpa only [one_mul,norm_one] using sine_bound 1 u x)
    (sine_sampling τ hτ u h N hN)

end OperatorDerivativeRewrite.Foundation.BrownianStoppedTrigConditional
