import Foundation.BrownianStoppedTrigConditional

/-! Conditional characteristic-function components of the actual Brownian
increment after a bounded stopping time, proved by optional sampling and rotation. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianStoppedIncrementFourier
open InfiniteGaussian IBMConstructedSources BrownianMassClockStoppingTime
open BrownianFourierMartingales BrownianStoppedFourier BrownianStoppedTrigConditional
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath

def increment (τ : SampleSpace → ℝ≥0) (h : ℝ≥0) (ω : SampleSpace) : ℝ :=
  clockPath ω (τ ω+h)-clockPath ω (τ ω)

variable (τ : SampleSpace → ℝ≥0)
  (hτ : IsStoppingTime augmentedPast (fun ω => (τ ω : WithTop ℝ≥0)))

include hτ in
theorem increment_measurable (h : ℝ≥0) : Measurable (increment τ h) :=
  (shifted_brownian_measurable τ hτ h).sub
    ((brownian_at_stop_measurable τ hτ).mono hτ.measurableSpace_le le_rfl)

theorem cosine_increment_conditional (u : ℝ) (h : ℝ≥0) (N : ℕ) (hN : ∀ ω, τ ω ≤ N) :
    gaussianProduct[(fun ω => cosine u (increment τ h ω)) | hτ.measurableSpace]
      =ᵐ[gaussianProduct] (fun _ => decay u h) := by
  let c : SampleSpace → ℝ := fun ω => cosine u (clockPath ω (τ ω))
  let s : SampleSpace → ℝ := fun ω => sine u (clockPath ω (τ ω))
  let C : SampleSpace → ℝ := fun ω => cosine u (clockPath ω (τ ω+h))
  let S : SampleSpace → ℝ := fun ω => sine u (clockPath ω (τ ω+h))
  have hc : StronglyMeasurable[hτ.measurableSpace] c :=
    ((cosine_smooth u).continuous.measurable.comp (brownian_at_stop_measurable τ hτ)).stronglyMeasurable
  have hs : StronglyMeasurable[hτ.measurableSpace] s :=
    ((sine_smooth u).continuous.measurable.comp (brownian_at_stop_measurable τ hτ)).stronglyMeasurable
  have hbcos (x : ℝ) : ‖cosine u x‖ ≤ 1 := by simpa only [one_mul,norm_one] using cosine_bound 1 u x
  have hbsin (x : ℝ) : ‖sine u x‖ ≤ 1 := by simpa only [one_mul,norm_one] using sine_bound 1 u x
  have hC : Integrable C gaussianProduct := Integrable.of_bound
    ((cosine_smooth u).continuous.measurable.comp (shifted_brownian_measurable τ hτ h)).aestronglyMeasurable
    1 (Eventually.of_forall (fun ω => hbcos _))
  have hS : Integrable S gaussianProduct := Integrable.of_bound
    ((sine_smooth u).continuous.measurable.comp (shifted_brownian_measurable τ hτ h)).aestronglyMeasurable
    1 (Eventually.of_forall (fun ω => hbsin _))
  have hCc : Integrable (C*c) gaussianProduct :=
    hC.mul_bdd (hc.mono hτ.measurableSpace_le).aestronglyMeasurable
      (Eventually.of_forall (fun ω => hbcos _))
  have hSs : Integrable (S*s) gaussianProduct :=
    hS.mul_bdd (hs.mono hτ.measurableSpace_le).aestronglyMeasurable
      (Eventually.of_forall (fun ω => hbsin _))
  have he : (fun ω => cosine u (increment τ h ω)) = C*c+S*s := by
    funext ω
    dsimp [cosine,sine,increment,C,c,S,s]
    rw [mul_sub,Real.cos_sub]
  rw [he]
  have hadd := condExp_add hCc hSs hτ.measurableSpace
  have hpC := condExp_mul_of_stronglyMeasurable_right hc hCc hC
  have hpS := condExp_mul_of_stronglyMeasurable_right hs hSs hS
  filter_upwards [hadd,hpC,hpS,cosine_conditional τ hτ u h N hN,
    sine_conditional τ hτ u h N hN] with ω ha hpc hps hfc hfs
  change gaussianProduct[C*c+S*s | hτ.measurableSpace] ω = _
  rw [ha]
  change gaussianProduct[C*c | hτ.measurableSpace] ω+
    gaussianProduct[S*s | hτ.measurableSpace] ω = _
  rw [hpc,hps]
  change gaussianProduct[C | hτ.measurableSpace] ω*c ω+
    gaussianProduct[S | hτ.measurableSpace] ω*s ω = _
  rw [hfc,hfs]
  have hsq : c ω^2+s ω^2 = 1 := Real.cos_sq_add_sin_sq _
  change (decay u h*c ω)*c ω+(decay u h*s ω)*s ω = decay u h
  calc
    _ = decay u h*(c ω^2+s ω^2) := by ring
    _ = _ := by rw [hsq,mul_one]

theorem sine_increment_conditional (u : ℝ) (h : ℝ≥0) (N : ℕ) (hN : ∀ ω, τ ω ≤ N) :
    gaussianProduct[(fun ω => sine u (increment τ h ω)) | hτ.measurableSpace]
      =ᵐ[gaussianProduct] (fun _ => (0 : ℝ)) := by
  let c : SampleSpace → ℝ := fun ω => cosine u (clockPath ω (τ ω))
  let s : SampleSpace → ℝ := fun ω => sine u (clockPath ω (τ ω))
  let C : SampleSpace → ℝ := fun ω => cosine u (clockPath ω (τ ω+h))
  let S : SampleSpace → ℝ := fun ω => sine u (clockPath ω (τ ω+h))
  have hc : StronglyMeasurable[hτ.measurableSpace] c :=
    ((cosine_smooth u).continuous.measurable.comp (brownian_at_stop_measurable τ hτ)).stronglyMeasurable
  have hs : StronglyMeasurable[hτ.measurableSpace] s :=
    ((sine_smooth u).continuous.measurable.comp (brownian_at_stop_measurable τ hτ)).stronglyMeasurable
  have hbcos (x : ℝ) : ‖cosine u x‖ ≤ 1 := by simpa only [one_mul,norm_one] using cosine_bound 1 u x
  have hbsin (x : ℝ) : ‖sine u x‖ ≤ 1 := by simpa only [one_mul,norm_one] using sine_bound 1 u x
  have hC : Integrable C gaussianProduct := Integrable.of_bound
    ((cosine_smooth u).continuous.measurable.comp (shifted_brownian_measurable τ hτ h)).aestronglyMeasurable
    1 (Eventually.of_forall (fun ω => hbcos _))
  have hS : Integrable S gaussianProduct := Integrable.of_bound
    ((sine_smooth u).continuous.measurable.comp (shifted_brownian_measurable τ hτ h)).aestronglyMeasurable
    1 (Eventually.of_forall (fun ω => hbsin _))
  have hSc : Integrable (S*c) gaussianProduct :=
    hS.mul_bdd (hc.mono hτ.measurableSpace_le).aestronglyMeasurable
      (Eventually.of_forall (fun ω => hbcos _))
  have hCs : Integrable (C*s) gaussianProduct :=
    hC.mul_bdd (hs.mono hτ.measurableSpace_le).aestronglyMeasurable
      (Eventually.of_forall (fun ω => hbsin _))
  have he : (fun ω => sine u (increment τ h ω)) = S*c-C*s := by
    funext ω
    dsimp [cosine,sine,increment,C,c,S,s]
    rw [mul_sub,Real.sin_sub]
  rw [he]
  have hsub := condExp_sub hSc hCs hτ.measurableSpace
  have hpS := condExp_mul_of_stronglyMeasurable_right hc hSc hS
  have hpC := condExp_mul_of_stronglyMeasurable_right hs hCs hC
  filter_upwards [hsub,hpS,hpC,sine_conditional τ hτ u h N hN,
    cosine_conditional τ hτ u h N hN] with ω ha hps hpc hfs hfc
  change gaussianProduct[S*c-C*s | hτ.measurableSpace] ω = _
  rw [ha]
  change gaussianProduct[S*c | hτ.measurableSpace] ω-
    gaussianProduct[C*s | hτ.measurableSpace] ω = _
  rw [hps,hpc]
  change gaussianProduct[S | hτ.measurableSpace] ω*c ω-
    gaussianProduct[C | hτ.measurableSpace] ω*s ω = _
  rw [hfs,hfc]
  change (decay u h*s ω)*c ω-(decay u h*c ω)*s ω = 0
  ring

end OperatorDerivativeRewrite.Foundation.BrownianStoppedIncrementFourier
