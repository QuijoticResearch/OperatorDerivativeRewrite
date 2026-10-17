import Foundation.BrownianStoppedIncrementFourier
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-! Genuine Gaussian laws of Brownian increments after bounded stopping times,
including laws restricted to arbitrary events in the stopping sigma-algebra. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianStoppedIncrementLaw
open InfiniteGaussian IBMConstructedSources BrownianMassClockStoppingTime
open BrownianFourierMartingales BrownianStoppedFourier BrownianStoppedTrigConditional
open BrownianStoppedIncrementFourier
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath

theorem charFun_map_trig {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (X : Ω → ℝ) (hX : Measurable X) (u : ℝ) :
    charFun (μ.map X) u = ((∫ ω, cosine u (X ω) ∂μ : ℝ) : ℂ)+
      ((∫ ω, sine u (X ω) ∂μ : ℝ) : ℂ)*Complex.I := by
  have hc : Integrable (fun ω => cosine u (X ω)) μ :=
    Integrable.of_bound ((cosine_smooth u).continuous.measurable.comp hX).aestronglyMeasurable 1
      (Eventually.of_forall (fun ω => by simpa only [one_mul,norm_one] using cosine_bound 1 u (X ω)))
  have hs : Integrable (fun ω => sine u (X ω)) μ :=
    Integrable.of_bound ((sine_smooth u).continuous.measurable.comp hX).aestronglyMeasurable 1
      (Eventually.of_forall (fun ω => by simpa only [one_mul,norm_one] using sine_bound 1 u (X ω)))
  have hf : Continuous (fun x : ℝ => Complex.exp ((u : ℂ)*x*Complex.I)) := by fun_prop
  rw [charFun_apply_real,integral_map hX.aemeasurable hf.aestronglyMeasurable]
  have he (x : ℝ) : Complex.exp ((u : ℂ)*x*Complex.I) =
      (cosine u x : ℂ)+(sine u x : ℂ)*Complex.I := by
    simpa only [cosine,sine,Complex.ofReal_mul] using Complex.exp_ofReal_mul_I (u*x)
  simp_rw [he]
  have hc' : Integrable (fun ω => (cosine u (X ω) : ℂ)) μ := hc.ofReal
  have hs' : Integrable (fun ω => (sine u (X ω) : ℂ)*Complex.I) μ :=
    hs.ofReal.mul_const Complex.I
  calc
    _ = (∫ ω, (cosine u (X ω) : ℂ) ∂μ)+
        ∫ ω, (sine u (X ω) : ℂ)*Complex.I ∂μ := integral_add hc' hs'
    _ = _ := by rw [integral_mul_const,integral_complex_ofReal,integral_complex_ofReal]

theorem gaussian_charFun_decay (u : ℝ) (h : ℝ≥0) :
    charFun (gaussianReal 0 h) u = (decay u h : ℂ) := by
  rw [charFun_gaussianReal,decay_eq,Complex.ofReal_exp]
  congr 1
  push_cast
  ring

variable (τ : SampleSpace → ℝ≥0)
  (hτ : IsStoppingTime augmentedPast (fun ω => (τ ω : WithTop ℝ≥0)))

theorem cosine_event_integral (u : ℝ) (h : ℝ≥0) (N : ℕ) (hN : ∀ ω, τ ω ≤ N)
    (A : Set SampleSpace) (hA : MeasurableSet[hτ.measurableSpace] A) :
    (∫ ω in A, cosine u (increment τ h ω) ∂gaussianProduct) =
      gaussianProduct.real A*decay u h := by
  have hi : Integrable (fun ω => cosine u (increment τ h ω)) gaussianProduct :=
    Integrable.of_bound ((cosine_smooth u).continuous.measurable.comp
      (increment_measurable τ hτ h)).aestronglyMeasurable 1
      (Eventually.of_forall (fun ω => by simpa only [one_mul,norm_one] using cosine_bound 1 u _))
  calc
    _ = ∫ ω in A, gaussianProduct[(fun ω => cosine u (increment τ h ω)) |
        hτ.measurableSpace] ω ∂gaussianProduct :=
      (setIntegral_condExp hτ.measurableSpace_le hi hA).symm
    _ = ∫ _ in A, decay u h ∂gaussianProduct :=
      integral_congr_ae (ae_restrict_of_ae (cosine_increment_conditional τ hτ u h N hN))
    _ = _ := by simp only [setIntegral_const,smul_eq_mul,Measure.real]

theorem sine_event_integral (u : ℝ) (h : ℝ≥0) (N : ℕ) (hN : ∀ ω, τ ω ≤ N)
    (A : Set SampleSpace) (hA : MeasurableSet[hτ.measurableSpace] A) :
    (∫ ω in A, sine u (increment τ h ω) ∂gaussianProduct) = 0 := by
  have hi : Integrable (fun ω => sine u (increment τ h ω)) gaussianProduct :=
    Integrable.of_bound ((sine_smooth u).continuous.measurable.comp
      (increment_measurable τ hτ h)).aestronglyMeasurable 1
      (Eventually.of_forall (fun ω => by simpa only [one_mul,norm_one] using sine_bound 1 u _))
  calc
    _ = ∫ ω in A, gaussianProduct[(fun ω => sine u (increment τ h ω)) |
        hτ.measurableSpace] ω ∂gaussianProduct :=
      (setIntegral_condExp hτ.measurableSpace_le hi hA).symm
    _ = ∫ _ in A, (0 : ℝ) ∂gaussianProduct :=
      integral_congr_ae (ae_restrict_of_ae (sine_increment_conditional τ hτ u h N hN))
    _ = _ := by simp only [integral_zero]

theorem restricted_increment_law (h : ℝ≥0) (N : ℕ) (hN : ∀ ω, τ ω ≤ N)
    (A : Set SampleSpace) (hA : MeasurableSet[hτ.measurableSpace] A) :
    (gaussianProduct.restrict A).map (increment τ h) =
      gaussianProduct A • gaussianReal 0 h := by
  letI : IsFiniteMeasure (gaussianProduct A • gaussianReal 0 h) := ⟨by
    simp only [Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
    exact measure_lt_top _ _⟩
  apply Measure.ext_of_charFun
  funext u
  rw [charFun_map_trig _ _ (increment_measurable τ hτ h),
    cosine_event_integral τ hτ u h N hN A hA,sine_event_integral τ hτ u h N hN A hA]
  have he : charFun (gaussianProduct A • gaussianReal 0 h) u =
      (gaussianProduct A).toReal • charFun (gaussianReal 0 h) u := by
    rw [charFun_apply,integral_smul_measure]
    rfl
  rw [he,gaussian_charFun_decay]
  simp only [Measure.real,Complex.ofReal_zero,zero_mul,add_zero,
    RCLike.real_smul_eq_coe_mul,Complex.ofReal_mul]
  rfl

include hτ in
theorem increment_law (h : ℝ≥0) (N : ℕ) (hN : ∀ ω, τ ω ≤ N) :
    gaussianProduct.map (increment τ h) = gaussianReal 0 h := by
  simpa only [Measure.restrict_univ,measure_univ,one_smul] using
    restricted_increment_law τ hτ h N hN univ MeasurableSet.univ

theorem increment_independent (h : ℝ≥0) (N : ℕ) (hN : ∀ ω, τ ω ≤ N) :
    Indep (MeasurableSpace.comap (increment τ h) inferInstance)
      hτ.measurableSpace gaussianProduct := by
  apply (indep_iff_forall_indepSet gaussianProduct).mpr
  intro S A hS hA
  obtain ⟨B,hB,rfl⟩ := hS
  have hR := increment_measurable τ hτ h
  apply (indepSet_iff_measure_inter_eq_mul (hR hB)
    (hτ.measurableSpace_le A hA) gaussianProduct).mpr
  have hm := congrArg (fun ν : Measure ℝ => ν B)
    (restricted_increment_law τ hτ h N hN A hA)
  rw [Measure.map_apply hR hB,Measure.restrict_apply (hR hB),
    Measure.smul_apply,smul_eq_mul] at hm
  have hl := congrArg (fun ν : Measure ℝ => ν B) (increment_law τ hτ h N hN)
  rw [Measure.map_apply hR hB] at hl
  rw [hm,hl]
  exact mul_comm _ _

end OperatorDerivativeRewrite.Foundation.BrownianStoppedIncrementLaw
