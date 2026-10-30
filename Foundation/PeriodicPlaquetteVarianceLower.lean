import Foundation.PeriodicLinkDisintegration
import Foundation.PeriodicCurvatureVariance
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Quantitative nondegeneracy of actual stationary periodic plaquette variance.
The one-link conditional lower bound is transported through the true reweighted
marginal, the actual augmented bridge and the stationary two-step bridge tower.
Bounds for squared distance from every constant avoid auxiliary conditional-mean
constructions. This is a fixed-cell theorem, not local spectral slowing or a
continuum or infinite-volume mass-gap result. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open OperatorDerivativeRewrite.Foundation
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab
open PeriodicLinkStaples PeriodicLinkDisintegration
open SU2WilsonConvolution
namespace OperatorDerivativeRewrite.Foundation.PeriodicPlaquetteVarianceLower
attribute [local irreducible] split coordinateSplit baseField conditionalKernel marginal

theorem centered_fiber (e : SpatialEdge) (β : ℝ) (hβ : 0 ≤ β)
    (U W : State) (r : Rest e) (C : SU2) (c : ℝ) :
    6/(49*(1+6*β)^2) ≤
      ∫ A, (halfTrace (C*A)-c)^2 ∂conditionalKernel e β U W r := by
  let := kernel_markov e β U W
  have hm : Measurable (fun A : SU2 => halfTrace (C*A)) :=
    halfTrace_measurable.comp (measurable_const.mul measurable_id)
  have hl : MemLp (fun A : SU2 => halfTrace (C*A)) 2 (conditionalKernel e β U W r) :=
    MemLp.of_bound hm.aestronglyMeasurable 1
      (ae_of_all _ (fun A => by simpa only [Real.norm_eq_abs] using halfTrace_bound (C*A)))
  have hv := conditional_variance_lower e β hβ U W r C
  have hv' : 6/(49*(1+6*β)^2) ≤
      variance (fun A : SU2 => halfTrace (C*A)) (conditionalKernel e β U W r) := by
    simpa only [variance_eq_sub hl,Pi.pow_apply] using hv
  have hs := variance_sub_const (μ := conditionalKernel e β U W r) hm.aestronglyMeasurable c
  have hle := variance_le_expectation_sq
    (X := fun A : SU2 => halfTrace (C*A)-c) (hm.sub measurable_const).aestronglyMeasurable
    (μ := conditionalKernel e β U W r)
  rw [hs] at hle
  exact hv'.trans hle

private theorem square_bound {x c : ℝ} (hx : |x| ≤ 1) :
    |(x-c)^2| ≤ (1+|c|)^2 := by
  rw [abs_of_nonneg (sq_nonneg _)]
  have h := (abs_sub x c).trans (add_le_add hx (le_refl |c|))
  nlinarith [abs_nonneg (x-c),abs_nonneg c,sq_abs (x-c)]

theorem centered_augmented (p : SpatialFace) (β : ℝ) (hβ : 0 ≤ β)
    (U W : State) (c : ℝ) :
    6/(49*(1+6*β)^2) ≤ ∫ q, (PeriodicCurvatureVariance.plaquette p q.1-c)^2
      ∂PeriodicAugmentedBridge.law β U W := by
  let e := faceEdge p 0
  let f : Rest e × SU2 → ℝ := fun z =>
    (PeriodicCurvatureVariance.plaquette p ((split e).symm z).1-c)^2
  let := marginal_probability e β U W
  let := kernel_markov e β U W
  have hm : Measurable f :=
    (((PeriodicCurvatureVariance.plaquette_measurable p).comp
      (measurable_fst.comp (split e).symm.measurable)).sub measurable_const).pow_const 2
  have hb (z : Rest e × SU2) : ‖f z‖ ≤ (1+|c|)^2 := by
    rw [Real.norm_eq_abs]
    exact square_bound (halfTrace_bound _)
  have hi : Integrable f ((marginal e β U W) ⊗ₘ conditionalKernel e β U W) :=
    Integrable.of_bound hm.aestronglyMeasurable _ (ae_of_all _ hb)
  have he (r : Rest e) :
      6/(49*(1+6*β)^2) ≤ ∫ A, f (r,A) ∂conditionalKernel e β U W r := by
    have hf (A : SU2) : f (r,A) =
        (halfTrace (faceRemainder (baseField e r) p 0*A)-c)^2 := by
      dsimp [f,PeriodicCurvatureVariance.plaquette]
      rw [assemble,spatial_trace_at_slot,halfTrace_mul_comm]
    simp_rw [hf]
    exact centered_fiber e β hβ U W r _ c
  have hmarg := integral_mono (integrable_const (6/(49*(1+6*β)^2)))
    hi.integral_compProd he
  simp only [integral_const,probReal_univ,one_smul] at hmarg
  simp only [Kernel.prodMkLeft_apply,Kernel.const_apply] at hmarg
  rw [← Measure.integral_compProd hi] at hmarg
  rw [← actual_factorization] at hmarg
  rw [integral_map (split e).measurable.aemeasurable hm.aestronglyMeasurable] at hmarg
  simpa only [f,MeasurableEquiv.symm_apply_apply] using hmarg

theorem centered_bridge (p : SpatialFace) (β : ℝ) (hβ : 0 ≤ β)
    (U W : State) (c : ℝ) :
    6/(49*(1+6*β)^2) ≤ ∫ V, (PeriodicCurvatureVariance.plaquette p V-c)^2
      ∂PeriodicGroundBridge.law β U W := by
  have hm : Measurable (fun V => (PeriodicCurvatureVariance.plaquette p V-c)^2) :=
    ((PeriodicCurvatureVariance.plaquette_measurable p).sub measurable_const).pow_const 2
  have h := PeriodicAugmentedBridge.projection_integral β U W _ hm ((1+|c|)^2)
    (fun V => square_bound (halfTrace_bound _))
  rw [← h]
  exact centered_augmented p β hβ U W c

theorem centered_stationary (p : SpatialFace) (β : ℝ) (hβ : 0 ≤ β)
    (d : PeriodicSlabGround.GroundData β) (c : ℝ) :
    6/(49*(1+6*β)^2) ≤ ∫ V, (PeriodicCurvatureVariance.plaquette p V-c)^2
      ∂d.stationary := by
  let := d.stationary_probability
  let := d.transition_markov
  let f : State → ℝ := fun V => (PeriodicCurvatureVariance.plaquette p V-c)^2
  have hf : Measurable f :=
    ((PeriodicCurvatureVariance.plaquette_measurable p).sub measurable_const).pow_const 2
  have hb (V : State) : |f V| ≤ (1+|c|)^2 := square_bound (halfTrace_bound _)
  let M : State × State → ℝ := fun q => ∫ V, f V ∂PeriodicGroundBridge.bridgeKernel β q
  have hm : Measurable M := hf.stronglyMeasurable.integral_kernel.measurable
  have hmb (q : State × State) : ‖M q‖ ≤ (1+|c|)^2 := by
    have hh := norm_integral_le_of_norm_le_const
      (f := f)
      (μ := PeriodicGroundBridge.bridgeKernel β q)
      (ae_of_all _ (fun V => by simpa only [Real.norm_eq_abs] using hb V))
    simpa only [probReal_univ,mul_one] using hh
  have hi (U : State) : Integrable (fun W => M (U,W)) ((d.transition ∘ₖ d.transition) U) :=
    Integrable.of_bound (hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      _ (ae_of_all _ (fun W => hmb (U,W)))
  have hm' : Measurable (fun U => ∫ W, M (U,W) ∂((d.transition ∘ₖ d.transition) U)) :=
    hm.stronglyMeasurable.integral_kernel_prod_right'.measurable
  have hb' (U : State) : ‖∫ W, M (U,W) ∂((d.transition ∘ₖ d.transition) U)‖ ≤ (1+|c|)^2 := by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (f := fun W => M (U,W))
      (μ := (d.transition ∘ₖ d.transition) U) (ae_of_all _ (fun W => hmb (U,W)))
  have hj : Integrable (fun U => ∫ W, M (U,W) ∂((d.transition ∘ₖ d.transition) U))
      d.stationary := Integrable.of_bound hm'.aestronglyMeasurable _ (ae_of_all _ hb')
  have lower (U : State) : 6/(49*(1+6*β)^2) ≤
      ∫ W, M (U,W) ∂((d.transition ∘ₖ d.transition) U) := by
    have h := integral_mono (integrable_const (6/(49*(1+6*β)^2))) (hi U)
      (fun W => by simpa only [M,PeriodicGroundBridge.bridgeKernel_apply] using
        centered_bridge p β hβ U W c)
    simpa only [integral_const,probReal_univ,one_smul] using h
  have h := integral_mono (integrable_const (6/(49*(1+6*β)^2))) hj lower
  simp only [integral_const,probReal_univ,one_smul,M,PeriodicGroundBridge.bridgeKernel_apply] at h
  rw [PeriodicGroundBridge.stationary_bridge_average d f hf ((1+|c|)^2) hb] at h
  exact h

theorem stationary_variance_lower (p : SpatialFace) (β : ℝ) (hβ : 0 ≤ β)
    (d : PeriodicSlabGround.GroundData β) :
    6/(49*(1+6*β)^2) ≤ variance (PeriodicCurvatureVariance.plaquette p) d.stationary := by
  rw [variance_eq_integral (PeriodicCurvatureVariance.plaquette_measurable p).aemeasurable]
  exact centered_stationary p β hβ d _

/-- The constructed ground transform, with no additional existence premise. -/
theorem actual_variance_lower (p : SpatialFace) (β : ℝ) (hβ : 0 ≤ β) :
    6/(49*(1+6*β)^2) ≤ variance (PeriodicCurvatureVariance.plaquette p)
      (PeriodicSlabGround.ground β).stationary :=
  stationary_variance_lower p β hβ (PeriodicSlabGround.ground β)

end OperatorDerivativeRewrite.Foundation.PeriodicPlaquetteVarianceLower
