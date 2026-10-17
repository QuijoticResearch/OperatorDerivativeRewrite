import Foundation.StickyPairMarginals

/-! Complex Fourier sampling at two genuine ordered bounded Brownian stopping times. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianComplexSampling
open InfiniteGaussian IBMConstructedSources BrownianFourierMartingales
open BrownianMassClockStoppingTime BrownianStoppedFourier ContinuousTimeChangeMartingale
open ContinuousBoundedSampling StickyPairSampling IBMOneTimeFourier
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath

def imaginaryEmbedding : ℝ →L[ℝ] ℂ :=
  ((ContinuousLinearMap.mul ℝ ℂ) Complex.I).comp Complex.ofRealCLM

def phase (u : ℝ) (t : ℝ≥0) (w : SampleSpace) : ℂ :=
  (cosineProcess u t w : ℂ)+imaginaryEmbedding (sineProcess u t w)

theorem phase_eq (u : ℝ) (t : ℝ≥0) (w : SampleSpace) :
    phase u t w=(weight u t : ℂ)*observable u (clockPath w t) := by
  rw [observable,Complex.exp_ofReal_mul_I]
  simp only [phase,imaginaryEmbedding,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply,Complex.ofRealCLM_apply,cosineProcess,sineProcess,
    cosine,sine,Complex.ofReal_mul]
  change _+Complex.I*((weight u t : ℂ)*(Real.sin (u*clockPath w t):ℂ))=_
  ring

variable (τ : SampleSpace → ℝ≥0)
  (hτ : IsStoppingTime augmentedPast (fun w => (τ w : WithTop ℝ≥0)))

theorem phase_at_stop_measurable (u : ℝ) :
    Measurable[hτ.measurableSpace] (fun w => phase u (τ w) w) := by
  simp_rw [phase_eq]
  have ht := time_measurable augmentedPast τ hτ
  have hb := brownian_at_stop_measurable τ hτ
  exact ((Complex.continuous_ofReal.measurable.comp
    ((weight_smooth u).continuous.measurable.comp
      (NNReal.continuous_coe.measurable.comp ht))).mul
    ((observable_continuous u).measurable.comp hb))

include hτ in
theorem phase_integrable (u : ℝ) (N : ℕ) (hN : ∀ w, τ w ≤ N) :
    Integrable (fun w => phase u (τ w) w) gaussianProduct :=
  ((stopped_integrable gaussianProduct augmentedPast (cosineProcess u)
    (cosine_martingale u) (cosine_continuous u) τ hτ N hN).ofReal).add
    (imaginaryEmbedding.integrable_comp (stopped_integrable gaussianProduct augmentedPast
      (sineProcess u) (sine_martingale u) (sine_continuous u) τ hτ N hN))

include hτ in
theorem phase_mean (u : ℝ) (N : ℕ) (hN : ∀ w, τ w ≤ N) :
    (∫ w, phase u (τ w) w ∂gaussianProduct)=1 := by
  have hc := stopped_integrable gaussianProduct augmentedPast (cosineProcess u)
    (cosine_martingale u) (cosine_continuous u) τ hτ N hN
  have hs := stopped_integrable gaussianProduct augmentedPast (sineProcess u)
    (sine_martingale u) (sine_continuous u) τ hτ N hN
  change (∫ w, (cosineProcess u (τ w) w : ℂ)+
    imaginaryEmbedding (sineProcess u (τ w) w) ∂gaussianProduct)=1
  have hi := integral_add hc.ofReal (imaginaryEmbedding.integrable_comp hs)
  change (∫ w, (cosineProcess u (τ w) w : ℂ)+
    imaginaryEmbedding (sineProcess u (τ w) w) ∂gaussianProduct)=
    (∫ w, (cosineProcess u (τ w) w : ℂ) ∂gaussianProduct)+
    ∫ w, imaginaryEmbedding (sineProcess u (τ w) w) ∂gaussianProduct at hi
  rw [hi,integral_complex_ofReal,imaginaryEmbedding.integral_comp_comm hs,
    stopped_cosine_mean u τ hτ N hN,stopped_sine_mean u τ hτ N hN]
  simp

variable (σ : SampleSpace → ℝ≥0)
  (hσ : IsStoppingTime augmentedPast (fun w => (σ w : WithTop ℝ≥0)))

include hτ in
theorem phase_conditional (u : ℝ) (hστ : ∀ w, σ w ≤ τ w)
    (N : ℕ) (hN : ∀ w, τ w ≤ N) :
    gaussianProduct[(fun w => phase u (τ w) w) | hσ.measurableSpace]
      =ᵐ[gaussianProduct] (fun w => phase u (σ w) w) := by
  have hc := stopped_integrable gaussianProduct augmentedPast (cosineProcess u)
    (cosine_martingale u) (cosine_continuous u) τ hτ N hN
  have hs := stopped_integrable gaussianProduct augmentedPast (sineProcess u)
    (sine_martingale u) (sine_continuous u) τ hτ N hN
  have hcos := sample_two gaussianProduct augmentedPast (cosineProcess u)
    (cosine_martingale u) (cosine_continuous u) σ τ hσ hτ hστ N hN
  have hsin := sample_two gaussianProduct augmentedPast (sineProcess u)
    (sine_martingale u) (sine_continuous u) σ τ hσ hτ hστ N hN
  have hca := Complex.ofRealCLM.comp_condExp_comm hc (m := hσ.measurableSpace)
  have hsa := imaginaryEmbedding.comp_condExp_comm hs (m := hσ.measurableSpace)
  have hadd := condExp_add hc.ofReal (imaginaryEmbedding.integrable_comp hs) hσ.measurableSpace
  change gaussianProduct[(fun w => (cosineProcess u (τ w) w : ℂ)+
    imaginaryEmbedding (sineProcess u (τ w) w)) | hσ.measurableSpace] =ᵐ[gaussianProduct] _ at hadd
  apply hadd.trans
  filter_upwards [hca,hsa,hcos,hsin] with w hca hsa hcos hsin
  change (gaussianProduct[(fun w => cosineProcess u (τ w) w) | hσ.measurableSpace] w : ℂ)=
    gaussianProduct[(fun w => (cosineProcess u (τ w) w : ℂ)) | hσ.measurableSpace] w at hca
  change imaginaryEmbedding (gaussianProduct[(fun w => sineProcess u (τ w) w) |
    hσ.measurableSpace] w)=gaussianProduct[(fun w => imaginaryEmbedding
    (sineProcess u (τ w) w)) | hσ.measurableSpace] w at hsa
  change gaussianProduct[(fun w => (cosineProcess u (τ w) w : ℂ)) | hσ.measurableSpace] w+
    gaussianProduct[(fun w => imaginaryEmbedding (sineProcess u (τ w) w)) |
      hσ.measurableSpace] w=phase u (σ w) w
  rw [← hca,← hsa,← hcos,← hsin]
  rfl

include hτ in
theorem weighted_sampling (u : ℝ) (hστ : ∀ w, σ w ≤ τ w)
    (N : ℕ) (hN : ∀ w, τ w ≤ N) (F : SampleSpace → ℂ)
    (hF : StronglyMeasurable[hσ.measurableSpace] F)
    (hi : Integrable (fun w => F w*phase u (τ w) w) gaussianProduct) :
    (∫ w, F w*phase u (τ w) w ∂gaussianProduct)=
      ∫ w, F w*phase u (σ w) w ∂gaussianProduct := by
  have hp := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ)
    hF hi (phase_integrable τ hτ u N hN)
  calc
    _ = ∫ w, gaussianProduct[(fun w => F w*phase u (τ w) w) | hσ.measurableSpace] w
        ∂gaussianProduct := (integral_condExp hσ.measurableSpace_le).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hp,phase_conditional τ hτ σ hσ u hστ N hN] with w hw hc
      change gaussianProduct[(fun w => F w*phase u (τ w) w) | hσ.measurableSpace] w=_ at hw ⊢
      rw [hw,hc]
      rfl

end OperatorDerivativeRewrite.Foundation.BrownianComplexSampling
