import Foundation.GaussianDeterministicIntegral

/-! Deterministic causal L2 kernels in the ACTUAL predictable stochastic integral.
Per-time L2 and support are explicit. No random-kernel Fubini or fractional
Brownian normalization is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianDeterministicVolterra
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProductL2 GaussianTimeProcess
open GaussianPredictableFull GaussianDeterministicIntegral GaussianContinuousRigidity
open GaussianHilbertProcess
attribute [local instance] timeHilbert_secondCountable

theorem predictable_time_measurable :
    @Measurable (ℝ≥0 × SampleSpace) ℝ≥0 naturalFiltration.predictable inferInstance Prod.fst := by
  letI : MeasurableSpace (ℝ≥0 × SampleSpace) := naturalFiltration.predictable
  apply measurable_of_Ioi
  intro t
  rw [show Prod.fst ⁻¹' Ioi t = Ioi t ×ˢ (univ : Set SampleSpace) by ext z; simp]
  exact measurableSet_predictable_Ioi_prod MeasurableSet.univ

/-- Predictability follows from deterministic measurability and positive-time
support, without any step approximation or additional regularity assumption. -/
theorem positive_profile_predictable (a : TimeHilbert)
    (ha : ∀ᵐ t ∂(volume : Measure ℝ), t ≤ 0 → a t = 0) :
    productTensor a gaussianOne ∈ fullPredictable := by
  let b : ℝ≥0 → ℝ := (Ioi 0).indicator (fun t => a (t : ℝ))
  have hb : Measurable b :=
    ((Lp.stronglyMeasurable a).measurable.comp measurable_coe_nnreal_real).indicator measurableSet_Ioi
  have hm : StronglyMeasurable[PredictableRealL2.predictable naturalFiltration]
      (fun z : ℝ × SampleSpace => b z.1.toNNReal) := by
    have hh := (hb.comp predictable_time_measurable).stronglyMeasurable
    exact hh.comp_measurable (Measurable.of_comap_le le_rfl)
  have he : productTensor a gaussianOne =ᵐ[timeProbability]
      fun z => b z.1.toNNReal := by
    have hp := (Measure.quasiMeasurePreserving_fst
      (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae ha
    have ho := (Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae_eq_comp gaussianOne_coeFn
    filter_upwards [productTensor_coeFn a gaussianOne, hp, ho] with z ht hp ho
    change gaussianOne z.2 = 1 at ho
    rw [ht, ho, mul_one]
    by_cases hz : 0 < z.1
    · have hz' : 0 < z.1.toNNReal := Real.toNNReal_pos.mpr hz
      simp [b, hz', Real.coe_toNNReal _ hz.le]
    · have hz' : z.1.toNNReal = 0 := Real.toNNReal_eq_zero.mpr (le_of_not_gt hz)
      rw [hp (le_of_not_gt hz), hz']
      simp [b]
  rw [mem_fullPredictable_iff]
  refine ⟨hm.aestronglyMeasurable.congr he.symm, ?_⟩
  filter_upwards [he] with z hz hs
  have hnon : z.1 ≤ 0 := le_of_not_gt (fun h => hs ⟨h, mem_univ _⟩)
  rw [hz, Real.toNNReal_eq_zero.mpr hnon]
  simp [b]

def positiveProfiles : Submodule ℝ TimeHilbert :=
  supportedL2 (μ := (volume : Measure ℝ)) (s := Ioi 0) measurableSet_Ioi

def profileField (a : positiveProfiles) : fullPredictable :=
  ⟨productTensor a gaussianOne, positive_profile_predictable a (by
    have h := (mem_supportedL2_iff measurableSet_Ioi (a : TimeHilbert)).mp a.property
    filter_upwards [h] with t ht hle
    exact ht (not_lt.mpr hle))⟩

def profileIntegral (a : positiveProfiles) : GaussianL2 := itoIntegral (profileField a)

theorem profileIntegral_eq_isonormal (a : positiveProfiles) :
    profileIntegral a = isonormalEmbedding TimeHilbert a :=
  itoIntegral_deterministic a (profileField a).property

theorem profileIntegral_derivative (a : positiveProfiles) :
    (profileIntegral a, fieldEmbedding (productTensor a gaussianOne)) ∈
      closedCylindricalDerivative.graph := by
  rw [profileIntegral_eq_isonormal]
  exact firstChaos_closedDerivative_graph a

theorem profileIntegral_law (a : positiveProfiles) :
    gaussianProduct.map (profileIntegral a) = gaussianReal 0 ⟨‖(a : TimeHilbert)‖ ^ 2, sq_nonneg _⟩ := by
  rw [profileIntegral_eq_isonormal]
  exact isonormal_law a.val

theorem profileIntegral_pair_integrable (a b : positiveProfiles) :
    Integrable (fun ω => profileIntegral a ω * profileIntegral b ω) gaussianProduct := by
  rw [profileIntegral_eq_isonormal, profileIntegral_eq_isonormal]
  exact isonormal_product_integrable a.val b.val

theorem profile_pair_integrable (a b : positiveProfiles) :
    Integrable (fun t => a.val t * b.val t) (volume : Measure ℝ) :=
  mul_L2_integrable (Lp.memLp a.val) (Lp.memLp b.val)

theorem profileIntegral_covariance (a b : positiveProfiles) :
    cov[profileIntegral a, profileIntegral b; gaussianProduct] =
      ∫ t, a.val t * b.val t ∂(volume : Measure ℝ) := by
  rw [profileIntegral_eq_isonormal, profileIntegral_eq_isonormal]
  change cov[isonormal TimeHilbert a.val, isonormal TimeHilbert b.val; gaussianProduct] = _
  rw [isonormal_covariance, L2_inner_eq_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun _ => by simp [Real.inner_apply, mul_comm]

/-- A causal deterministic Volterra kernel belongs to the positive-time
integrand space at EACH time, including degenerate kernels and time zero. -/
theorem causal_profile_mem (t : ℝ≥0) (k : TimeHilbert)
    (hk : ∀ᵐ s ∂(volume : Measure ℝ), s ∉ Ioc 0 (t : ℝ) → k s = 0) :
    k ∈ positiveProfiles := by
  rw [positiveProfiles, mem_supportedL2_iff]
  filter_upwards [hk] with s hs hnon
  exact hs (fun h => hnon h.1)

/-- Each time has its own actual L2 kernel. No joint time regularity is
asserted by this finite-dimensional-law construction. -/
def volterraProcess (K : ℝ≥0 → TimeHilbert)
    (hK : ∀ t : ℝ≥0, ∀ᵐ s ∂(volume : Measure ℝ), s ∉ Ioc 0 (t : ℝ) → K t s = 0)
    (t : ℝ≥0) : SampleSpace → ℝ :=
  profileIntegral ⟨K t, causal_profile_mem t (K t) (hK t)⟩

theorem volterraProcess_eq (K : ℝ≥0 → TimeHilbert)
    (hK : ∀ t : ℝ≥0, ∀ᵐ s ∂(volume : Measure ℝ), s ∉ Ioc 0 (t : ℝ) → K t s = 0) (t : ℝ≥0) :
    volterraProcess K hK t = isonormal TimeHilbert (K t) :=
  congrArg (fun f : GaussianL2 => (f : SampleSpace → ℝ))
    (profileIntegral_eq_isonormal ⟨K t, causal_profile_mem t (K t) (hK t)⟩)

theorem volterraProcess_isGaussianProcess (K : ℝ≥0 → TimeHilbert)
    (hK : ∀ t : ℝ≥0, ∀ᵐ s ∂(volume : Measure ℝ), s ∉ Ioc 0 (t : ℝ) → K t s = 0) :
    IsGaussianProcess (volterraProcess K hK) gaussianProduct := by
  have he : volterraProcess K hK = fun t => isonormal TimeHilbert (K t) :=
    funext (volterraProcess_eq K hK)
  rw [he]
  exact isonormal_isGaussianProcess.comp_right K

theorem volterraProcess_covariance (K : ℝ≥0 → TimeHilbert)
    (hK : ∀ t : ℝ≥0, ∀ᵐ s ∂(volume : Measure ℝ), s ∉ Ioc 0 (t : ℝ) → K t s = 0) (s t : ℝ≥0) :
    cov[volterraProcess K hK s, volterraProcess K hK t; gaussianProduct] =
      ∫ r, K s r * K t r ∂(volume : Measure ℝ) :=
  profileIntegral_covariance ⟨K s, causal_profile_mem s (K s) (hK s)⟩
    ⟨K t, causal_profile_mem t (K t) (hK t)⟩

end OperatorDerivativeRewrite.Foundation.GaussianDeterministicVolterra
