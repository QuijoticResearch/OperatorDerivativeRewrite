import Foundation.GaussianPredictableHorizon
import Foundation.L2Supported

/-! Identification of the old completion with the full raw predictable L2 domain. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianPredictableFull
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 GaussianTimeHilbert
open GaussianPredictableL2Completion GaussianPredictableHorizon PredictableRealL2

def positiveTimes : Set (ℝ × SampleSpace) := Ioi 0 ×ˢ univ

theorem positiveTimes_measurable : MeasurableSet positiveTimes :=
  measurableSet_Ioi.prod MeasurableSet.univ

theorem horizons_union : (⋃ n : ℕ, horizon (Ω := SampleSpace) (n : ℝ≥0)) = positiveTimes := by
  ext z
  simp only [mem_iUnion, horizon, positiveTimes, mem_prod, mem_Ioc, mem_Ioi, mem_univ,
    and_true, NNReal.coe_natCast]
  constructor
  · rintro ⟨n, hn⟩
    exact hn.1
  · intro hz
    obtain ⟨n, hn⟩ := exists_nat_gt z.1
    exact ⟨n, hz, hn.le⟩

theorem horizons_monotone : Monotone (fun n : ℕ => horizon (Ω := SampleSpace) (n : ℝ≥0)) := by
  intro n m hnm z hz
  exact ⟨⟨hz.1.1, hz.1.2.trans (by exact_mod_cast hnm)⟩, hz.2⟩

/-- The full domain is defined by measurable representatives and positive-time support. -/
def fullPredictable : Submodule ℝ TimeProbabilityL2 :=
  lpMeas ℝ ℝ (predictable naturalFiltration) 2 timeProbability ⊓
    supportedL2 positiveTimes_measurable

theorem mem_fullPredictable_iff (U : TimeProbabilityL2) : U ∈ fullPredictable ↔
    AEStronglyMeasurable[predictable naturalFiltration] U timeProbability ∧
      (∀ᵐ z ∂timeProbability, z ∉ positiveTimes → U z = 0) := by
  change (_ ∧ U ∈ supportedL2 positiveTimes_measurable) ↔ _
  rw [mem_supportedL2_iff]
  rfl

theorem fullPredictable_isClosed : IsClosed (fullPredictable : Set TimeProbabilityL2) :=
  (isClosed_aestronglyMeasurable (predictable_le naturalFiltration)).inter
    (supportedL2_isClosed positiveTimes_measurable)

theorem past_step_mem_fullPredictable (s t : ℝ≥0) (A : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct) :
    productTensor (intervalVector s t) A ∈ fullPredictable := by
  rw [mem_fullPredictable_iff]
  have ht := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae_eq_comp
      (intervalVector_coeFn s t)
  have he : productTensor (intervalVector s t) A =ᵐ[timeProbability]
      fun z => (Ioc (s : ℝ) (t : ℝ)).indicator (fun _ => A z.2) z.1 := by
    filter_upwards [productTensor_coeFn (intervalVector s t) A, ht] with z hz ht
    simp only [Function.comp_apply] at ht
    rw [hz, ht]
    by_cases h : z.1 ∈ Ioc (s : ℝ) (t : ℝ) <;> simp [h]
  constructor
  · obtain ⟨a, ha, hea⟩ :=
      (GaussianPredictableStep.measurable_natural_iff_exists_pastCoefficient
        (fun t => (process_stronglyMeasurable t).measurable) s (hA.mk A)).mp
          hA.stronglyMeasurable_mk.measurable
    have hm : StronglyMeasurable[predictable naturalFiltration]
        ((Function.uncurry (GaussianPredictableStep.stepProcess process s t a)) ∘
          toNonnegative) :=
      (timeStep_stronglyPredictable s t ha).comp_measurable (Measurable.of_comap_le le_rfl)
    apply hm.aestronglyMeasurable.congr
    have hc := (Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae_eq_comp hA.ae_eq_mk
    filter_upwards [he, hc] with z hz hc
    simp only [Function.comp_apply] at hc
    rw [hea] at hc
    rw [hz]
    have hiff : z.1.toNNReal ∈ Ioc s t ↔ z.1 ∈ Ioc (s : ℝ) (t : ℝ) := by
      simp only [mem_Ioc, Real.lt_toNNReal_iff_coe_lt, Real.toNNReal_le_iff_le_coe]
    change (Ioc s t).indicator (fun _ =>
      GaussianPredictableStep.pastCoefficient process s a z.2) z.1.toNNReal = _
    by_cases h : z.1 ∈ Ioc (s : ℝ) (t : ℝ)
    · simp [h, hiff.mpr h, hc]
    · simp [h, not_congr hiff |>.mpr h]
  · filter_upwards [he] with z hz hs
    rw [hz]
    apply indicator_of_notMem
    intro hz
    exact hs ⟨lt_of_le_of_lt s.coe_nonneg hz.1, mem_univ _⟩

/-- Full predictable fields supported in positive time belong to the OLD completion. -/
theorem predictable_mem_closedProductSteps (U : TimeProbabilityL2)
    (hU : AEStronglyMeasurable[predictable naturalFiltration] U timeProbability)
    (hsupp : ∀ᵐ z ∂timeProbability, z ∉ positiveTimes → U z = 0) :
    U ∈ closedProductSteps := by
  have hclosed := productStepSpan.isClosed_topologicalClosure
  have : CompleteSpace closedProductSteps := hclosed.completeSpace_coe
  rw [← closedProductSteps.orthogonal_orthogonal]
  apply (closedProductSteps.orthogonal.mem_orthogonal U).2
  intro V hV
  have hi : Integrable (fun z => inner ℝ (V z) (U z)) timeProbability :=
    L2.integrable_inner V U
  have hz (n : ℕ) : (∫ z in horizon (n : ℝ≥0), inner ℝ (V z) (U z) ∂timeProbability) = 0 := by
    let R : Lp ℝ 2 (horizonMeasure (n : ℝ≥0) gaussianProduct) :=
      ((Lp.memLp U).restrict (horizon (n : ℝ≥0))).toLp U
    have hR : AEStronglyMeasurable[predictable naturalFiltration] R
        (horizonMeasure (n : ℝ≥0) gaussianProduct) :=
      hU.restrict.congr (MemLp.coeFn_toLp _).symm
    have he := L2ZeroExtension_coeFn (horizon_measurable (n : ℝ≥0)) R
    have heR := (ae_eq_restrict_iff_indicator_ae_eq (horizon_measurable (n : ℝ≥0))).mp
      (show R =ᵐ[horizonMeasure (n : ℝ≥0) gaussianProduct] U from MemLp.coeFn_toLp _)
    have hv := Submodule.inner_left_of_mem_orthogonal
      (zeroExtension_mem (n : ℝ≥0) R hR) hV
    rw [L2_inner_eq_integral] at hv
    rw [← integral_indicator (horizon_measurable (n : ℝ≥0))]
    convert hv using 1
    apply integral_congr_ae
    filter_upwards [he, heR] with z hz hr
    rw [hz, hr]
    by_cases h : z ∈ horizon (Ω := SampleSpace) (n : ℝ≥0) <;> simp [h]
  have ht := tendsto_setIntegral_of_monotone
    (fun n : ℕ => horizon_measurable (Ω := SampleSpace) (n : ℝ≥0))
    horizons_monotone hi.integrableOn
  simp only [hz, horizons_union] at ht
  have hzero : (∫ z in positiveTimes, inner ℝ (V z) (U z) ∂timeProbability) = 0 :=
    tendsto_nhds_unique ht tendsto_const_nhds
  rw [L2_inner_eq_integral, ← hzero, ← integral_indicator positiveTimes_measurable]
  apply integral_congr_ae
  filter_upwards [hsupp] with z hz
  by_cases h : z ∈ positiveTimes
  · simp [h]
  · simp [h, hz h]

/-- Actual equality of domains, not a definition of predictability by closure. -/
theorem closedProductSteps_eq_fullPredictable : closedProductSteps = fullPredictable := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · change transportRelation.map (LinearMap.fst ℝ TimeProbabilityL2 GaussianVectorL2) ≤ _
      rw [Submodule.map_le_iff_le_comap]
      apply Submodule.span_le.mpr
      rintro z ⟨n, r, p, s, t, hrs, hst, rfl⟩
      exact past_step_mem_fullPredictable s t _
        (GaussianPastStepCompletion.past_polynomial_measurable s r hrs p)
    · exact fullPredictable_isClosed
  · intro U hU
    obtain ⟨hm, hs⟩ := (mem_fullPredictable_iff U).mp hU
    exact predictable_mem_closedProductSteps U hm hs

theorem mem_closedProductSteps_iff (U : TimeProbabilityL2) : U ∈ closedProductSteps ↔
    AEStronglyMeasurable[predictable naturalFiltration] U timeProbability ∧
      (∀ᵐ z ∂timeProbability, z ∉ positiveTimes → U z = 0) := by
  rw [closedProductSteps_eq_fullPredictable, mem_fullPredictable_iff]

/-- The identity on the actual ambient L2 classes. -/
def domainEquiv : fullPredictable ≃ₗᵢ[ℝ] closedProductSteps where
  toLinearEquiv := LinearEquiv.ofEq _ _ closedProductSteps_eq_fullPredictable.symm
  norm_map' _ := rfl

def itoIntegral : fullPredictable →ₗᵢ[ℝ] GaussianL2 :=
  productIntegral.comp domainEquiv.toLinearIsometry

theorem itoIntegral_norm (U : fullPredictable) : ‖itoIntegral U‖ = ‖U‖ :=
  itoIntegral.norm_map U

theorem itoIntegral_centered (U : fullPredictable) :
    (∫ ω, itoIntegral U ω ∂gaussianProduct) = 0 :=
  productIntegral_centered (domainEquiv U)

theorem itoIntegral_divergence_graph (U : fullPredictable) :
    ((productToField (domainEquiv U) : GaussianVectorL2), itoIntegral U) ∈
      hilbertDivergence.graph := productIntegral_hilbertDivergence_graph (domainEquiv U)

/-- Agreement with actual increment products for arbitrary L2 past coefficients. -/
theorem itoIntegral_past_step (s t : ℝ≥0) (hst : s ≤ t) (A : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct) :
    itoIntegral ⟨productTensor (intervalVector s t) A, past_step_mem_fullPredictable s t A hA⟩
      =ᵐ[gaussianProduct] fun ω => A ω * (process t ω - process s ω) :=
  GaussianPastStepCompletion.productIntegral_pastStep_coeFn s t hst A hA

theorem itoIntegral_past_partition {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (A : Fin n → GaussianL2)
    (hA : ∀ i, AEStronglyMeasurable[naturalFiltration (τ i.castSucc)] (A i) gaussianProduct) :
    itoIntegral (domainEquiv.symm (GaussianPastStepCompletion.pastPartition τ hτ A hA))
      =ᵐ[gaussianProduct]
        fun ω => ∑ i, A i ω * (process (τ i.succ) ω - process (τ i.castSucc) ω) := by
  change productIntegral (domainEquiv (domainEquiv.symm _)) =ᵐ[gaussianProduct] _
  rw [domainEquiv.apply_symm_apply]
  exact GaussianPastStepCompletion.productIntegral_pastPartition_coeFn τ hτ A hA

/-- Uniqueness among all continuous linear extensions from the dense algebraic steps. -/
theorem itoIntegral_unique (J : fullPredictable →L[ℝ] GaussianL2)
    (hJ : ∀ z : transportRelation,
      J (domainEquiv.symm (productAssembly z)) = productIntegral (productAssembly z)) :
    J = itoIntegral.toContinuousLinearMap := by
  have he := productAssembly_dense.equalizer
    (J.continuous.comp domainEquiv.symm.continuous) productIntegral.continuous (funext hJ)
  apply ContinuousLinearMap.ext
  intro U
  change J U = productIntegral (domainEquiv U)
  have h := congr_fun he (domainEquiv U)
  simpa only [Function.comp_apply, domainEquiv.symm_apply_apply] using h

end OperatorDerivativeRewrite.Foundation.GaussianPredictableFull
