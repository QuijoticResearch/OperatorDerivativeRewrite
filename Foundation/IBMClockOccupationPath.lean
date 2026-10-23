import Foundation.IBMClockOccupationTests

/-! Actual samplewise signed occupation tests and their L2 realization by the
physical kernel of the original linear IBM-average clock derivative. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockOccupationPath
open InfiniteGaussian GaussianTimeHilbert IBMClockPhysicalOccupation
open IBMClockOccupationTests IBMClockOverlapEnergy
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def value (h : CoefficientSpace) (φ : ℝ → ℝ) (p : ℝ × SampleSpace) : ℝ :=
  inner ℝ h (IBMClockAverageCandidate.direction p.1) *
    BrownianSignIntegral.signum (IBMConstructedSources.clockPath p.2 p.1.toNNReal) *
      φ |IBMConstructedSources.clockPath p.2 p.1.toNNReal|

theorem value_measurable (h : CoefficientSpace) (φ : ℝ → ℝ) (hc : Continuous φ) :
    Measurable (value h φ) := by
  have hd : Measurable (fun t : ℝ => inner ℝ h (IBMClockAverageCandidate.direction t)) :=
    (continuous_const.inner IBMClockAverageCandidate.direction_continuous).measurable
  have hb := BrownianClockWeightedEnergy.sigma_measurable
  exact ((hd.comp measurable_fst).mul (BrownianSignIntegral.signum_measurable.comp hb)).mul
    (hc.measurable.comp (continuous_abs.measurable.comp hb))

theorem value_bound (h : CoefficientSpace) (φ : ℝ → ℝ) {M : ℝ}
    (_hM : 0 ≤ M) (hb : ∀ x, ‖φ x‖ ≤ M) (T : ℝ≥0)
    (p : ℝ × SampleSpace) (hp : p.1 ∈ Ioc 0 (T : ℝ)) :
    ‖value h φ p‖ ≤ ‖h‖ * Real.sqrt T * M := by
  have hd := IBMClockAverageCandidate.direction_norm_bound T.property hp
  have hi : ‖inner ℝ h (IBMClockAverageCandidate.direction p.1)‖ ≤ ‖h‖ * Real.sqrt T :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hd (norm_nonneg _))
  rw [value, norm_mul, norm_mul]
  calc
    _ ≤ ((‖h‖ * Real.sqrt T) * 1) * M :=
      mul_le_mul (mul_le_mul hi (BrownianSignIntegral.signum_bound _)
        (norm_nonneg _) (by positivity)) (hb _) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem value_time_integrable (h : CoefficientSpace) (φ : ℝ → ℝ)
    (hc : Continuous φ) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, ‖φ x‖ ≤ M)
    (T : ℝ≥0) (Y : SampleSpace) :
    Integrable (fun t : ℝ => value h φ (t,Y)) (window T) := by
  apply Integrable.of_bound
    (((value_measurable h φ hc).comp
      (measurable_id.prodMk measurable_const)).stronglyMeasurable.aestronglyMeasurable)
    (‖h‖ * Real.sqrt T * M)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact value_bound h φ hM hb T (t,Y) ht

def pathIntegral (h : CoefficientSpace) (φ : ℝ → ℝ) (T : ℝ≥0) (Y : SampleSpace) : ℝ :=
  ∫ t : ℝ, value h φ (t,Y) ∂window T

theorem pathIntegral_measurable (h : CoefficientSpace) (φ : ℝ → ℝ)
    (hc : Continuous φ) (T : ℝ≥0) : Measurable (pathIntegral h φ T) :=
  ((value_measurable h φ hc).stronglyMeasurable.integral_prod_left'
    (μ := window T)).measurable

theorem pathIntegral_bound (h : CoefficientSpace) (φ : ℝ → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, ‖φ x‖ ≤ M) (T : ℝ≥0) (Y : SampleSpace) :
    ‖pathIntegral h φ T Y‖ ≤ (T : ℝ) * (‖h‖ * Real.sqrt T * M) := by
  have ha : ∀ᵐ t ∂window T, ‖value h φ (t,Y)‖ ≤ ‖h‖ * Real.sqrt T * M := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact value_bound h φ hM hb T (t,Y) ht
  have hi := norm_integral_le_of_norm_le_const ha
  simpa [pathIntegral, window, Measure.real, Real.volume_Ioc,
    ENNReal.toReal_ofReal T.property, mul_comm] using hi

theorem pathIntegral_memLp (h : CoefficientSpace) (φ : ℝ → ℝ)
    (hc : Continuous φ) (hs : HasCompactSupport φ) (T : ℝ≥0) :
    MemLp (pathIntegral h φ T) 2 gaussianProduct := by
  obtain ⟨M, hM⟩ := hc.norm.bddAbove_range_of_hasCompactSupport hs.norm
  have hM0 : 0 ≤ M := (norm_nonneg (φ 0)).trans (hM ⟨0, rfl⟩)
  exact MemLp.of_bound (pathIntegral_measurable h φ hc T).aestronglyMeasurable
    ((T : ℝ) * (‖h‖ * Real.sqrt T * M))
    (ae_of_all _ (pathIntegral_bound h φ hM0 (fun x => hM ⟨x, rfl⟩) T))

def pathClass (h : CoefficientSpace) (φ : ℝ → ℝ) (hc : Continuous φ)
    (hs : HasCompactSupport φ) (T : ℝ≥0) : GaussianL2 :=
  (pathIntegral_memLp h φ hc hs T).toLp (pathIntegral h φ T)

theorem pathClass_ae (h : CoefficientSpace) (φ : ℝ → ℝ) (hc : Continuous φ)
    (hs : HasCompactSupport φ) (T : ℝ≥0) :
    pathClass h φ hc hs T =ᵐ[gaussianProduct] pathIntegral h φ T := MemLp.coeFn_toLp _

def component (v : TimeHilbert) : Lp TimeHilbert 2 gaussianProduct →L[ℝ] GaussianL2 :=
  (innerSL ℝ v).compLpL 2 gaussianProduct

theorem component_pairing (v : TimeHilbert) (u : Lp TimeHilbert 2 gaussianProduct)
    (ζ : GaussianL2) :
    inner ℝ (component v u) ζ = inner ℝ u (BochnerClosedOperator.tensor gaussianProduct ζ v) := by
  rw [L2_inner_eq_integral, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [(innerSL ℝ v).coeFn_compLpL u,
    BochnerClosedOperator.tensor_coeFn gaussianProduct ζ v] with Y hc ht
  change component v u Y = inner ℝ v (u Y) at hc
  rw [hc, ht, real_inner_smul_right, Real.inner_apply, real_inner_comm, mul_comm]

theorem pathClass_pairing (h : CoefficientSpace) (φ : ℝ → ℝ) (hc : Continuous φ)
    (hs : HasCompactSupport φ) (T : ℝ≥0) (ζ : GaussianL2) :
    inner ℝ (pathClass h φ hc hs T) ζ =
      ∫ Y, pathIntegral h φ T Y * ζ Y ∂gaussianProduct := by
  rw [L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [pathClass_ae h φ hc hs T] with Y hY
  rw [hY, Real.inner_apply, mul_comm]

attribute [local irreducible] component pathClass pathIntegral

theorem component_kernel_eq (h : CoefficientSpace) (φ : ℝ → ℝ) (hc : Continuous φ)
    (hs : HasCompactSupport φ) (T : ℝ≥0) :
    component (testClass φ hc hs) (kernel h T) = pathClass h φ hc hs T := by
  apply ext_inner_right ℝ
  intro ζ
  rw [component_pairing, kernel_actual_time_pairing, pathClass_pairing]
  simp only [pathIntegral, value]

/-- For each FIXED direction, horizon and spatial test, the actual kernel
represents the actual signed occupation integral almost surely in the clock.
This does not assert one common null set for all spatial tests. -/
theorem kernel_path_ae (h : CoefficientSpace) (φ : ℝ → ℝ) (hc : Continuous φ)
    (hs : HasCompactSupport φ) (T : ℝ≥0) :
    (fun Y => inner ℝ (kernel h T Y) (testClass φ hc hs)) =ᵐ[gaussianProduct]
      pathIntegral h φ T := by
  have ha : component (testClass φ hc hs) (kernel h T) =ᵐ[gaussianProduct]
      fun Y => inner ℝ (testClass φ hc hs) (kernel h T Y) := by
    simpa only [component, innerSL_apply_apply] using
      (innerSL ℝ (testClass φ hc hs)).coeFn_compLpL (kernel h T)
  rw [component_kernel_eq] at ha
  filter_upwards [ha, pathClass_ae h φ hc hs T] with Y hc hp
  exact (real_inner_comm _ _).trans ((hc.symm).trans hp)

theorem kernel_test_integrable (h : CoefficientSpace) (φ : ℝ → ℝ) (hc : Continuous φ)
    (hs : HasCompactSupport φ) (T : ℝ≥0) (Y : SampleSpace) :
    Integrable (fun r : ℝ => kernel h T Y r * φ r) := by
  have hi := (Lp.memLp (kernel h T Y)).integrable_mul (Lp.memLp (testClass φ hc hs))
  apply hi.congr
  filter_upwards [testClass_ae φ hc hs] with r hr
  simp only [Pi.mul_apply, hr]

/-- Literal spatial Lebesgue integral equals the actual signed time integral,
almost surely for each fixed admissible spatial test. -/
theorem kernel_spatial_integral_ae (h : CoefficientSpace) (φ : ℝ → ℝ)
    (hc : Continuous φ) (hs : HasCompactSupport φ) (T : ℝ≥0) :
    (fun Y => ∫ r : ℝ, kernel h T Y r * φ r) =ᵐ[gaussianProduct] pathIntegral h φ T := by
  have he (Y : SampleSpace) :
      inner ℝ (kernel h T Y) (testClass φ hc hs) = ∫ r : ℝ, kernel h T Y r * φ r := by
    rw [L2_inner_eq_integral]
    apply integral_congr_ae
    filter_upwards [testClass_ae φ hc hs] with r hr
    rw [hr, Real.inner_apply, mul_comm]
  filter_upwards [kernel_path_ae h φ hc hs T] with Y hY
  exact (he Y).symm.trans hY

/-- Any specified countable family has a common clock-full-measure event.
No uncountable determining-family or measure-equality conclusion is built in. -/
theorem kernel_spatial_integral_ae_family (h : CoefficientSpace) (φ : ℕ → ℝ → ℝ)
    (hc : ∀ n, Continuous (φ n)) (hs : ∀ n, HasCompactSupport (φ n)) (T : ℝ≥0) :
    ∀ᵐ Y ∂gaussianProduct, ∀ n,
      (∫ r : ℝ, kernel h T Y r * φ n r) = pathIntegral h (φ n) T Y :=
  ae_all_iff.mpr (fun n => kernel_spatial_integral_ae h (φ n) (hc n) (hs n) T)

end OperatorDerivativeRewrite.Foundation.IBMClockOccupationPath
