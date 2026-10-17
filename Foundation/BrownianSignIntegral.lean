import Foundation.BrownianClockWeightedEnergy
import Foundation.GaussianHermiteMartingale

/-! An actual predictable sign(B) field and its stochastic integral.
This constructs the martingale term needed for Tanaka; it does not assume
or assert an occupation formula or a local-time process. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianSignIntegral
open InfiniteGaussian GaussianTimeProductL2 GaussianProductDerivative
open GaussianPredictableFull GaussianHermiteRepresentation GaussianHermiteIntegrand
open GaussianTimeSpaceHermite BrownianClockWeightedEnergy IBMConstructedSources

def signum (x : ℝ) : ℝ := if 0 < x then 1 else if x < 0 then -1 else 0

theorem signum_measurable : Measurable signum := by
  unfold signum
  exact Measurable.ite measurableSet_Ioi measurable_const
    (Measurable.ite measurableSet_Iio measurable_const measurable_const)

theorem signum_zero : signum 0 = 0 := by simp [signum]

theorem signum_bound (x : ℝ) : ‖signum x‖ ≤ 1 := by
  unfold signum
  split_ifs <;> norm_num

theorem signum_sq {x : ℝ} (hx : x ≠ 0) : signum x ^ 2 = 1 := by
  rcases lt_or_gt_of_ne hx with h | h <;> simp [signum, h, not_lt_of_gt h]

theorem brownian_field_joint (T : ℝ≥0) :
    (hermiteIntegrand 1 T : TimeProbabilityL2) =ᵐ[timeProbability]
      (PredictableRealL2.horizon T).indicator sigma := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (Lp.stronglyMeasurable _).measurable
    (sigma_measurable.indicator (PredictableRealL2.horizon_measurable T)))).mpr
  filter_upwards [hermiteIntegrand_slices 1 T,
    scalarCurry_coeFn (hermiteIntegrand 1 T : TimeProbabilityL2)] with t ht hc
  by_cases hp : t ∈ Ioc 0 (T : ℝ)
  · rw [horizonValue, indicator_of_mem hp] at ht
    filter_upwards [hc, clockPath_coordinate_ae t.toNNReal,
      brownianCore_coeFn t.toNNReal 1] with ω hc hw h1
    rw [← hc, ht, h1, value_one]
    simpa [PredictableRealL2.horizon, hp, sigma] using hw.symm
  · rw [horizonValue, indicator_of_notMem hp] at ht
    filter_upwards [hc, Lp.coeFn_zero ℝ 2 gaussianProduct] with ω hc hz
    rw [← hc, ht, hz]
    simp [PredictableRealL2.horizon, hp]

private theorem field_memLp (T : ℝ≥0) :
    MemLp (fun z => signum ((hermiteIntegrand 1 T : TimeProbabilityL2) z))
      2 timeProbability := by
  have hconst : MemLp ((PredictableRealL2.horizon T).indicator
      (fun _ : ℝ × SampleSpace => (1 : ℝ))) 2 timeProbability := by
    apply (memLp_indicator_iff_restrict (PredictableRealL2.horizon_measurable T)).mpr
    exact memLp_const 1
  apply hconst.mono'
    (signum_measurable.comp (Lp.stronglyMeasurable _).measurable).aestronglyMeasurable
  filter_upwards [brownian_field_joint T] with z hz
  by_cases ht : z ∈ PredictableRealL2.horizon T
  · simpa [ht] using signum_bound ((hermiteIntegrand 1 T : TimeProbabilityL2) z)
  · simp [hz, ht, signum_zero]

def field (T : ℝ≥0) : TimeProbabilityL2 := (field_memLp T).toLp _

theorem field_coeFn (T : ℝ≥0) : field T =ᵐ[timeProbability]
    (PredictableRealL2.horizon T).indicator (fun z => signum (sigma z)) := by
  filter_upwards [MemLp.coeFn_toLp (field_memLp T), brownian_field_joint T] with z hf hb
  change field T z = _ at hf
  rw [hf, hb]
  by_cases ht : z ∈ PredictableRealL2.horizon T <;> simp [ht, signum_zero]

theorem field_predictable (T : ℝ≥0) : field T ∈ fullPredictable := by
  rw [mem_fullPredictable_iff]
  have h := (mem_fullPredictable_iff _).mp (hermiteIntegrand 1 T).property
  constructor
  · obtain ⟨g, hg, he⟩ := h.1
    refine ⟨signum ∘ g, (signum_measurable.comp hg.measurable).stronglyMeasurable, ?_⟩
    filter_upwards [MemLp.coeFn_toLp (field_memLp T), he] with z hf he
    change field T z = _ at hf
    change field T z = signum (g z)
    rw [hf, he]
  · filter_upwards [MemLp.coeFn_toLp (field_memLp T), h.2] with z hf hs hz
    change field T z = _ at hf
    rw [hf, hs hz, signum_zero]

def predictableField (T : ℝ≥0) : fullPredictable := ⟨field T, field_predictable T⟩

def terminal (T : ℝ≥0) : GaussianL2 := itoIntegral (predictableField T)

theorem terminal_centered (T : ℝ≥0) : ∫ ω, terminal T ω ∂gaussianProduct = 0 :=
  itoIntegral_centered _

theorem field_square (T : ℝ≥0) : (fun z => field T z ^ 2) =ᵐ[timeProbability]
    (PredictableRealL2.horizon T).indicator (fun _ => (1 : ℝ)) := by
  have hn := (ae_eq_restrict_iff_indicator_ae_eq
    (PredictableRealL2.horizon_measurable T)).mp
      ((sigma_nonzero T).mono (fun z hz => signum_sq hz))
  filter_upwards [field_coeFn T, hn] with z hf hn
  rw [hf]
  by_cases ht : z ∈ PredictableRealL2.horizon T
  · simpa [ht] using hn
  · simp [ht]

theorem field_norm_sq (T : ℝ≥0) : ‖field T‖ ^ 2 = (T : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, L2_inner_eq_integral]
  calc
    _ = ∫ z, (PredictableRealL2.horizon T).indicator
        (fun _ => (1 : ℝ)) z ∂timeProbability := by
      apply integral_congr_ae
      filter_upwards [field_square T] with z hz
      simpa [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs] using hz
    _ = (T : ℝ) := by
      rw [integral_indicator (PredictableRealL2.horizon_measurable T)]
      change (∫ _ : ℝ × SampleSpace, (1 : ℝ) ∂base T) = _
      rw [show base T = (volume.restrict (Ioc 0 (T : ℝ))).prod gaussianProduct from
        PredictableRealL2.horizonMeasure_eq_product T gaussianProduct]
      simp [Measure.real, Measure.prod_apply, Real.volume_Ioc]

theorem terminal_norm_sq (T : ℝ≥0) : ‖terminal T‖ ^ 2 = (T : ℝ) := by
  change ‖itoIntegral (predictableField T)‖ ^ 2 = _
  rw [itoIntegral.norm_map]
  exact field_norm_sq T

end OperatorDerivativeRewrite.Foundation.BrownianSignIntegral
