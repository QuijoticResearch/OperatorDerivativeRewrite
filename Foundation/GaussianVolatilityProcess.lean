import Foundation.GaussianConditionalIto

/-! Actual finite-horizon stochastic-volatility martingales. No Malliavin
regularity or positivity is needed for the martingale construction itself. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianVolatilityProcess
open InfiniteGaussian GaussianTimeProductL2 GaussianTimeProcess
open GaussianPredictableFull GaussianPredictableCutoff GaussianConditionalIto
open PredictableRealL2

def value (U : fullPredictable) (T : ℝ≥0) : GaussianL2 :=
  itoIntegral (predictableCut T U)

theorem value_mem_past (U : fullPredictable) (T : ℝ≥0) : value U T ∈ pastL2 T :=
  integral_cut_mem_past T U

theorem cut_cut (U : fullPredictable) (S T : ℝ≥0) :
    predictableCut S (predictableCut T U) = predictableCut (min S T) U := by
  apply Subtype.ext
  exact GaussianPredictableCutoff.cut_cut S T U

theorem value_projection (U : fullPredictable) (S T : ℝ≥0) :
    pastProjection S (value U T) = value U (min S T) := by
  rw [value, pastProjection_integral, cut_cut]
  rfl

theorem value_condExp (U : fullPredictable) (S T : ℝ≥0) :
    gaussianProduct[value U T | naturalFiltration S] =ᵐ[gaussianProduct]
      value U (min S T) := by
  have h := pastProjection_ae S (value U T)
  rw [value_projection] at h
  exact h.symm

/-- A genuinely adapted representative; its equality to the actual integral is proved below. -/
def process (U : fullPredictable) (T : ℝ≥0) : SampleSpace → ℝ :=
  gaussianProduct[value U T | naturalFiltration T]

theorem process_ae (U : fullPredictable) (T : ℝ≥0) :
    process U T =ᵐ[gaussianProduct] value U T := by
  simpa only [process, min_self] using value_condExp U T T

theorem process_stronglyAdapted (U : fullPredictable) :
    StronglyAdapted naturalFiltration (process U) :=
  fun _ => stronglyMeasurable_condExp

theorem process_memLp (U : fullPredictable) (T : ℝ≥0) :
    MemLp (process U T) 2 gaussianProduct :=
  (Lp.memLp (value U T)).ae_eq (process_ae U T).symm

theorem process_condExp (U : fullPredictable) (S T : ℝ≥0) (hST : S ≤ T) :
    gaussianProduct[process U T | naturalFiltration S] =ᵐ[gaussianProduct] process U S := by
  have h := value_condExp U S T
  rw [min_eq_left hST] at h
  exact ((condExp_congr_ae (process_ae U T)).trans h).trans (process_ae U S).symm

theorem process_martingale (U : fullPredictable) :
    Martingale (process U) naturalFiltration gaussianProduct :=
  ⟨process_stronglyAdapted U, fun S T hST => process_condExp U S T hST⟩

theorem process_centered (U : fullPredictable) (T : ℝ≥0) :
    ∫ ω, process U T ω ∂gaussianProduct = 0 := by
  rw [integral_congr_ae (process_ae U T)]
  exact itoIntegral_centered _

theorem value_inner (U V : fullPredictable) (S T : ℝ≥0) :
    inner ℝ (value U S) (value V T) =
      inner ℝ (U : TimeProbabilityL2) (cut (min S T) V) := by
  rw [value, value, itoIntegral.inner_map_map]
  change inner ℝ (cut S U) (cut T V) = _
  rw [cut_inner, GaussianPredictableCutoff.cut_cut]

theorem process_pair_integrable (U V : fullPredictable) (S T : ℝ≥0) :
    Integrable (fun ω => process U S ω * process V T ω) gaussianProduct :=
  mul_L2_integrable (process_memLp U S) (process_memLp V T)

theorem process_product_integral (U V : fullPredictable) (S T : ℝ≥0) :
    ∫ ω, process U S ω * process V T ω ∂gaussianProduct =
      ∫ z in horizon (min S T), (U : TimeProbabilityL2) z * V.val z ∂timeProbability := by
  calc
    _ = inner ℝ (value U S) (value V T) := by
      rw [L2_inner_eq_integral]
      apply integral_congr_ae
      filter_upwards [process_ae U S, process_ae V T] with ω hU hV
      simp [hU, hV, mul_comm]
    _ = inner ℝ (U : TimeProbabilityL2) (cut (min S T) V) := value_inner U V S T
    _ = _ := by
      rw [L2_inner_eq_integral, ← integral_indicator (horizon_measurable (min S T))]
      apply integral_congr_ae
      filter_upwards [cut_coeFn (min S T) V] with z hz
      rw [hz]
      by_cases h : z ∈ horizon (min S T) <;> simp [h, mul_comm]

theorem process_isometry (U : fullPredictable) (T : ℝ≥0) :
    ∫ ω, process U T ω ^ 2 ∂gaussianProduct =
      ∫ z in horizon T, (U : TimeProbabilityL2) z ^ 2 ∂timeProbability := by
  simpa only [min_self, pow_two] using process_product_integral U U T T

/-- Bounded predictable coefficients are square integrable on each finite horizon;
no derivative-domain condition is hidden in this construction. -/
theorem bounded_memLp (T : ℝ≥0) (σ : ℝ × SampleSpace → ℝ)
    (hσ : Measurable[predictable naturalFiltration] σ) (C : ℝ)
    (hC : ∀ z ∈ horizon T, ‖σ z‖ ≤ C) :
    MemLp σ 2 (horizonMeasure T gaussianProduct) := by
  apply MemLp.of_bound
    (hσ.mono (predictable_le naturalFiltration) le_rfl).aestronglyMeasurable C
  filter_upwards [ae_restrict_mem (horizon_measurable T)] with z hz
  exact hC z hz

def boundedField (T : ℝ≥0) (σ : ℝ × SampleSpace → ℝ)
    (hσ : Measurable[predictable naturalFiltration] σ) (C : ℝ)
    (hC : ∀ z ∈ horizon T, ‖σ z‖ ≤ C) : fullPredictable :=
  ⟨L2ZeroExtension (horizon_measurable T) ((bounded_memLp T σ hσ C hC).toLp σ), by
    rw [← closedProductSteps_eq_fullPredictable]
    apply GaussianPredictableHorizon.zeroExtension_mem
    exact hσ.stronglyMeasurable.aestronglyMeasurable.congr
      (MemLp.coeFn_toLp (bounded_memLp T σ hσ C hC)).symm⟩

theorem boundedField_coeFn (T : ℝ≥0) (σ : ℝ × SampleSpace → ℝ)
    (hσ : Measurable[predictable naturalFiltration] σ) (C : ℝ)
    (hC : ∀ z ∈ horizon T, ‖σ z‖ ≤ C) :
    (boundedField T σ hσ C hC : TimeProbabilityL2) =ᵐ[timeProbability]
      (horizon T).indicator σ := by
  exact (L2ZeroExtension_coeFn (horizon_measurable T) _).trans
    ((ae_eq_restrict_iff_indicator_ae_eq (horizon_measurable T)).mp
      (MemLp.coeFn_toLp (bounded_memLp T σ hσ C hC)))

/-- Positivity is an explicit hypothesis on the raw coefficient, and survives
in the actual finite-horizon L² representative. -/
theorem boundedField_lower (T : ℝ≥0) (σ : ℝ × SampleSpace → ℝ)
    (hσ : Measurable[predictable naturalFiltration] σ) (C : ℝ)
    (hC : ∀ z ∈ horizon T, ‖σ z‖ ≤ C) (ε : ℝ)
    (hε : ∀ z ∈ horizon T, ε ≤ σ z) :
    ∀ᵐ z ∂timeProbability, z ∈ horizon T →
      ε ≤ (boundedField T σ hσ C hC : TimeProbabilityL2) z := by
  filter_upwards [boundedField_coeFn T σ hσ C hC] with z hz hzt
  rw [hz, indicator_of_mem hzt]
  exact hε z hzt
end OperatorDerivativeRewrite.Foundation.GaussianVolatilityProcess
