import Foundation.FourierPathMeasuredKernels
import Foundation.FourierPathDualDensitySamplers

/-! Actual finite weighted path expectations are uniformly contractive on completed Fourier tests. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathSamplerOperators
open L1SeriesSynthesis HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open HigherHeatInterpolatedPaths HigherHeatWeightedPaths

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def finite (k : ℕ) (hk : 0 < k) (H : ℝ≥0) (hH : 0 < H) (n : ℕ) :
    TestSpace levels ξ →L[ℂ] ℂ :=
  FourierPathMeasuredKernels.functional (probabilityPath k hk H hH n) levels ξ
    (fun ω => (pathWeight k hk H hH n ω : ℂ)) (pathWeight_integrable k hk H hH n).ofReal
    id measurable_id

theorem finite_apply (k : ℕ) (hk : 0 < k) (H : ℝ≥0) (hH : 0 < H) (n : ℕ)
    (q : TestSpace levels ξ) : finite levels ξ k hk H hH n q =
      ∫ ω, pathWeight k hk H hH n ω • realize levels ξ q ω ∂probabilityPath k hk H hH n := by
  simp only [finite, FourierPathMeasuredKernels.functional_apply, id_eq, Complex.real_smul]

theorem finite_bound (k : ℕ) (hk : 0 < k) (H : ℝ≥0) (hH : 0 < H) (n : ℕ)
    (q : TestSpace levels ξ) : ‖finite levels ξ k hk H hH n q‖ ≤ ‖q‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a,ha,hna⟩ := Submodule.Quotient.norm_mk_lt q hε
  have he : (fun ω => realize levels ξ q ω) =
      HigherHeatMixedFourierPaths.series (spectrumLevels levels) (spectrumFrequency levels ξ) a := by
    funext ω
    rw [← ha]
    change realization levels ξ a ω = _
    exact realization_apply levels ξ a ω
  rw [finite_apply, ← signedPath_expectation k hk H hH n _ (test_integrable levels ξ k hk H hH n q)]
  rw [he]
  exact (HigherHeatMixedFourierPaths.series_expectation_bound _ _ a (coeff_summable a)
    k hk H hH n).trans ((coeff_norm a).trans_le hna.le)

theorem finite_norm (k : ℕ) (hk : 0 < k) (H : ℝ≥0) (hH : 0 < H) (n : ℕ) :
    ‖finite levels ξ k hk H hH n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  simpa only [one_mul] using finite_bound levels ξ k hk H hH n q

theorem finite_tendsto (k : ℕ) (hk : 0 < k) (H : ℝ≥0) (hH : 0 < H) (q : TestSpace levels ξ) :
    Tendsto (fun n => finite levels ξ k hk H hH n q) atTop (𝓝 (expectation levels ξ k hk H hH q)) := by
  simp only [finite_apply]
  exact weighted_expectation_limit levels ξ k hk H hH q

end OperatorDerivativeRewrite.Foundation.FourierPathSamplerOperators
