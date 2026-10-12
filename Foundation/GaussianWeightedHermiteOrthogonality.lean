import Foundation.GaussianHermiteMartingale
import Foundation.GaussianWeightedIntegrand

/-! Exact second moments and martingale-difference orthogonality for arbitrary L2 past weights. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianWeightedHermiteOrthogonality
open InfiniteGaussian GaussianTimeProcess GaussianTimeSpaceHermite GaussianTimeProductL2
open GaussianProductDerivative GaussianPredictableFull GaussianPredictableCutoff
open GaussianConditionalIto GaussianHermiteMartingale GaussianWeightedHermite
open GaussianPastFutureProducts GaussianHermiteFutureError
open GaussianPredictableStep (pastCoefficient)

variable (s : ℝ≥0) (a : (Iic s → ℝ) → ℝ) (ha : Measurable a)
  (hA : MemLp (pastCoefficient process s a) 2 gaussianProduct)

theorem coefficient_norm_sq (r : ℝ≥0) (n : ℕ) :
    ‖coefficient s a ha hA r n‖ ^ 2 =
      (∫ ω, pastCoefficient process s a ω ^ 2 ∂gaussianProduct) *
        (n.factorial : ℝ) * (r : ℝ) ^ n := by
  have he : (∫ ω, value n (process (s + r) ω - process s ω) r ^ 2 ∂gaussianProduct) =
      (n.factorial : ℝ) * (r : ℝ) ^ n := by
    rw [← GaussianShiftedHermite.incrementCore_norm_sq s r n, BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [GaussianShiftedHermite.incrementCore_coeFn s r n] with ω hω
    simp only [hω, Real.norm_eq_abs, sq_abs]
  calc
    _ = ∫ ω, (pastCoefficient process s a ω *
        value n (process (s + r) ω - process s ω) r) ^ 2 ∂gaussianProduct := by
      rw [BochnerL2Dominated.norm_sq_integral]
      apply integral_congr_ae
      filter_upwards [coefficient_coeFn s a ha hA r n] with ω hω
      simp only [hω, Real.norm_eq_abs, sq_abs]
    _ = _ := by
      have hp := past_future_sq_integral s ha (value_functional_measurable n r) hA
        (GaussianShiftedHermite.incrementCore_memLp s r n 2 (by simp))
      simp only [futureValue, futureProcess] at hp
      rw [hp, he]
      ring

theorem cut_weightedIntegrand_of_le (S : ℝ≥0) (hS : S ≤ s) (n : ℕ) (r : ℝ≥0) :
    predictableCut S (hermiteIntegrand s a ha hA n r) = 0 := by
  apply Subtype.ext
  apply scalarCurry.injective
  apply Lp.ext
  filter_upwards [scalarCurry_cut S (hermiteIntegrand s a ha hA n r),
    GaussianWeightedIntegrand.hermiteIntegrand_slices s a ha hA n r,
    Lp.coeFn_zero GaussianL2 2 volume] with t hc ht h0
  change scalarCurry (cut S (hermiteIntegrand s a ha hA n r)) t = scalarCurry 0 t
  rw [hc, map_zero, h0]
  by_cases hm : t ∈ Ioc 0 (S : ℝ)
  · rw [indicator_of_mem hm, ht]
    have hn : t - s ∉ Ioc 0 (r : ℝ) := by
      intro hh
      have hts : t ≤ s := hm.2.trans hS
      linarith [hh.1]
    exact indicator_of_notMem hn _
  · exact indicator_of_notMem hm _

theorem pastProjection_coefficient_zero (S : ℝ≥0) (hS : S ≤ s) (n : ℕ) (r : ℝ≥0) :
    pastProjection S (coefficient s a ha hA r (n + 1)) = 0 := by
  rw [hermite_representation s a ha hA n r, map_smul, pastProjection_integral,
    cut_weightedIntegrand_of_le s a ha hA S hS n r, map_zero, smul_zero]

theorem past_inner_coefficient_zero (G : GaussianL2) (hG : G ∈ pastL2 s) (n : ℕ) (r : ℝ≥0) :
    inner ℝ G (coefficient s a ha hA r (n + 1)) = 0 := by
  have hself : (pastL2 s).starProjection G = G := Submodule.starProjection_eq_self_iff.mpr hG
  rw [← hself, (pastL2 s).inner_starProjection_left_eq_right]
  change inner ℝ G (pastProjection s (coefficient s a ha hA r (n + 1))) = 0
  rw [pastProjection_coefficient_zero s a ha hA s le_rfl, inner_zero_right]

theorem coefficient_inner_of_disjoint (t : ℝ≥0) (b : (Iic t → ℝ) → ℝ) (hb : Measurable b)
    (hB : MemLp (pastCoefficient process t b) 2 gaussianProduct)
    (r u : ℝ≥0) (h : s + r ≤ t) (n m : ℕ) :
    inner ℝ (coefficient s a ha hA r n) (coefficient t b hb hB u (m + 1)) = 0 :=
  past_inner_coefficient_zero t b hb hB _
    ((coefficient_past s a ha hA r n).mono (naturalFiltration.mono h)) m u

end OperatorDerivativeRewrite.Foundation.GaussianWeightedHermiteOrthogonality
