import Foundation.GaussianConditionalClarkOcone
import Foundation.GaussianPolynomialProcess
import Mathlib.Probability.Martingale.Basic

/-! All time-space Hermite orders are actual raw Brownian martingales. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianHermiteMartingale
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 GaussianProductDerivative
open GaussianPredictableFull GaussianPredictableCutoff GaussianConditionalIto
open GaussianConditionalClarkOcone GaussianTimeSpaceHermite GaussianHermiteRepresentation
open GaussianHermiteIntegrand GaussianPolynomialProcess

theorem scalarCurry_cut (T : ℝ≥0) (U : TimeProbabilityL2) :
    scalarCurry (cut T U) =ᵐ[volume] (Ioc 0 (T : ℝ)).indicator (scalarCurry U) := by
  filter_upwards [scalarCurry_coeFn (cut T U), scalarCurry_coeFn U,
    ae_ae_of_ae_prod (cut_coeFn T U)] with t hc hu ht
  by_cases hm : t ∈ Ioc 0 (T : ℝ)
  · rw [indicator_of_mem hm]
    apply Lp.ext
    filter_upwards [hc, hu, ht] with ω hc hu ht
    rw [hc, hu, ht]
    exact indicator_of_mem (show (t, ω) ∈ PredictableRealL2.horizon T from ⟨hm, mem_univ _⟩) _
  · rw [indicator_of_notMem hm]
    apply Lp.ext
    filter_upwards [hc, ht, Lp.coeFn_zero ℝ 2 gaussianProduct] with ω hc ht h0
    rw [hc, ht, h0]
    exact indicator_of_notMem (fun hh => hm hh.1) _

theorem cut_hermiteIntegrand (n : ℕ) (S T : ℝ≥0) :
    predictableCut S (hermiteIntegrand n T) = hermiteIntegrand n (min S T) := by
  apply Subtype.ext
  apply scalarCurry.injective
  apply Lp.ext
  filter_upwards [scalarCurry_cut S (hermiteIntegrand n T), hermiteIntegrand_slices n T,
    hermiteIntegrand_slices n (min S T)] with t hc ht hm
  change scalarCurry (cut S (hermiteIntegrand n T)) t = _
  rw [hc, hm]
  by_cases hs : t ∈ Ioc 0 (S : ℝ)
  · rw [indicator_of_mem hs, ht]
    have he : t ∈ Ioc 0 (min (S : ℝ) (T : ℝ)) ↔ t ∈ Ioc 0 (T : ℝ) := by
      simp only [mem_Ioc, le_min_iff]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hs.2, h.2⟩⟩
    by_cases hT : t ∈ Ioc 0 (T : ℝ) <;> simp [horizonValue, NNReal.coe_min, hT, he]
  · have he : t ∉ Ioc 0 (min (S : ℝ) (T : ℝ)) :=
      fun hh => hs ⟨hh.1, hh.2.trans (min_le_left _ _)⟩
    simp [hs, horizonValue, NNReal.coe_min, he]

theorem pastProjection_brownianCore (n : ℕ) (S T : ℝ≥0) :
    pastProjection S (brownianCore T n : GaussianL2) = brownianCore (min S T) n := by
  cases n with
  | zero => simp only [brownianCore_zero_degree, pastProjection_one]
  | succ n =>
    rw [hermite_representation n T, map_smul, pastProjection_integral,
      cut_hermiteIntegrand, ← hermite_representation]

theorem hermite_condExp (n : ℕ) (S T : ℝ≥0) (hST : S ≤ T) :
    gaussianProduct[(fun ω => value n (process T ω) T) | naturalFiltration S]
      =ᵐ[gaussianProduct] fun ω => value n (process S ω) S := by
  have hc := pastProjection_ae S (brownianCore T n)
  rw [pastProjection_brownianCore, min_eq_left hST] at hc
  exact ((condExp_congr_ae (brownianCore_coeFn T n)).symm.trans hc.symm).trans
    (brownianCore_coeFn S n)

theorem hermite_integrable (n : ℕ) (T : ℝ≥0) :
    Integrable (fun ω => value n (process T ω) T) gaussianProduct :=
  ((Lp.memLp (brownianCore T n : GaussianL2)).integrable (by norm_num)).congr
    (brownianCore_coeFn T n)

/-- Mathlib's genuine martingale predicate for the actual adapted polynomial functions. -/
theorem hermite_martingale (n : ℕ) :
    Martingale (fun t ω => value n (process t ω) t) naturalFiltration gaussianProduct := by
  constructor
  · intro t
    letI : MeasurableSpace SampleSpace := naturalFiltration t
    exact ((polynomial t n).continuous_eval.measurable.comp
      (Measurable.of_eval fun _ : Unit => (process_stronglyAdapted t).measurable)).stronglyMeasurable
  · exact fun S T hST => hermite_condExp n S T hST

end OperatorDerivativeRewrite.Foundation.GaussianHermiteMartingale
