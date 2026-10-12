import Foundation.GaussianHermiteMartingale
import Foundation.GaussianPolynomialIto

/-! Conditional polynomial Itô: genuine heat-polynomial martingales and compensated L2 identities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set MvPolynomial
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianPolynomialMartingale
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 GaussianProductDerivative
open GaussianPredictableFull GaussianPredictableCutoff GaussianConditionalIto
open GaussianConditionalClarkOcone GaussianHermiteMartingale GaussianPolynomialProcess
open GaussianPolynomialHeat GaussianPolynomialIto

theorem cut_polynomial_integrand (S T : ℝ≥0) (p : SpaceTimePolynomial)
    (U V : fullPredictable) (hU : scalarCurry (U : TimeProbabilityL2) = spatialField T p)
    (hV : scalarCurry (V : TimeProbabilityL2) = spatialField (min S T) p) :
    predictableCut S U = V := by
  apply Subtype.ext
  apply scalarCurry.injective
  apply Lp.ext
  filter_upwards [scalarCurry_cut S U, spatialField_coeFn T p,
    spatialField_coeFn (min S T) p] with t hc ht hm
  change scalarCurry (cut S U) t = _
  rw [hc, hU, hV, hm]
  by_cases hs : t ∈ Ioc 0 (S : ℝ)
  · rw [indicator_of_mem hs, ht]
    have he : t ∈ Ioc 0 (min (S : ℝ) (T : ℝ)) ↔ t ∈ Ioc 0 (T : ℝ) := by
      simp only [mem_Ioc, le_min_iff]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hs.2, h.2⟩⟩
    by_cases hT : t ∈ Ioc 0 (T : ℝ) <;> simp [NNReal.coe_min, hT, he]
  · have he : t ∉ Ioc 0 (min (S : ℝ) (T : ℝ)) :=
      fun hh => hs ⟨hh.1, hh.2.trans (min_le_left _ _)⟩
    simp [hs, NNReal.coe_min, he]

/-- Every polynomial's genuine heat-compensated process has the martingale conditional
identity in Gaussian L2. The time integral in noiseTarget is the verified Bochner integral. -/
theorem pastProjection_noiseTarget (p : SpaceTimePolynomial) (S T : ℝ≥0) :
    pastProjection S (noiseTarget T p) = noiseTarget (min S T) p := by
  obtain ⟨U, hU, hJU⟩ := polynomial_representation T p
  obtain ⟨V, hV, hJV⟩ := polynomial_representation (min S T) p
  rw [← hJU, pastProjection_integral, cut_polynomial_integrand S T p U V hU hV, hJV]

theorem valueL2_zero (p : SpaceTimePolynomial) :
    valueL2 0 p = eval ![(0 : ℝ), 0] p • gaussianOne := by
  apply Lp.ext
  filter_upwards [valueL2_coeFn 0 p, process_zero_ae,
    Lp.coeFn_smul (eval ![(0 : ℝ), 0] p) gaussianOne, gaussianOne_coeFn] with ω hp hz hs h1
  simp only [hp, NNReal.coe_zero, hz, hs, Pi.smul_apply, h1, smul_eq_mul, mul_one]

theorem evaluation_stronglyAdapted (p : SpaceTimePolynomial) :
    StronglyAdapted naturalFiltration (fun t ω => eval ![(t : ℝ), process t ω] p) := by
  intro t
  letI : MeasurableSpace SampleSpace := naturalFiltration t
  apply (p.continuous_eval.measurable.comp ?_).stronglyMeasurable
  apply Measurable.of_eval
  intro i
  fin_cases i
  · exact measurable_const
  · exact (process_stronglyAdapted t).measurable

theorem evaluation_integrable (p : SpaceTimePolynomial) (T : ℝ≥0) :
    Integrable (fun ω => eval ![(T : ℝ), process T ω] p) gaussianProduct :=
  ((Lp.memLp (valueL2 T p)).integrable (by norm_num)).congr (valueL2_coeFn T p)

theorem valueL2_mem_past (p : SpaceTimePolynomial) (T : ℝ≥0) : valueL2 T p ∈ pastL2 T :=
  (evaluation_stronglyAdapted p T).aestronglyMeasurable.congr (valueL2_coeFn T p).symm

theorem pastProjection_heatPolynomial (p : SpaceTimePolynomial) (hp : heat p = 0)
    (S T : ℝ≥0) : pastProjection S (valueL2 T p) = valueL2 (min S T) p := by
  have h := pastProjection_noiseTarget p S T
  simp only [noiseTarget_apply, hp, map_zero, intervalIntegral.integral_zero, sub_zero,
    map_sub, valueL2_zero, map_smul, pastProjection_one] at h
  exact sub_left_injective h

/-- The PDE hypothesis is the explicit polynomial equation Dt p + (1/2) Dxx p = 0.
The conclusion is Mathlib's martingale predicate for actual Brownian evaluations. -/
theorem heatPolynomial_martingale (p : SpaceTimePolynomial) (hp : heat p = 0) :
    Martingale (fun (t : ℝ≥0) ω => eval ![(t : ℝ), process t ω] p) naturalFiltration gaussianProduct := by
  refine ⟨evaluation_stronglyAdapted p, ?_⟩
  intro S T hST
  have hc := pastProjection_ae S (valueL2 T p)
  rw [pastProjection_heatPolynomial p hp, min_eq_left hST] at hc
  exact ((condExp_congr_ae (valueL2_coeFn T p)).symm.trans hc.symm).trans (valueL2_coeFn S p)

/-- Conditional Dynkin identity; both time integrals are genuine Gaussian-L2 Bochner integrals. -/
theorem polynomial_conditional_drift (p : SpaceTimePolynomial) (S T : ℝ≥0) (hST : S ≤ T) :
    pastProjection S (valueL2 T p) - valueL2 S p =
      pastProjection S (timeIntegral T (heat p)) - timeIntegral S (heat p) := by
  have h := pastProjection_noiseTarget p S T
  change pastProjection S (valueL2 T p - valueL2 0 p - timeIntegral T (heat p)) =
    valueL2 (min S T) p - valueL2 0 p - timeIntegral (min S T) (heat p) at h
  rw [min_eq_left hST, map_sub, map_sub, valueL2_zero, map_smul, pastProjection_one] at h
  linear_combination (norm := module) h

theorem pastProjection_timeIntegral (p : SpaceTimePolynomial) (T : ℝ≥0) :
    pastProjection T (timeIntegral T p) = timeIntegral T p := by
  change pastProjection T (∫ t in 0..(T : ℝ), valueL2 t.toNNReal p) = _
  rw [← (pastProjection T).intervalIntegral_comp_comm (valueL2_intervalIntegrable p T)]
  apply intervalIntegral.integral_congr
  intro t ht
  change pastProjection T (valueL2 t.toNNReal p) = valueL2 t.toNNReal p
  apply Submodule.starProjection_eq_self_iff.mpr
  have htT : t.toNNReal ≤ T := by
    apply Real.toNNReal_le_iff_le_coe.mpr
    exact (uIcc_of_le T.coe_nonneg ▸ ht).2
  exact (valueL2_mem_past p t.toNNReal).mono (naturalFiltration.mono htT)

/-- Standard conditional Dynkin formula with the heat drift integrated from S to T.
It uses actual L2-valued Bochner time integration and no pointwise path-integral assumption. -/
theorem polynomial_conditional_dynkin (p : SpaceTimePolynomial) (S T : ℝ≥0) (hST : S ≤ T) :
    pastProjection S (valueL2 T p) - valueL2 S p =
      pastProjection S (∫ t in (S : ℝ)..(T : ℝ), valueL2 t.toNNReal (heat p)) := by
  rw [polynomial_conditional_drift p S T hST, ← pastProjection_timeIntegral (heat p) S,
    ← map_sub]
  congr 1
  have hc := ((valueL2_continuous (heat p)).comp continuous_real_toNNReal)
  have h := intervalIntegral.integral_add_adjacent_intervals
    (valueL2_intervalIntegrable (heat p) S) (hc.intervalIntegrable (S : ℝ) (T : ℝ))
  change timeIntegral T (heat p) - timeIntegral S (heat p) = _
  change timeIntegral S (heat p) + _ = timeIntegral T (heat p) at h
  rw [← h, add_sub_cancel_left]

end OperatorDerivativeRewrite.Foundation.GaussianPolynomialMartingale
