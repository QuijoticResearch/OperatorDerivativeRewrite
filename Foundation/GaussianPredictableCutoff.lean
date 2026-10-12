import Foundation.GaussianPredictableFull
import Foundation.BochnerL2Dominated

/-! Actual finite-time cutoffs on the independently defined predictable L² space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianPredictableCutoff
open InfiniteGaussian GaussianTimeProductL2 GaussianTimeHilbert GaussianTimeProcess
open GaussianPredictableFull GaussianPredictableL2Completion PredictableRealL2

def cut (T : ℝ≥0) : TimeProbabilityL2 →L[ℝ] TimeProbabilityL2 :=
  (L2ZeroExtensionIsometry (μ := timeProbability) (horizon_measurable T)).toContinuousLinearMap.comp
    (LpToLpRestrictCLM _ ℝ ℝ timeProbability 2 (horizon T))

theorem cut_coeFn (T : ℝ≥0) (U : TimeProbabilityL2) :
    cut T U =ᵐ[timeProbability] (horizon T).indicator U := by
  exact (L2ZeroExtension_coeFn (horizon_measurable T) _).trans
    ((ae_eq_restrict_iff_indicator_ae_eq (horizon_measurable T)).mp
      (LpToLpRestrictCLM_coeFn ℝ (horizon T) U))

theorem cut_norm_le (T : ℝ≥0) (U : TimeProbabilityL2) : ‖cut T U‖ ≤ ‖U‖ := by
  change ‖L2ZeroExtension (horizon_measurable T) _‖ ≤ _
  rw [L2ZeroExtension_norm]
  exact norm_Lp_toLp_restrict_le _ _

theorem cut_mem (T : ℝ≥0) (U : fullPredictable) : cut T U ∈ fullPredictable := by
  have h := GaussianPredictableHorizon.zeroExtension_mem T
    (LpToLpRestrictCLM _ ℝ ℝ timeProbability 2 (horizon T) U)
    (U.property.1.restrict.congr
      (LpToLpRestrictCLM_coeFn ℝ (horizon T) (U : TimeProbabilityL2)).symm)
  change L2ZeroExtension (horizon_measurable T)
    (LpToLpRestrictCLM _ ℝ ℝ timeProbability 2 (horizon T) (U : TimeProbabilityL2)) ∈ _
  simpa only [closedProductSteps_eq_fullPredictable] using h

def predictableCut (T : ℝ≥0) : fullPredictable →L[ℝ] fullPredictable :=
  ((cut T).comp fullPredictable.subtypeL).codRestrict fullPredictable (cut_mem T)

theorem predictableCut_coe (T : ℝ≥0) (U : fullPredictable) :
    (predictableCut T U : TimeProbabilityL2) = cut T U := rfl

theorem cut_inner (T : ℝ≥0) (U V : TimeProbabilityL2) :
    inner ℝ (cut T U) V = inner ℝ U (cut T V) := by
  rw [L2_inner_eq_integral, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [cut_coeFn T U, cut_coeFn T V] with z hu hv
  rw [hu, hv]
  by_cases hz : z ∈ horizon T <;> simp [hz]

theorem cut_cut (S T : ℝ≥0) (U : TimeProbabilityL2) :
    cut S (cut T U) = cut (min S T) U := by
  apply Lp.ext
  filter_upwards [cut_coeFn S (cut T U), cut_coeFn T U, cut_coeFn (min S T) U]
    with z hs ht hm
  rw [hs, hm]
  by_cases hz : z ∈ horizon S
  · rw [indicator_of_mem hz, ht]
    by_cases hzt : z ∈ horizon T
    · have hzm : z ∈ horizon (min S T) := ⟨⟨hz.1.1, le_min hz.1.2 hzt.1.2⟩, mem_univ _⟩
      simp [hzt, hzm]
    · have hzm : z ∉ horizon (min S T) := fun hh => hzt
        ⟨⟨hh.1.1, hh.1.2.trans (min_le_right _ _)⟩, mem_univ _⟩
      simp [hzt, hzm]
  · have hzm : z ∉ horizon (min S T) := fun hh => hz
      ⟨⟨hh.1.1, hh.1.2.trans (min_le_left _ _)⟩, mem_univ _⟩
    simp [hz, hzm]

theorem cut_tensor (T s t : ℝ≥0) (A : GaussianL2) :
    cut T (productTensor (intervalVector s t) A) =
      productTensor (intervalVector s (min t T)) A := by
  apply Lp.ext
  have ht := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
    (ν := gaussianProduct)).ae_eq_comp (intervalVector_coeFn s t)
  have hm := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
    (ν := gaussianProduct)).ae_eq_comp (intervalVector_coeFn s (min t T))
  filter_upwards [cut_coeFn T (productTensor (intervalVector s t) A),
    productTensor_coeFn (intervalVector s t) A,
    productTensor_coeFn (intervalVector s (min t T)) A, ht, hm] with z hc ha hb ht hm
  simp only [Function.comp_apply] at ht hm
  rw [hc, hb, hm]
  by_cases hz : z ∈ horizon T
  · rw [indicator_of_mem hz, ha, ht]
    have hi : z.1 ∈ Ioc (s : ℝ) (min (t : ℝ) (T : ℝ)) ↔ z.1 ∈ Ioc (s : ℝ) (t : ℝ) := by
      simp only [mem_Ioc, le_min_iff]
      exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hz.1.2⟩⟩
    by_cases hi' : z.1 ∈ Ioc (s : ℝ) (t : ℝ) <;> simp [hi', hi]
  · have hi : z.1 ∉ Ioc (s : ℝ) (min (t : ℝ) (T : ℝ)) := by
      intro hh
      exact hz ⟨⟨s.coe_nonneg.trans_lt hh.1,
        hh.2.trans (show (min t T : ℝ≥0) ≤ T from min_le_right _ _)⟩, mem_univ _⟩
    simp [hz, hi]

theorem sub_cut_tensor (T s t : ℝ≥0) (A : GaussianL2) :
    productTensor (intervalVector s t) A - cut T (productTensor (intervalVector s t) A) =
      productTensor (intervalVector (max s T) t) A := by
  apply Lp.ext
  have ht := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
    (ν := gaussianProduct)).ae_eq_comp (intervalVector_coeFn s t)
  have hm := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
    (ν := gaussianProduct)).ae_eq_comp (intervalVector_coeFn (max s T) t)
  filter_upwards [Lp.coeFn_sub (productTensor (intervalVector s t) A)
    (cut T (productTensor (intervalVector s t) A)),
    cut_coeFn T (productTensor (intervalVector s t) A),
    productTensor_coeFn (intervalVector s t) A,
    productTensor_coeFn (intervalVector (max s T) t) A, ht, hm] with z hd hc ha hb ht hm
  simp only [Function.comp_apply] at ht hm
  rw [hd]
  change productTensor (intervalVector s t) A z - cut T (productTensor (intervalVector s t) A) z = _
  rw [hc, hb, hm]
  by_cases hz : z ∈ horizon T
  · have hi : z.1 ∉ Ioc (max (s : ℝ) (T : ℝ)) (t : ℝ) :=
      fun h => (not_lt_of_ge hz.1.2) ((le_max_right _ _).trans_lt h.1)
    simp [hz, hi]
  · rw [indicator_of_notMem hz, sub_zero, ha, ht]
    have hi : z.1 ∈ Ioc (max (s : ℝ) (T : ℝ)) (t : ℝ) ↔ z.1 ∈ Ioc (s : ℝ) (t : ℝ) := by
      constructor
      · exact fun h => ⟨(le_max_left _ _).trans_lt h.1, h.2⟩
      · intro h
        have hT : (T : ℝ) < z.1 := lt_of_not_ge (fun hh => hz ⟨⟨s.coe_nonneg.trans_lt h.1, hh⟩, mem_univ _⟩)
        exact ⟨max_lt h.1 hT, h.2⟩
    by_cases hi' : z.1 ∈ Ioc (s : ℝ) (t : ℝ) <;> simp [hi', hi]

/-- Genuine L2 exhaustion of the positive half-line, with no finite-horizon hypothesis. -/
theorem cut_tendsto (U : fullPredictable) :
    Tendsto (fun n : ℕ => cut (n : ℝ≥0) U) atTop (𝓝 (U : TimeProbabilityL2)) := by
  apply BochnerL2Dominated.tendsto_of_ae_norm_bound
  · intro n
    filter_upwards [cut_coeFn (n : ℝ≥0) U] with z hz
    rw [hz]
    by_cases hs : z ∈ horizon (n : ℝ≥0) <;> simp [hs]
  · have hs := (mem_fullPredictable_iff _).mp U.property |>.2
    filter_upwards [ae_all_iff.mpr (fun n : ℕ => cut_coeFn (n : ℝ≥0) U), hs] with z hz hs
    by_cases hp : z ∈ positiveTimes
    · obtain ⟨N, hN⟩ := exists_nat_ge z.1
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with n hn
      have hm : z ∈ horizon (n : ℝ≥0) :=
        ⟨⟨hp.1, hN.trans (by exact_mod_cast hn)⟩, mem_univ _⟩
      exact ((hz n).trans (indicator_of_mem hm _)).symm
    · have he : ∀ n : ℕ, cut (n : ℝ≥0) U z = (U : TimeProbabilityL2) z := by
        intro n
        have hm : z ∉ horizon (n : ℝ≥0) := fun hh => hp ⟨hh.1.1, mem_univ _⟩
        rw [hz n, indicator_of_notMem hm, hs hp]
      simpa only [he] using (tendsto_const_nhds (x := (U : TimeProbabilityL2) z))

end OperatorDerivativeRewrite.Foundation.GaussianPredictableCutoff
