import Foundation.BrownianMassZeroFreeIntervals
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.Support

/-! An actual Stieltjes measure from the constructed mass path, with native
support containment in the Brownian zero set. No occupation formula assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianMassStieltjesSupport
open InfiniteGaussian IBMConstructedSources BrownianMassContinuousLimit
open BrownianMassZeroFreeIntervals

def cumulative (ω : SampleSpace) : StieltjesFunction ℝ≥0 := by
  classical
  exact if h : Monotone (limitPath ω) then
    ⟨limitPath ω, h, fun t => (limitPath ω).continuous.continuousAt.continuousWithinAt⟩
  else StieltjesFunction.const ℝ≥0 0

theorem cumulative_eq {ω : SampleSpace} (h : Monotone (limitPath ω)) (t : ℝ≥0) :
    cumulative ω t = limitPath ω t := by simp only [cumulative, dite_eq_left h]

theorem cumulative_continuous (ω : SampleSpace) : Continuous (cumulative ω) := by
  classical
  by_cases h : Monotone (limitPath ω)
  · simpa only [cumulative, dite_eq_left h] using (limitPath ω).continuous
  · simp only [cumulative, dite_eq_right h]
    exact continuous_const

def massMeasure (ω : SampleSpace) : Measure ℝ≥0 := (cumulative ω).measure

theorem massMeasure_Icc (ω : SampleSpace) (s t : ℝ≥0) :
    massMeasure ω (Icc s t) = ENNReal.ofReal (cumulative ω t - cumulative ω s) := by
  rw [massMeasure, StieltjesFunction.measure_Icc,
    (cumulative_continuous ω).continuousAt.continuousWithinAt.leftLim_eq]

theorem massMeasure_singleton (ω : SampleSpace) (t : ℝ≥0) : massMeasure ω {t} = 0 := by
  rw [massMeasure, StieltjesFunction.measure_singleton,
    (cumulative_continuous ω).continuousAt.continuousWithinAt.leftLim_eq]
  simp

theorem massMeasure_Ioc : ∀ᵐ ω ∂gaussianProduct, ∀ s t : ℝ≥0,
    massMeasure ω (Ioc s t) = ENNReal.ofReal (limitPath ω t - limitPath ω s) := by
  filter_upwards [limitPath_properties] with ω hω s t
  rw [massMeasure, StieltjesFunction.measure_Ioc,
    cumulative_eq hω.2.1, cumulative_eq hω.2.1]

theorem zero_free_measure : ∀ᵐ ω ∂gaussianProduct, ∀ s t : ℝ≥0, s ≤ t →
    (∀ u : ℝ≥0, u ∈ Icc s t → clockPath ω u ≠ 0) → massMeasure ω (Icc s t) = 0 := by
  filter_upwards [limitPath_properties, zero_free_constant] with ω hp hc s t hst hn
  rw [massMeasure_Icc, cumulative_eq hp.2.1, cumulative_eq hp.2.1, hc s t hst hn]
  simp

theorem support_subset_zeros : ∀ᵐ ω ∂gaussianProduct,
    (massMeasure ω).support ⊆ {t : ℝ≥0 | clockPath ω t = 0} := by
  filter_upwards [zero_free_measure] with ω hz x hx
  by_contra hn
  have ho : IsOpen {t : ℝ≥0 | clockPath ω t ≠ 0} :=
    (isClosed_eq (clockPath ω).continuous continuous_const).isOpen_compl
  obtain ⟨s, t, hxt, hnhds, hsub⟩ := exists_Icc_mem_subset_of_mem_nhds (ho.mem_nhds hn)
  have hzero := hz s t (hxt.1.trans hxt.2) (fun u hu => hsub hu)
  have hpos := (Measure.mem_support_iff_forall x).mp hx (Icc s t) hnhds
  rw [hzero] at hpos
  exact (lt_irrefl 0) hpos

theorem concentrated_on_zeros : ∀ᵐ ω ∂gaussianProduct,
    massMeasure ω {t : ℝ≥0 | clockPath ω t ≠ 0} = 0 := by
  filter_upwards [support_subset_zeros] with ω hs
  apply measure_mono_null _ (massMeasure ω).measure_compl_support
  intro t ht hmem
  exact ht (hs hmem)

end OperatorDerivativeRewrite.Foundation.BrownianMassStieltjesSupport
