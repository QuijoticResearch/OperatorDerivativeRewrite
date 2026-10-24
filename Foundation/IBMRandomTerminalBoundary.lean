import Foundation.IBMRawGridObservableTests
import Foundation.IBMClockOccupationPath

/-! Actual terminal-dependent folded-clock boundary. The terminal time is
excluded from fixed-time noncollision; no clipped-QV limit is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRandomTerminalBoundary
open InfiniteGaussian GaussianTimeProcess GaussianHilbertProcess GaussianTimeHilbert
open SeparableHilbertEmbedding IBMConstructedSources GaussianTimeProductL2
open IBMClockOverlapEnergy
attribute [local instance] timeHilbert_secondCountable

def sumVariance (s t : ℝ≥0) : ℝ≥0 := s+t+2*min s t

theorem clock_sum_hasLaw (s t : ℝ≥0) :
    HasLaw (fun Y => process s Y+process t Y) (gaussianReal 0 (sumVariance s t)) gaussianProduct := by
  have hl : HasLaw (isonormal TimeHilbert (timeVector s+timeVector t))
      (gaussianReal 0 (sumVariance s t)) gaussianProduct := by
    refine ⟨(isonormal_measurable _).aemeasurable,?_⟩
    rw [isonormal_law]
    apply congrArg (gaussianReal 0)
    apply NNReal.eq
    change ‖timeVector s+timeVector t‖^2 = (sumVariance s t:ℝ)
    rw [norm_add_sq_real,timeVector_norm_sq,timeVector_norm_sq,timeVector_inner]
    simp [sumVariance]
    ring
  exact hl.congr (isonormal_add_ae (timeVector s) (timeVector t)).symm

private theorem gaussian_nonzero_ae {f : SampleSpace → ℝ} {v : ℝ≥0}
    (hl : HasLaw f (gaussianReal 0 v) gaussianProduct) (hv : v ≠ 0) :
    ∀ᵐ Y ∂gaussianProduct, f Y ≠ 0 := by
  letI : NullSingletonClass (gaussianReal 0 v) := nullSingletonClass_gaussianReal hv
  have hm := hl.measure_eq (p:=fun x : ℝ => x=0)
    (measurableSet_eq_fun measurable_id measurable_const)
  have hz : gaussianProduct {Y | f Y=0} = 0 := by simpa using hm
  rw [ae_iff]
  simpa using hz

theorem folded_noncollision_ae (s t : ℝ≥0) (hst : s < t) :
    ∀ᵐ Y ∂gaussianProduct, |process s Y| ≠ |process t Y| := by
  have hd := gaussian_nonzero_ae (process_increment_hasLaw s t)
    (by
      intro hz
      have he : (t:ℝ) = (s:ℝ) := nndist_eq_zero.mp hz
      exact (ne_of_gt (show (s:ℝ) < t from hst)) he)
  have hv : sumVariance s t ≠ 0 := by
    unfold sumVariance
    have ht : 0 < t := lt_of_le_of_lt (show 0 ≤ s from s.property) hst
    positivity
  have ha := gaussian_nonzero_ae (clock_sum_hasLaw s t) hv
  filter_upwards [hd,ha] with Y hd ha
  intro he
  rcases abs_eq_abs.mp he with h | h
  · apply hd
    change process t Y-process s Y=0
    linarith
  · apply ha
    linarith

theorem path_folded_noncollision_ae (s t : ℝ≥0) (hst : s < t) :
    ∀ᵐ Y ∂gaussianProduct, |clockPath Y s| ≠ |clockPath Y t| := by
  filter_upwards [folded_noncollision_ae s t hst,
    clockPath_coordinate_ae s,clockPath_coordinate_ae t] with Y h hs ht
  rwa [hs,ht]

def distance (T : ℝ≥0) (z : ℝ × SampleSpace) : ℝ :=
  abs (abs (clockPath z.2 z.1.toNNReal)-abs (clockPath z.2 T))

theorem distance_measurable (T : ℝ≥0) : Measurable (distance T) := by
  have ht : Measurable (fun z : ℝ × SampleSpace => clockPath z.2 z.1.toNNReal) :=
    continuous_eval.measurable.comp
      ((clockPath_measurable.comp measurable_snd).prodMk
        (continuous_real_toNNReal.measurable.comp measurable_fst))
  have hT : Measurable (fun z : ℝ × SampleSpace => clockPath z.2 T) :=
    ((ContinuousMap.measurable_eval T).comp clockPath_measurable).comp measurable_snd
  exact continuous_abs.measurable.comp
    ((continuous_abs.measurable.comp ht).sub (continuous_abs.measurable.comp hT))

theorem distance_positive_ae (T : ℝ≥0) :
    ∀ᵐ Y ∂gaussianProduct, ∀ᵐ t ∂window T, 0 < distance T (t,Y) := by
  have hm : MeasurableSet {z : ℝ × SampleSpace | 0 < distance T z} :=
    measurableSet_lt measurable_const (distance_measurable T)
  apply (Measure.ae_ae_comm hm).mp
  have hnot : ∀ᵐ t ∂window T, t ≠ (T:ℝ) := by
    rw [ae_iff]
    have hz : (window T) {(T:ℝ)} = 0 := by
      unfold window
      rw [Measure.restrict_apply (measurableSet_singleton (T:ℝ))]
      exact measure_mono_null inter_subset_left (measure_singleton (T:ℝ))
    simpa using hz
  filter_upwards [ae_restrict_mem measurableSet_Ioc,hnot] with t ht hne
  have hlt : t.toNNReal < T := by
    apply NNReal.coe_lt_coe.mp
    rw [Real.coe_toNNReal t ht.1.le]
    exact lt_of_le_of_ne ht.2 hne
  filter_upwards [path_folded_noncollision_ae t.toNNReal T hlt] with Y hY
  exact abs_pos.mpr (sub_ne_zero.mpr hY)

end OperatorDerivativeRewrite.Foundation.IBMRandomTerminalBoundary
