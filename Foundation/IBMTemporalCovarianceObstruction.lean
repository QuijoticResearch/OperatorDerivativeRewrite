import Foundation.IBMClockBacktracking
import Foundation.IBMTimeAveragedObservable
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2

/-! Genuine clock backtracking makes the actual IBM increment negatively
paired with its past value. A past L2 projection cannot be the previous value. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMTemporalCovarianceObstruction
open InfiniteGaussian GaussianTimeProcess IBMRandomTimeHilbert IBMContinuousScenery
open IBMTimeAveragedObservable
set_option backward.isDefEq.respectTransparency false

def gap (s t : ℝ≥0) (ω : SampleSpace) : ℝ :=
  max (|process s ω| - |process t ω|) 0

theorem gap_nonneg (s t : ℝ≥0) (ω : SampleSpace) : 0 ≤ gap s t ω := le_max_right _ _

theorem gap_integrable (s t : ℝ≥0) : Integrable (gap s t) gaussianProduct := by
  have hi := ((process_memLp s 1 (by simp)).integrable (by simp)).abs
  apply Integrable.mono' hi
  · have hs := continuous_abs.measurable.comp (process_stronglyMeasurable s).measurable
    have ht := continuous_abs.measurable.comp (process_stronglyMeasurable t).measurable
    exact ((hs.sub ht).max measurable_const).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (gap_nonneg s t ω)]
      exact max_le (sub_le_self _ (abs_nonneg _)) (abs_nonneg _)

theorem expected_gap_positive : 0 < ∫ ω, gap 1 2 ω ∂gaussianProduct := by
  apply (integral_pos_iff_support_of_nonneg (gap_nonneg 1 2) (gap_integrable 1 2)).mpr
  apply IBMClockBacktracking.backtracking_positive.trans_le
  apply measure_mono
  intro ω hω
  change gap 1 2 ω ≠ 0
  exact ne_of_gt (lt_of_lt_of_le (sub_pos.mpr hω) (le_max_left _ _))

theorem scenery_pair_gap (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    inner ℝ (sourceScenery a) (sourceScenery b - sourceScenery a) = -max (a - b) 0 := by
  have hx := sourceScenery_norm_sq a
  have hy := sourceScenery_norm_sq b
  have hd := sourceScenery_increment_sq a b
  rw [abs_of_nonneg ha] at hx
  rw [abs_of_nonneg hb] at hy
  rw [norm_sub_sq_real] at hd
  have hsym : inner ℝ (sourceScenery b) (sourceScenery a) =
      inner ℝ (sourceScenery a) (sourceScenery b) := real_inner_comm _ _
  rw [hsym] at hd
  rw [inner_sub_right, real_inner_self_eq_norm_sq]
  by_cases hab : a ≤ b
  · rw [max_eq_right (sub_nonpos.mpr hab)]
    rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hd
    nlinarith
  · have hba : b ≤ a := le_of_not_ge hab
    rw [max_eq_left (sub_nonneg.mpr hba)]
    rw [abs_of_nonpos (sub_nonpos.mpr hba)] at hd
    nlinarith

theorem actual_increment_pairing (s t : ℝ≥0) :
    inner ℝ (intrinsicCurve s) (intrinsicCurve t - intrinsicCurve s) =
      -(∫ ω, gap s t ω ∂gaussianProduct) := by
  change inner ℝ (jointRealization (randomSourceL2 s))
    (jointRealization (randomSourceL2 t) - jointRealization (randomSourceL2 s)) = _
  rw [← jointRealization.map_sub, jointRealization.inner_map_map, L2_inner_eq_integral,
    ← integral_neg]
  apply integral_congr_ae
  filter_upwards [(randomSourceClass_memLp s).coeFn_toLp,
    (randomSourceClass_memLp t).coeFn_toLp,
    Lp.coeFn_sub (randomSourceL2 t) (randomSourceL2 s)] with ω hs ht hd
  change randomSourceL2 s ω = randomSourceClass s ω at hs
  change randomSourceL2 t ω = randomSourceClass t ω at ht
  rw [hd, Pi.sub_apply, hs, ht]
  exact scenery_pair_gap _ _ (abs_nonneg _) (abs_nonneg _)

theorem actual_increment_pairing_negative :
    inner ℝ (intrinsicCurve 1) (intrinsicCurve 2 - intrinsicCurve 1) < 0 := by
  rw [actual_increment_pairing]
  exact neg_neg_of_pos expected_gap_positive

/-- Every closed candidate past containing the previous actual IBM value
fails the martingale conditional-projection identity at times one and two. -/
theorem past_projection_ne_previous (V : Submodule ℝ JointL2) [CompleteSpace V]
    (hp : (intrinsicCurve 1 : JointL2) ∈ V) :
    V.starProjection (intrinsicCurve 2 : JointL2) ≠ (intrinsicCurve 1 : JointL2) := by
  intro he
  have h := V.inner_orthogonalProjectionOnto_eq_of_mem_left
    ⟨(intrinsicCurve 1 : JointL2), hp⟩ (intrinsicCurve 2 : JointL2)
  change inner ℝ (intrinsicCurve 1 : JointL2) (V.starProjection (intrinsicCurve 2 : JointL2)) =
    inner ℝ (intrinsicCurve 1 : JointL2) (intrinsicCurve 2 : JointL2) at h
  rw [he] at h
  have hz : inner ℝ (intrinsicCurve 1) (intrinsicCurve 2 - intrinsicCurve 1) = 0 := by
    change inner ℝ (intrinsicCurve 1 : JointL2)
      ((intrinsicCurve 2 : JointL2) - (intrinsicCurve 1 : JointL2)) = 0
    rw [inner_sub_right, ← h, sub_self]
  have hn := actual_increment_pairing_negative
  rw [hz] at hn
  exact (lt_irrefl 0) hn

end OperatorDerivativeRewrite.Foundation.IBMTemporalCovarianceObstruction
