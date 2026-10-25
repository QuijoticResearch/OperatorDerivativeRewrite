import Foundation.IBMFourierSourceMeanIto

/-! Native finite sums of the ORIGINAL predictable damping fields converge in
actual time-probability L2 to the completed reflected field. Continuity of the
original isometric Ito map identifies the actual stochastic integral limit. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.ReflectedDampingNativeIntegral
open InfiniteGaussian GaussianPredictableFull GaussianTimeProductL2
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe

theorem single_norm (c : ℝ) (hc : 0 ≤ c) (T : ℝ≥0) :
    ‖GaussianDampedReflectedIto.running c hc T‖ ≤ c * Real.sqrt (T : ℝ) := by
  have h : ‖(GaussianDampedReflectedIto.running c hc T : TimeProbabilityL2)‖ ≤
      c * ‖BrownianSignIntegral.field T‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [GaussianDampedReflectedIto.running_actual c hc T,
      BrownianSignIntegral.field_coeFn T] with z hu hs
    rw [hu, hs]
    by_cases hz : z ∈ PredictableRealL2.horizon T
    · simp only [indicator_of_mem hz, norm_mul, norm_neg, Real.norm_of_nonneg hc,
        Real.norm_of_nonneg (Real.exp_pos _).le]
      have he : Real.exp (-c * |BrownianClockWeightedEnergy.sigma z|) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc)
          (abs_nonneg _))
      exact (mul_le_mul_of_nonneg_left he
        (mul_nonneg hc (norm_nonneg _))).trans_eq (mul_one _)
    · simp [hz]
  have hs : ‖BrownianSignIntegral.field T‖ = Real.sqrt (T : ℝ) := by
    rw [← BrownianSignIntegral.field_norm_sq T, Real.sqrt_sq (norm_nonneg _)]
  exact h.trans_eq (by rw [hs])

variable (b c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k)

def term (T : ℝ≥0) (k : ℕ) : fullPredictable :=
  b k • GaussianDampedReflectedIto.running (c k) (hc k) T

def native (T : ℝ≥0) (N : ℕ) : fullPredictable :=
  ∑ k ∈ Finset.range N, term b c hc T k

theorem term_bound (T : ℝ≥0) (k : ℕ) :
    ‖term b c hc T k‖ ≤ ReflectedDampingSeries.cost1 b c k * Real.sqrt (T : ℝ) := by
  rw [term, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (single_norm (c k) (hc k) T) (abs_nonneg _)).trans_eq
    (by unfold ReflectedDampingSeries.cost1; ring)

variable (hb : Summable (fun k => |b k|)) (h2 : Summable (ReflectedDampingSeries.cost2 b c))
include hc hb h2

theorem term_norm_summable (T : ℝ≥0) : Summable (fun k => ‖term b c hc T k‖) :=
  ((ReflectedDampingSeries.cost1_summable b c hc hb h2).mul_right (Real.sqrt (T : ℝ))).of_nonneg_of_le (fun _ => norm_nonneg _) (term_bound b c hc T)

theorem terms_summable (T : ℝ≥0) : Summable (term b c hc T) :=
  (term_norm_summable b c hc hb h2 T).of_norm

theorem tsum_field (T : ℝ≥0) :
    (∑' k, term b c hc T k) = ReflectedDampingSeriesIto.running b c hc hb h2 T := by
  apply Subtype.ext
  have he := (terms_summable b c hc hb h2 T).map_tsum
    fullPredictable.subtypeL.toLinearMap.toAddMonoidHom fullPredictable.subtypeL.continuous
  change fullPredictable.subtypeL (∑' k, term b c hc T k) =
    ∑' k, (term b c hc T k : TimeProbabilityL2) at he
  change fullPredictable.subtypeL (∑' k, term b c hc T k) = _
  rw [he]
  apply Lp.ext
  have hn : Summable (fun k => ‖(term b c hc T k : TimeProbabilityL2)‖) :=
    term_norm_summable b c hc hb h2 T
  filter_upwards [Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hn),
    ae_all_iff.mpr fun k => Lp.coeFn_smul (b k)
      (GaussianDampedReflectedIto.running (c k) (hc k) T : TimeProbabilityL2),
    ae_all_iff.mpr fun k => GaussianDampedReflectedIto.running_actual (c k) (hc k) T,
    ReflectedDampingSeriesIto.running_actual b c hc hb h2 T] with z ht hm hu ha
  rw [ht, ha]
  by_cases hz : z ∈ PredictableRealL2.horizon T
  · rw [indicator_of_mem hz, ← tsum_mul_left]
    apply tsum_congr
    intro k
    change ((b k) • (GaussianDampedReflectedIto.running (c k) (hc k) T : TimeProbabilityL2)) z = _
    rw [hm k, Pi.smul_apply, hu k, indicator_of_mem hz]
    simp only [smul_eq_mul]
    ring
  · rw [indicator_of_notMem hz]
    calc
      _ = ∑' _ : ℕ, (0 : ℝ) := by
        apply tsum_congr
        intro k
        change ((b k) •
          (GaussianDampedReflectedIto.running (c k) (hc k) T : TimeProbabilityL2)) z = _
        rw [hm k, Pi.smul_apply, hu k, indicator_of_notMem hz]
        simp
      _ = 0 := tsum_zero

theorem partial_tendsto (T : ℝ≥0) :
    Tendsto (native b c hc T) atTop (𝓝 (ReflectedDampingSeriesIto.running b c hc hb h2 T)) := by
  have h := (terms_summable b c hc hb h2 T).hasSum.tendsto_sum_nat
  rw [tsum_field b c hc hb h2 T] at h
  exact h

theorem integral_tendsto (T : ℝ≥0) :
    Tendsto (fun N => ∑ k ∈ Finset.range N,
      b k • itoIntegral (GaussianDampedReflectedIto.running (c k) (hc k) T))
      atTop (𝓝 (itoIntegral (ReflectedDampingSeriesIto.running b c hc hb h2 T))) := by
  have h := itoIntegral.continuous.tendsto
    (ReflectedDampingSeriesIto.running b c hc hb h2 T) |>.comp
      (partial_tendsto b c hc hb h2 T)
  simpa only [Function.comp_def, native, map_sum, term, map_smul] using h

end OperatorDerivativeRewrite.Foundation.ReflectedDampingNativeIntegral
