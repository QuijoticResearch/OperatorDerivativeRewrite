import Foundation.IBMContinuousQuadrature
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Deterministic C1 time weights against continuous paths. The limit is
identified through genuine time integration and finite summation by parts. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMTimeWeightQuadrature
open IBMContinuousQuadrature

theorem discrete_by_parts (a b : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, a i * (b (i + 1) - b i)) =
      a N * b N - a 0 * b 0 -
        ∑ i ∈ Finset.range N, b (i + 1) * (a (i + 1) - a i) := by
  have he : (∑ i ∈ Finset.range N, a i * (b (i + 1) - b i)) +
      (∑ i ∈ Finset.range N, b (i + 1) * (a (i + 1) - a i)) =
      ∑ i ∈ Finset.range N, (a (i + 1) * b (i + 1) - a i * b i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [Finset.sum_range_sub (fun i => a i * b i)] at he
  linarith

theorem compact_weight_bounds (h : ℝ → ℝ) (hh : ContDiff ℝ 1 h)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ B K : ℝ, 0 ≤ B ∧ 0 ≤ K ∧ (∀ t ∈ Icc 0 T, |h t| ≤ B) ∧
      (∀ t ∈ Icc 0 T, |deriv h t| ≤ K) ∧
      (∀ x ∈ Icc 0 T, ∀ y ∈ Icc 0 T, |h y - h x| ≤ K * |y - x|) := by
  have hd := hh.continuous_deriv (by norm_num)
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).exists_bound_of_continuousOn
    hh.continuous.continuousOn
  obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).exists_bound_of_continuousOn
    hd.continuousOn
  refine ⟨B, K, (norm_nonneg _).trans (hB 0 ⟨le_rfl, hT⟩),
    (norm_nonneg _).trans (hK 0 ⟨le_rfl, hT⟩), ?_, ?_, ?_⟩
  · intro t ht
    simpa only [Real.norm_eq_abs] using hB t ht
  · intro t ht
    simpa only [Real.norm_eq_abs] using hK t ht
  · intro x hx y hy
    have he := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := h) (fun t _ => (hh.differentiable (by norm_num)) t)
      (fun t ht => hK t ht) (convex_Icc 0 T) hx hy
    simpa only [Real.norm_eq_abs] using he

def rightSum (h j : ℝ → ℝ) (T : ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, j (time T N (i + 1)) *
    (h (time T N (i + 1)) - h (time T N i))

theorem right_error_bound (h j : ℝ → ℝ) (hh : ContDiff ℝ 1 h) (hj : Continuous j)
    {T K η : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    (N : ℕ) (hN : 0 < N)
    (hd : ∀ t ∈ Icc 0 T, |deriv h t| ≤ K)
    (hosc : ∀ x ∈ Icc 0 T, ∀ y ∈ Icc 0 T, |x - y| ≤ T / N → |j x - j y| ≤ η) :
    |rightSum h j T N - ∫ t in (0 : ℝ)..T, deriv h t * j t| ≤ K * η * T := by
  have hp : (0 : ℝ) < N := by exact_mod_cast hN
  have hstep : 0 ≤ T / N := div_nonneg hT hp.le
  have hder := hh.continuous_deriv (by norm_num)
  have hc : Continuous (fun t => deriv h t * j t) := hder.mul hj
  have hcell (i : ℕ) (hi : i < N) :
      |j (time T N (i + 1)) * (h (time T N (i + 1)) - h (time T N i)) -
        ∫ t in time T N i..time T N (i + 1), deriv h t * j t| ≤
          (K * η) * (T / N) := by
    have hiN : i + 1 ≤ N := by omega
    have hle : time T N i ≤ time T N (i + 1) := by linarith [time_step T N i]
    have hftc := intervalIntegral.integral_deriv_eq_sub
      (fun t ht => (hh.differentiable (by norm_num)) t) (hder.intervalIntegrable
        (time T N i) (time T N (i + 1)))
    have he : j (time T N (i + 1)) * (h (time T N (i + 1)) - h (time T N i)) -
        ∫ t in time T N i..time T N (i + 1), deriv h t * j t =
        ∫ t in time T N i..time T N (i + 1), deriv h t * (j (time T N (i + 1)) - j t) := by
      simp_rw [mul_sub]
      have hc1 : IntervalIntegrable (fun t => deriv h t * j (time T N (i + 1))) volume
          (time T N i) (time T N (i + 1)) :=
        (hder.mul_const _).intervalIntegrable _ _
      have hi := intervalIntegral.integral_sub hc1 (hc.intervalIntegrable
        (time T N i) (time T N (i + 1)))
      rw [hi, intervalIntegral.integral_mul_const, hftc]
      ring
    rw [he]
    have hb (t : ℝ) (ht : t ∈ uIoc (time T N i) (time T N (i + 1))) :
        ‖deriv h t * (j (time T N (i + 1)) - j t)‖ ≤ K * η := by
      rw [uIoc_of_le hle] at ht
      have htT : t ∈ Icc 0 T :=
        ⟨(time_mem hT hN (by omega : i ≤ N)).1.trans ht.1.le,
          ht.2.trans (time_mem hT hN hiN).2⟩
      have hdist : |time T N (i + 1) - t| ≤ T / N := by
        rw [abs_of_nonneg (sub_nonneg.mpr ht.2)]
        linarith [time_step T N i, ht.1]
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hd t htT)
        (hosc _ (time_mem hT hN hiN) t htT hdist) (abs_nonneg _) hK
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [time_step, abs_of_nonneg hstep] at hn
    simpa only [Real.norm_eq_abs] using hn
  have ht := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i => time T N i) (f := fun t => deriv h t * j t) (μ := volume) (n := N)
    (fun i hi => hc.intervalIntegrable _ _)
  have hz : time T N 0 = 0 := by simp [time]
  have hend : time T N N = T := by unfold time; exact div_mul_cancel₀ _ hp.ne'
  rw [hz, hend] at ht
  calc
    _ = |∑ i ∈ Finset.range N,
        (j (time T N (i + 1)) * (h (time T N (i + 1)) - h (time T N i)) -
          ∫ t in time T N i..time T N (i + 1), deriv h t * j t)| := by
      rw [Finset.sum_sub_distrib, ht]
      rfl
    _ ≤ ∑ i ∈ Finset.range N,
        |j (time T N (i + 1)) * (h (time T N (i + 1)) - h (time T N i)) -
          ∫ t in time T N i..time T N (i + 1), deriv h t * j t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range N, (K * η) * (T / N) :=
      Finset.sum_le_sum fun i hi => hcell i (Finset.mem_range.mp hi)
    _ = K * η * T := by simp; field_simp

theorem rightSum_tendsto (h j : ℝ → ℝ) (hh : ContDiff ℝ 1 h) (hj : Continuous j)
    {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun n => rightSum h j T (n + 1)) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, deriv h t * j t)) := by
  obtain ⟨B, K, hB, hK, hb, hd, hLip⟩ := compact_weight_bounds h hh hT
  have hstep : Tendsto (fun n : ℕ => T / (n + 1 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Filter.tendsto_atTop_add_const_right _ _
      tendsto_natCast_atTop_atTop)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε / (2 * (K * T + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).uniformContinuousOn_of_continuous
      hj.continuousOn) η hη
  filter_upwards [hstep.eventually (gt_mem_nhds hδ)] with n hn
  have ho : ∀ x ∈ Icc 0 T, ∀ y ∈ Icc 0 T,
      |x - y| ≤ T / (n + 1 : ℝ) → |j x - j y| ≤ η := by
    intro x hx y hy hxy
    have he := hu x hx y hy (by simpa only [Real.dist_eq] using hxy.trans_lt hn)
    simpa only [Real.dist_eq] using he.le
  have he := right_error_bound h j hh hj hT hK (n + 1) (by omega) hd
    (by simpa only [Nat.cast_add, Nat.cast_one] using ho)
  rw [Real.dist_eq]
  have heta : η * (2 * (K * T + 1)) = ε := by dsimp [η]; field_simp
  nlinarith [mul_nonneg hK hT]

theorem increment_sum_tendsto (h j : ℝ → ℝ) (hh : ContDiff ℝ 1 h) (hj : Continuous j)
    {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun n => ∑ i ∈ Finset.range (n + 1), h (time T (n + 1) i) *
      (j (time T (n + 1) (i + 1)) - j (time T (n + 1) i))) atTop
      (𝓝 (h T * j T - h 0 * j 0 - ∫ t in (0 : ℝ)..T, deriv h t * j t)) := by
  have he (n : ℕ) := discrete_by_parts (fun i => h (time T (n + 1) i))
    (fun i => j (time T (n + 1) i)) (n + 1)
  have hz (n : ℕ) : time T (n + 1) 0 = 0 := by simp [time]
  have ht (n : ℕ) : time T (n + 1) (n + 1) = T := by
    unfold time
    exact div_mul_cancel₀ _ (by positivity)
  simp only [hz, ht] at he
  have hlim := (tendsto_const_nhds (x := h T * j T - h 0 * j 0)).sub
    (rightSum_tendsto h j hh hj hT)
  exact hlim.congr' (Eventually.of_forall fun n => (he n).symm)

end OperatorDerivativeRewrite.Foundation.IBMTimeWeightQuadrature
