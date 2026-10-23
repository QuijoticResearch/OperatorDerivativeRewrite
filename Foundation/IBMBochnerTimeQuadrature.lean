import Foundation.IBMContinuousQuadrature
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Uniform time quadrature in a complete normed space, used for genuine
observable-L2 IBM quadrature. No point-observation derivative is assumed. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMBochnerTimeQuadrature
open IBMContinuousQuadrature
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def rightSum (j : ℝ → E) (T : ℝ) (N : ℕ) : E :=
  ∑ i ∈ Finset.range N, (T / N) • j (time T N (i + 1))

theorem right_error_bound (j : ℝ → E) (hj : Continuous j) {T η : ℝ}
    (hT : 0 ≤ T) (N : ℕ) (hN : 0 < N)
    (hosc : ∀ x ∈ Icc 0 T, ∀ y ∈ Icc 0 T, |x - y| ≤ T / N → ‖j x - j y‖ ≤ η) :
    ‖rightSum j T N - ∫ t in (0 : ℝ)..T, j t‖ ≤ η * T := by
  have hp : (0 : ℝ) < N := by exact_mod_cast hN
  have hstep : 0 ≤ T / N := div_nonneg hT hp.le
  have cell (i : ℕ) (hi : i < N) :
      ‖(T / N) • j (time T N (i + 1)) -
        ∫ t in time T N i..time T N (i + 1), j t‖ ≤ η * (T / N) := by
    have hle : time T N i ≤ time T N (i + 1) := by linarith [time_step T N i]
    have he : (T / N) • j (time T N (i + 1)) -
        ∫ t in time T N i..time T N (i + 1), j t =
        ∫ t in time T N i..time T N (i + 1), (j (time T N (i + 1))-j t) := by
      rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
        (hj.intervalIntegrable _ _), intervalIntegral.integral_const, time_step]
    rw [he]
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun t => j (time T N (i + 1))-j t) (a := time T N i) (b := time T N (i + 1))
      (C := η) (fun t ht => by
        rw [uIoc_of_le hle] at ht
        have htT : t ∈ Icc 0 T :=
          ⟨(time_mem hT hN (by omega : i ≤ N)).1.trans ht.1.le,
            ht.2.trans (time_mem hT hN (by omega : i + 1 ≤ N)).2⟩
        apply hosc _ (time_mem hT hN (by omega : i + 1 ≤ N)) t htT
        rw [abs_of_nonneg (sub_nonneg.mpr ht.2)]
        linarith [time_step T N i, ht.1])
    rwa [time_step, abs_of_nonneg hstep] at hn
  have ht := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i => time T N i) (f := j) (μ := volume) (n := N)
    (fun i hi => hj.intervalIntegrable _ _)
  have hz : time T N 0 = 0 := by simp [time]
  have hend : time T N N = T := by unfold time; exact div_mul_cancel₀ _ hp.ne'
  rw [hz,hend] at ht
  calc
    _ = ‖∑ i ∈ Finset.range N, ((T / N) • j (time T N (i + 1)) -
        ∫ t in time T N i..time T N (i + 1), j t)‖ := by
      rw [Finset.sum_sub_distrib,ht]; rfl
    _ ≤ ∑ i ∈ Finset.range N, ‖(T / N) • j (time T N (i + 1)) -
        ∫ t in time T N i..time T N (i + 1), j t‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range N, η * (T / N) :=
      Finset.sum_le_sum fun i hi => cell i (Finset.mem_range.mp hi)
    _ = η * T := by simp; field_simp

theorem rightSum_tendsto (j : ℝ → E) (hj : Continuous j) {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun n => rightSum j T (n + 1)) atTop (𝓝 (∫ t in (0 : ℝ)..T, j t)) := by
  have step : Tendsto (fun n : ℕ => T / (n + 1 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Filter.tendsto_atTop_add_const_right _ _
      tendsto_natCast_atTop_atTop)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε/(2*(T + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨δ,hδ,hu⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).uniformContinuousOn_of_continuous
      hj.continuousOn) η hη
  filter_upwards [step.eventually (gt_mem_nhds hδ)] with n hn
  have hb := right_error_bound j hj hT (n + 1) (by omega) (by
    intro x hx y hy hxy
    have hxy' : |x - y| ≤ T / (n + 1 : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hxy
    exact le_of_lt (by
      simpa only [dist_eq_norm] using hu x hx y hy
        (by simpa only [Real.dist_eq] using hxy'.trans_lt hn)))
  rw [dist_eq_norm]
  have heta : η * (2*(T + 1))=ε := by dsimp [η]; field_simp
  nlinarith

end OperatorDerivativeRewrite.Foundation.IBMBochnerTimeQuadrature
