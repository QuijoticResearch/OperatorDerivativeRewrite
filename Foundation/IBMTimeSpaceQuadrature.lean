import Foundation.IBMTimeSpacePeano
import Foundation.IBMTimeWeightQuadrature

/-! The genuine time-partial correction along any continuous real path.
No variation or differentiability of that path is assumed. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMTimeSpaceQuadrature
open IBMContinuousQuadrature

def timeDerivative (F : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ := deriv (fun s => F s x) t

def increments (F : ℝ → ℝ → ℝ) (j : ℝ → ℝ) (T : ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N,
    (F (time T N (i + 1)) (j (time T N (i + 1))) -
      F (time T N i) (j (time T N (i + 1))))

theorem error_bound (F : ℝ → ℝ → ℝ) (j : ℝ → ℝ)
    (hF : ∀ x, ContDiff ℝ 1 (fun t => F t x))
    (hD : Continuous (fun p : ℝ × ℝ => timeDerivative F p.1 p.2))
    (hj : Continuous j) {T η : ℝ} (hT : 0 ≤ T)
    (N : ℕ) (hN : 0 < N)
    (hosc : ∀ i < N, ∀ t ∈ Icc (time T N i) (time T N (i + 1)),
      |timeDerivative F t (j (time T N (i + 1))) - timeDerivative F t (j t)| ≤ η) :
    |increments F j T N - ∫ t in (0 : ℝ)..T, timeDerivative F t (j t)| ≤ η * T := by
  have hp : (0 : ℝ) < N := by exact_mod_cast hN
  have hstep : 0 ≤ T / N := div_nonneg hT hp.le
  have hc : Continuous (fun t => timeDerivative F t (j t)) :=
    hD.comp (continuous_id.prodMk hj)
  have cell (i : ℕ) (hi : i < N) :
      |F (time T N (i + 1)) (j (time T N (i + 1))) -
        F (time T N i) (j (time T N (i + 1))) -
        ∫ t in time T N i..time T N (i + 1), timeDerivative F t (j t)| ≤ η * (T / N) := by
    have hle : time T N i ≤ time T N (i + 1) := by linarith [time_step T N i]
    have hd : Continuous (fun t => timeDerivative F t (j (time T N (i + 1)))) :=
      hD.comp (continuous_id.prodMk continuous_const)
    have ftc := intervalIntegral.integral_deriv_eq_sub
      (fun t ht => ((hF (j (time T N (i + 1)))).differentiable (by norm_num)) t)
      (hd.intervalIntegrable (time T N i) (time T N (i + 1)))
    have he : F (time T N (i + 1)) (j (time T N (i + 1))) -
        F (time T N i) (j (time T N (i + 1))) -
        ∫ t in time T N i..time T N (i + 1), timeDerivative F t (j t) =
        ∫ t in time T N i..time T N (i + 1),
          (timeDerivative F t (j (time T N (i + 1))) - timeDerivative F t (j t)) := by
      rw [intervalIntegral.integral_sub (hd.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
      exact congrArg (fun x => x - ∫ t in time T N i..time T N (i + 1),
        timeDerivative F t (j t)) ftc.symm
    rw [he]
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := time T N i) (b := time T N (i + 1)) (C := η)
      (f := fun t => timeDerivative F t (j (time T N (i + 1))) - timeDerivative F t (j t))
      (fun t ht => by
        rw [uIoc_of_le hle] at ht
        simpa only [Real.norm_eq_abs] using hosc i hi t ⟨ht.1.le,ht.2⟩)
    rw [time_step, abs_of_nonneg hstep] at hn
    simpa only [Real.norm_eq_abs] using hn
  have ht := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i => time T N i) (f := fun t => timeDerivative F t (j t))
    (μ := volume) (n := N) (fun i hi => hc.intervalIntegrable _ _)
  have hz : time T N 0 = 0 := by simp [time]
  have hend : time T N N = T := by unfold time; exact div_mul_cancel₀ _ hp.ne'
  rw [hz,hend] at ht
  calc
    _ = |∑ i ∈ Finset.range N,
        (F (time T N (i + 1)) (j (time T N (i + 1))) -
          F (time T N i) (j (time T N (i + 1))) -
          ∫ t in time T N i..time T N (i + 1), timeDerivative F t (j t))| := by
      rw [Finset.sum_sub_distrib,ht]; rfl
    _ ≤ ∑ i ∈ Finset.range N, |F (time T N (i + 1)) (j (time T N (i + 1))) -
          F (time T N i) (j (time T N (i + 1))) -
          ∫ t in time T N i..time T N (i + 1), timeDerivative F t (j t)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range N, η * (T / N) :=
      Finset.sum_le_sum fun i hi => cell i (Finset.mem_range.mp hi)
    _ = η * T := by simp; field_simp

theorem increments_tendsto (F : ℝ → ℝ → ℝ) (j : ℝ → ℝ)
    (hF : ∀ x, ContDiff ℝ 1 (fun t => F t x))
    (hD : Continuous (fun p : ℝ × ℝ => timeDerivative F p.1 p.2))
    (hj : Continuous j) {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun n => increments F j T (n + 1)) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, timeDerivative F t (j t))) := by
  obtain ⟨R,hR⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).exists_bound_of_continuousOn
    hj.continuousOn
  have step : Tendsto (fun n : ℕ => T / (n + 1 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Filter.tendsto_atTop_add_const_right _ _
      tendsto_natCast_atTop_atTop)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε/(2*(T + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨δ, hδ, hu⟩ := IBMTimeSpacePeano.horizontal_modulus
    (timeDerivative F) hD T R η hη
  obtain ⟨ρ, hρ, hjuc⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).uniformContinuousOn_of_continuous
      hj.continuousOn) δ hδ
  filter_upwards [step.eventually (gt_mem_nhds hρ)] with n hn
  have ho : ∀ i < n + 1, ∀ t ∈ Icc (time T (n + 1) i) (time T (n + 1) (i + 1)),
      |timeDerivative F t (j (time T (n + 1) (i + 1))) - timeDerivative F t (j t)| ≤ η := by
    intro i hi t ht
    have hiN : i + 1 ≤ n + 1 := by omega
    have htT : t ∈ Icc 0 T := ⟨(time_mem hT (by omega) (by omega : i ≤ n + 1)).1.trans ht.1,
      ht.2.trans (time_mem hT (by omega) hiN).2⟩
    have hrT := time_mem hT (by omega : 0 < n + 1) hiN
    have hdist : |time T (n + 1) (i + 1)-t| ≤ T / (n + 1 : ℝ) := by
      rw [abs_of_nonneg (sub_nonneg.mpr ht.2)]
      have hs := time_step T (n + 1) i
      push_cast at hs
      linarith [ht.1]
    have hjdist : |j (time T (n + 1) (i + 1))-j t| < δ := by
      simpa only [Real.dist_eq] using hjuc _ hrT t htT
        (by simpa only [Real.dist_eq] using hdist.trans_lt hn)
    exact (hu t htT (j t) (abs_le.mp (by simpa using hR t htT))
      (j (time T (n + 1) (i + 1))) (abs_le.mp (by simpa using hR _ hrT)) hjdist).le
  have hb := error_bound F j hF hD hj hT (n + 1) (by omega)
    (by simpa only [Nat.cast_add, Nat.cast_one] using ho)
  rw [Real.dist_eq]
  have heta : η * (2*(T + 1))=ε := by dsimp [η]; field_simp
  nlinarith

end OperatorDerivativeRewrite.Foundation.IBMTimeSpaceQuadrature
