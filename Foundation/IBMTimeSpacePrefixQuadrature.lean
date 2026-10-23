import Foundation.IBMTimeSpaceQuadrature

/-! One deterministic time-partial error estimate for ALL prefixes of a grid. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMTimeSpacePrefixQuadrature
open IBMContinuousQuadrature IBMTimeSpaceQuadrature

def increments (F : ℝ → ℝ → ℝ) (j : ℝ → ℝ) (T : ℝ) (N m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range m,
    (F (time T N (i + 1)) (j (time T N (i + 1))) -
      F (time T N i) (j (time T N (i + 1))))

theorem rescale_time (T : ℝ) (N m i : ℕ) (hm : m ≠ 0) :
    time (time T N m) m i = time T N i := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  unfold time
  field_simp

theorem prefix_error_bound (F : ℝ → ℝ → ℝ) (j : ℝ → ℝ)
    (hF : ∀ x, ContDiff ℝ 1 (fun t => F t x))
    (hD : Continuous (fun p : ℝ × ℝ => timeDerivative F p.1 p.2))
    (hj : Continuous j) {T η : ℝ} (hT : 0 ≤ T) (hη : 0 ≤ η)
    (N : ℕ) (hN : 0 < N) (m : ℕ) (hmN : m ≤ N)
    (hosc : ∀ i < N, ∀ t ∈ Icc (time T N i) (time T N (i + 1)),
      |timeDerivative F t (j (time T N (i + 1))) - timeDerivative F t (j t)| ≤ η) :
    |increments F j T N m - ∫ t in (0 : ℝ)..time T N m, timeDerivative F t (j t)| ≤ η * T := by
  by_cases hm : m = 0
  · subst m
    simp only [increments, Finset.range_zero, Finset.sum_empty, time, Nat.cast_zero,
      mul_zero, intervalIntegral.integral_same, sub_self, abs_zero]
    exact mul_nonneg hη hT
  have ht := time_mem hT hN hmN
  have hb := IBMTimeSpaceQuadrature.error_bound F j hF hD hj ht.1 m (by omega)
    (by
      intro i hi t hti
      simp only [rescale_time T N m _ hm] at hti ⊢
      exact hosc i (lt_of_lt_of_le hi hmN) t hti)
  have he : IBMTimeSpaceQuadrature.increments F j (time T N m) m = increments F j T N m := by
    simp only [IBMTimeSpaceQuadrature.increments, increments, rescale_time T N m _ hm]
  rw [he] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left ht.2 hη)

def errorMaximum (F : ℝ → ℝ → ℝ) (j : ℝ → ℝ) (T : ℝ) (n : ℕ) : ℝ :=
  (Finset.range (n + 2)).sup' Finset.nonempty_range_add_one
    (fun m => |increments F j T (n + 1) m -
      ∫ t in (0 : ℝ)..time T (n + 1) m, timeDerivative F t (j t)|)

theorem errorMaximum_nonneg (F : ℝ → ℝ → ℝ) (j : ℝ → ℝ) (T : ℝ) (n : ℕ) :
    0 ≤ errorMaximum F j T n :=
  (abs_nonneg _).trans (Finset.le_sup'
    (fun m => |increments F j T (n + 1) m -
      ∫ t in (0 : ℝ)..time T (n + 1) m, timeDerivative F t (j t)|)
    (b := 0) (by simp))

theorem error_le_maximum (F : ℝ → ℝ → ℝ) (j : ℝ → ℝ) (T : ℝ) (n m : ℕ)
    (hm : m ≤ n + 1) :
    |increments F j T (n + 1) m -
      ∫ t in (0 : ℝ)..time T (n + 1) m, timeDerivative F t (j t)| ≤ errorMaximum F j T n :=
  Finset.le_sup' (fun k => |increments F j T (n + 1) k -
    ∫ t in (0 : ℝ)..time T (n + 1) k, timeDerivative F t (j t)|)
    (Finset.mem_range.mpr (by omega))

/-- The samplewise maximum of the genuine time-integral errors tends to zero.
This is stronger than separate convergence at fixed prefix indices. -/
theorem errorMaximum_tendsto (F : ℝ → ℝ → ℝ) (j : ℝ → ℝ)
    (hF : ∀ x, ContDiff ℝ 1 (fun t => F t x))
    (hD : Continuous (fun p : ℝ × ℝ => timeDerivative F p.1 p.2))
    (hj : Continuous j) {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (errorMaximum F j T) atTop (𝓝 0) := by
  obtain ⟨R,hR⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).exists_bound_of_continuousOn
    hj.continuousOn
  have step : Tendsto (fun n : ℕ => T / (n + 1 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Filter.tendsto_atTop_add_const_right _ _
      tendsto_natCast_atTop_atTop)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε/(2*(T + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨δ,hδ,hu⟩ := IBMTimeSpacePeano.horizontal_modulus
    (timeDerivative F) hD T R η hη
  obtain ⟨ρ,hρ,hjuc⟩ := Metric.uniformContinuousOn_iff.mp
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
  have hb : errorMaximum F j T n ≤ η * T := by
    apply Finset.sup'_le
    intro m hm
    exact prefix_error_bound F j hF hD hj hT hη.le (n + 1) (by omega) m
      (by have := Finset.mem_range.mp hm; omega)
      (by simpa only [Nat.cast_add, Nat.cast_one] using ho)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (errorMaximum_nonneg F j T n)]
  have heta : η * (2*(T + 1))=ε := by dsimp [η]; field_simp
  nlinarith

end OperatorDerivativeRewrite.Foundation.IBMTimeSpacePrefixQuadrature
