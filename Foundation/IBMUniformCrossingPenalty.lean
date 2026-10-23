import Foundation.IBMUniformQuarticProbability
import Foundation.IBMClockGaussianTail

/-! The reflection correction vanishes in probability along actual Brownian
uniform grids, by localization near zero and an integrable triangular bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMUniformCrossingPenalty
open InfiniteGaussian IBMConstructedSources IBMReflectedClockCorrection
open IBMUniformClockGridEnergy IBMUniformClockMaximum IBMClockTraversalEnvelope
open IBMFoldedTransitionBound IBMClockGaussianTail
attribute [local irreducible] IBMConstructedSources.clockPath

theorem penalty_le_tent {a b δ : ℝ} (hδ : 0 ≤ δ) (hinc : |b - a| ≤ δ) :
    crossingPenalty a b ≤ δ * tent δ a := by
  by_cases ha : |a| ≤ δ
  · have hs : (b - a) ^ 2 ≤ δ ^ 2 := by
      rw [← sq_abs (b - a)]
      gcongr
    have ht : δ ≤ tent δ a := by
      have := le_max_left (2 * δ - |a|) 0
      change δ ≤ max (2 * δ - |a|) 0
      linarith
    exact (crossingPenalty_bounds a b).2.trans
      (hs.trans (by nlinarith))
  · have hprod : 0 ≤ a * b := by
      have hd := abs_le.mp hinc
      by_cases hsign : 0 ≤ a
      · rw [abs_of_nonneg hsign] at ha
        exact mul_nonneg hsign (by linarith)
      · have hn : a ≤ 0 := (lt_of_not_ge hsign).le
        rw [abs_of_nonpos hn] at ha
        exact mul_nonneg_of_nonpos_of_nonpos hn (by linarith)
    rw [crossingPenalty_eq_zero_of_nonneg hprod]
    exact mul_nonneg hδ (tent_nonneg _ _)

def nearEnergy (T : ℝ≥0) (n : ℕ) (δ : ℝ) (ω : SampleSpace) : ℝ :=
  δ * ∑ i ∈ Finset.range n, tent δ (clockPath ω (grid (T / n) i))

def penalty (T : ℝ≥0) (n : ℕ) (ω : SampleSpace) : ℝ :=
  ∑ i ∈ Finset.range n, crossingPenalty (clockPath ω (grid (T / n) i))
    (clockPath ω (grid (T / n) (i + 1)))

theorem penalty_nonneg (T : ℝ≥0) (n : ℕ) (ω : SampleSpace) : 0 ≤ penalty T n ω :=
  Finset.sum_nonneg fun _ _ => (crossingPenalty_bounds _ _).1

theorem penalty_measurable (T : ℝ≥0) (n : ℕ) : Measurable (penalty T n) := by
  apply Finset.measurable_sum
  intro i hi
  have ha := (ContinuousMap.measurable_eval (grid (T / n) i)).comp clockPath_measurable
  have hb := (ContinuousMap.measurable_eval (grid (T / n) (i + 1))).comp clockPath_measurable
  exact ((continuous_abs.measurable.comp (ha.mul hb)).sub (ha.mul hb)).const_mul 2

theorem nearEnergy_nonneg (T : ℝ≥0) (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (ω : SampleSpace) :
    0 ≤ nearEnergy T n δ ω :=
  mul_nonneg hδ (Finset.sum_nonneg fun _ _ => tent_nonneg _ _)

theorem clock_tent_integrable {δ : ℝ} (hδ : 0 ≤ δ) (t : ℝ≥0) :
    Integrable (fun ω => tent δ (clockPath ω t)) gaussianProduct := by
  apply Integrable.of_bound
    ((tent_continuous δ).measurable.comp
      ((ContinuousMap.measurable_eval t).comp clockPath_measurable)).aestronglyMeasurable (2 * δ)
  exact ae_of_all _ fun ω => by
    change ‖tent δ (clockPath ω t)‖ ≤ 2 * δ
    rw [Real.norm_eq_abs, abs_of_nonneg (tent_nonneg _ _)]
    exact tent_le hδ _

theorem nearEnergy_integrable (T : ℝ≥0) (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    Integrable (nearEnergy T n δ) gaussianProduct :=
  (integrable_finsetSum (Finset.range n) fun _ _ => clock_tent_integrable hδ _).const_mul δ

theorem clock_tent_mean_le {δ : ℝ} (hδ : 0 ≤ δ) (t : ℝ≥0) (ht : 0 < t) :
    (∫ ω, tent δ (clockPath ω t) ∂gaussianProduct) ≤ 16 * δ ^ 2 * peak t := by
  have hl := (clock_hasLaw t).integral_comp (f := tent δ) (tent_continuous δ).aestronglyMeasurable
  simp only [Function.comp_def] at hl
  rw [hl]
  simpa only [tent, zero_sub, abs_neg, abs_abs] using
    folded_tent_average_le hδ 0 0 (ne_of_gt ht)

theorem peak_grid_succ (h : ℝ≥0) (i : ℕ) :
    peak (grid h (i + 1)) = peak h / Real.sqrt (i + 1 : ℝ) := by
  have he (s : ℝ≥0) : nndist (s : ℝ) (0 : ℝ) = s := by
    apply NNReal.eq
    simp only [coe_nndist, Real.dist_eq, sub_zero, abs_of_nonneg s.coe_nonneg]
  have hx := grid_peak h 0 (i + 1) (by omega)
  simpa only [grid, Nat.cast_zero, mul_zero, NNReal.coe_zero, he, Nat.sub_zero,
    Nat.cast_add, Nat.cast_one] using hx

theorem positive_tent_sum_le {h : ℝ≥0} (hh : 0 < h) {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    (∑ i ∈ Finset.range n, ∫ ω, tent δ (clockPath ω (grid h (i + 1))) ∂gaussianProduct) ≤
      32 * δ ^ 2 * peak h * Real.sqrt (n : ℝ) := by
  calc
    _ ≤ ∑ i ∈ Finset.range n, 16 * δ ^ 2 * peak h * (1 / Real.sqrt (i + 1 : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      have ht : 0 < grid h (i + 1) := mul_pos hh (by positivity)
      simpa only [peak_grid_succ, div_eq_mul_inv, mul_assoc, one_mul] using
        clock_tent_mean_le hδ (grid h (i + 1)) ht
    _ = (16 * δ ^ 2 * peak h) * ∑ i ∈ Finset.range n, 1 / Real.sqrt (i + 1 : ℝ) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := (mul_le_mul_of_nonneg_left (inverse_sqrt_sum n)
      (mul_nonneg (by positivity) (peak_nonneg h))).trans_eq (by ring)

theorem nearEnergy_mean_le {T : ℝ≥0} (hT : 0 < T) {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    (∫ ω, nearEnergy T (n + 1) δ ω ∂gaussianProduct) ≤
      2 * δ ^ 2 + 32 * peak T * (n + 1 : ℝ) * δ ^ 3 := by
  let h : ℝ≥0 := T / (n + 1)
  have hh : 0 < h := div_pos hT (by positivity)
  have hp := positive_tent_sum_le hh hδ n
  have hz : (∫ ω, tent δ (clockPath ω (grid h 0)) ∂gaussianProduct) ≤ 2 * δ :=
    (integral_mono (clock_tent_integrable hδ _) (integrable_const _)
      (fun ω => tent_le hδ _)).trans_eq (by simp)
  have hs : Real.sqrt (n : ℝ) ≤ Real.sqrt (n + 1 : ℝ) := Real.sqrt_le_sqrt (by linarith)
  have hm := mul_le_mul_of_nonneg_left hs
    (mul_nonneg (by positivity : 0 ≤ 32 * δ ^ 2) (peak_nonneg h))
  rw [show peak h = peak T * Real.sqrt (n + 1 : ℝ) by
    dsimp only [h]; simpa only [Nat.cast_add, Nat.cast_one] using peak_div T (n + 1)] at hp hm
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ (n + 1 : ℝ))
  simp only [nearEnergy, Nat.cast_add, Nat.cast_one]
  change (∫ ω, δ * ∑ i ∈ Finset.range (n + 1), tent δ (clockPath ω (grid h i))
    ∂gaussianProduct) ≤ _
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => clock_tent_integrable hδ _),
    Finset.sum_range_succ']
  have hp' : (∑ i ∈ Finset.range n, ∫ ω, tent δ (clockPath ω (grid h (i + 1)))
      ∂gaussianProduct) ≤ 32 * δ ^ 2 * peak T * (n + 1 : ℝ) := by
    calc
      _ ≤ 32 * δ ^ 2 * (peak T * Real.sqrt (n + 1 : ℝ)) * Real.sqrt (n + 1 : ℝ) :=
        hp.trans hm
      _ = 32 * δ ^ 2 * peak T * (Real.sqrt (n + 1 : ℝ)) ^ 2 := by ring
      _ = _ := by rw [hsq]
  exact (mul_le_mul_of_nonneg_left (add_le_add hp' hz) hδ).trans_eq (by ring)

theorem penalty_le_nearEnergy (T : ℝ≥0) (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    {ω : SampleSpace} (hω : ω ∉ bad T n δ) :
    penalty T n ω ≤ nearEnergy T n δ ω := by
  rw [nearEnergy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hx : |clockPath ω (grid (T / n) (i + 1)) - clockPath ω (grid (T / n) i)| < δ := by
    apply lt_of_not_ge
    intro h
    exact hω (mem_iUnion.mpr ⟨⟨i, Finset.mem_range.mp hi⟩, h⟩)
  exact penalty_le_tent hδ hx.le

theorem penalty_tail_le (T : ℝ≥0) (n : ℕ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    gaussianProduct.real {ω | ε ≤ penalty T n ω} ≤ gaussianProduct.real (bad T n δ) +
      (∫ ω, nearEnergy T n δ ω ∂gaussianProduct) / ε := by
  have hm : gaussianProduct.real {ω | ε ≤ nearEnergy T n δ ω} ≤
      (∫ ω, nearEnergy T n δ ω ∂gaussianProduct) / ε := by
    apply (le_div_iff₀ hε).mpr
    rw [mul_comm]
    exact mul_meas_ge_le_integral_of_nonneg (ae_of_all _ (nearEnergy_nonneg T n hδ.le))
      (nearEnergy_integrable T n hδ.le) ε
  have hs : {ω | ε ≤ penalty T n ω} ⊆ bad T n δ ∪ {ω | ε ≤ nearEnergy T n δ ω} := by
    intro ω h
    by_cases hw : ω ∈ bad T n δ
    · exact Or.inl hw
    · exact Or.inr (h.trans (penalty_le_nearEnergy T n hδ.le hw))
  exact ((measureReal_mono hs (by finiteness)).trans (measureReal_union_le _ _)).trans
    (add_le_add le_rfl hm)

theorem rate_identity (x K : ℝ) (hx : 0 < x) :
    2 * (x ^ (-(4/9 : ℝ))) ^ 2 + K * x * (x ^ (-(4/9 : ℝ))) ^ 3 =
      2 * x ^ (-(8/9 : ℝ)) + K * x ^ (-(1/3 : ℝ)) := by
  have h2 : (x ^ (-(4/9 : ℝ))) ^ 2 = x ^ (-(8/9 : ℝ)) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hx.le]; norm_num
  have h3 : (x ^ (-(4/9 : ℝ))) ^ 3 = x ^ (-(4/3 : ℝ)) := by
    rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul hx.le]; norm_num
  have ha := Real.rpow_add hx 1 (-(4/3 : ℝ))
  norm_num only [Real.rpow_one] at ha
  rw [h2,h3]
  calc
    _ = 2 * x ^ (-(8/9 : ℝ)) + K * (x * x ^ (-(4/3 : ℝ))) := by ring
    _ = _ := by rw [← ha]

attribute [local irreducible] nearEnergy penalty IBMUniformClockMaximum.bad

theorem nearEnergy_mean_tendsto {T : ℝ≥0} (hT : 0 < T) :
    Filter.Tendsto (fun n : ℕ => ∫ ω,
      nearEnergy T (n + 1) ((n + 1 : ℝ) ^ (-(4/9 : ℝ))) ω ∂gaussianProduct)
      Filter.atTop (nhds 0) := by
  have hb (n : ℕ) : (∫ ω, nearEnergy T (n + 1) ((n + 1 : ℝ) ^ (-(4/9 : ℝ))) ω
      ∂gaussianProduct) ≤ 2 * (n + 1 : ℝ) ^ (-(8/9 : ℝ)) +
      (32 * peak T) * (n + 1 : ℝ) ^ (-(1/3 : ℝ)) := by
    have h := nearEnergy_mean_le hT
      (δ := (n + 1 : ℝ) ^ (-(4/9 : ℝ))) (by positivity) n
    simpa only [rate_identity _ _ (by positivity : 0 < (n + 1 : ℝ))] using h
  have hn : Filter.Tendsto (fun n : ℕ => (n + 1 : ℝ)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h8 := (tendsto_rpow_neg_atTop (by norm_num : 0 < (8/9 : ℝ))).comp hn
  have h3 := (tendsto_rpow_neg_atTop (by norm_num : 0 < (1/3 : ℝ))).comp hn
  apply squeeze_zero (fun n => integral_nonneg (nearEnergy_nonneg T (n + 1) (by positivity))) hb
  simpa only [Function.comp_def, mul_zero, add_zero] using
    (h8.const_mul 2).add (h3.const_mul (32 * peak T))

theorem penalty_tendstoInMeasure {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure gaussianProduct (fun n : ℕ => penalty T (n + 1))
      Filter.atTop (fun _ => (0 : ℝ)) := by
  apply tendstoInMeasure_iff_measureReal_norm.mpr
  intro ε hε
  simp only [sub_zero, Real.norm_eq_abs, abs_of_nonneg (penalty_nonneg _ _ _)]
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun n =>
    penalty_tail_le T (n + 1) (δ := (n + 1 : ℝ) ^ (-(4/9 : ℝ)))
      (Real.rpow_pos_of_pos (by positivity : 0 < (n + 1 : ℝ)) _) hε)
  simpa only [zero_div, add_zero] using
    (bad_probability_tendsto T).add ((nearEnergy_mean_tendsto hT).div_const ε)

end OperatorDerivativeRewrite.Foundation.IBMUniformCrossingPenalty
