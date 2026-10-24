import Foundation.IBMClippedClockCrossing

/-! Actual Brownian large-increment energy, controlled by verified fourth
moments. This is independent of any stochastic-integral convention. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClippedClockTail
open InfiniteGaussian GaussianTimeProcess GaussianTimeDivergence GaussianTimeFieldNorm
open GaussianBrownianQuadraticVariation

theorem fourth_integral (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ Y, (process t Y-process s Y)^4 ∂gaussianProduct) = 3*((t:ℝ)-s)^2 := by
  calc
    _ = ∫ Y, (firstChaosEmbedding (incrementDirection s t) Y)^4 ∂gaussianProduct := by
      apply integral_congr_ae
      filter_upwards [process_increment_ae s t hst] with Y hY
      change firstChaosEmbedding (incrementDirection s t) Y = process t Y-process s Y at hY
      rw [hY]
    _ = _ := by rw [IBMSourceMoments.firstChaos_fourth,incrementDirection_norm_sq s t hst]

def cell (δ : ℝ) (s t : ℝ≥0) (Y : SampleSpace) : ℝ :=
  if δ < |process t Y-process s Y| then (process t Y-process s Y)^2 else 0

theorem cell_nonneg (δ : ℝ) (s t : ℝ≥0) (Y : SampleSpace) : 0 ≤ cell δ s t Y := by
  unfold cell
  split_ifs <;> positivity

theorem cell_integrable (δ : ℝ) (s t : ℝ≥0) : Integrable (cell δ s t) gaussianProduct := by
  have hd := (process_stronglyMeasurable t).measurable.sub (process_stronglyMeasurable s).measurable
  have hm : Measurable (cell δ s t) := Measurable.ite
    (measurableSet_lt measurable_const (continuous_abs.measurable.comp hd)) (hd.pow_const 2) measurable_const
  apply (((process_memLp t 2 (by norm_num)).sub (process_memLp s 2 (by norm_num))).integrable_sq).mono'
    hm.aestronglyMeasurable
  exact ae_of_all _ fun Y => by
    simp only [Pi.sub_apply]
    rw [Real.norm_of_nonneg (cell_nonneg δ s t Y)]
    unfold cell
    split_ifs <;> nlinarith [sq_nonneg (process t Y-process s Y)]

theorem cell_bound (δ : ℝ) (hδ : 0 < δ) (s t : ℝ≥0) (Y : SampleSpace) :
    cell δ s t Y ≤ (process t Y-process s Y)^4/δ^2 := by
  unfold cell
  split_ifs with h
  · rw [le_div_iff₀ (sq_pos_of_pos hδ)]
    have hs : δ^2 ≤ (process t Y-process s Y)^2 := by
      nlinarith [sq_abs (process t Y-process s Y),abs_nonneg (process t Y-process s Y)]
    nlinarith [sq_nonneg (process t Y-process s Y)]
  · positivity

theorem cell_mean_bound (δ : ℝ) (hδ : 0 < δ) (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ Y, cell δ s t Y ∂gaussianProduct) ≤ 3*((t:ℝ)-s)^2/δ^2 := by
  have h4 : Integrable (fun Y => (process t Y-process s Y)^4) gaussianProduct := by
    simpa only [Pi.sub_apply,Real.norm_eq_abs,(show Even 4 by decide).pow_abs] using
      ((process_memLp t 4 (by norm_num)).sub (process_memLp s 4 (by norm_num))).integrable_norm_pow'
  have h := integral_mono (cell_integrable δ s t) (h4.div_const (δ^2)) (cell_bound δ hδ s t)
  simpa only [integral_div,fourth_integral s t hst] using h

def value (δ : ℝ) (T : ℝ≥0) (N : ℕ) (Y : SampleSpace) : ℝ :=
  ∑ i : Fin (N+1), cell δ (uniformTime T N i.castSucc) (uniformTime T N i.succ) Y

theorem value_nonneg (δ : ℝ) (T : ℝ≥0) (N : ℕ) (Y : SampleSpace) : 0 ≤ value δ T N Y :=
  Finset.sum_nonneg fun i _ => cell_nonneg δ _ _ Y

theorem value_integrable (δ : ℝ) (T : ℝ≥0) (N : ℕ) : Integrable (value δ T N) gaussianProduct :=
  integrable_finset_sum _ fun _ _ => cell_integrable _ _ _

theorem mean_bound (δ : ℝ) (hδ : 0 < δ) (T : ℝ≥0) (N : ℕ) :
    (∫ Y, value δ T N Y ∂gaussianProduct) ≤ 3*(T:ℝ)^2/((N+1)*δ^2) := by
  unfold value
  rw [integral_finset_sum _ (fun _ _ => cell_integrable _ _ _)]
  calc
    _ ≤ ∑ i : Fin (N+1), 3*((uniformTime T N i.succ:ℝ)-uniformTime T N i.castSucc)^2/δ^2 :=
      Finset.sum_le_sum fun i _ => cell_mean_bound δ hδ _ _ (uniformTime_monotone T N (Fin.castSucc_le_succ i))
    _ = _ := by
      simp only [uniformTime_step,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        Nat.cast_add,Nat.cast_one]
      have hn : (N+1:ℝ) ≠ 0 := by positivity
      have hd : δ ≠ 0 := ne_of_gt hδ
      field_simp
      <;> ring

def width (N : ℕ) : ℝ := (Real.sqrt (Real.sqrt (N+1:ℝ)))⁻¹

theorem width_pos (N : ℕ) : 0 < width N := by unfold width; positivity

theorem width_tendsto : Tendsto width atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ => (Real.sqrt (Real.sqrt (N+1:ℝ)))⁻¹) atTop (𝓝 0)
  have hs : Tendsto (fun N : ℕ => Real.sqrt (Real.sqrt (N+1:ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
  simpa only [one_div] using (tendsto_const_nhds.div_atTop hs :
    Tendsto (fun N : ℕ => 1/Real.sqrt (Real.sqrt (N+1:ℝ))) atTop (𝓝 0))

theorem width_sq (N : ℕ) : (width N)^2 = 1/Real.sqrt (N+1:ℝ) := by
  rw [width,inv_pow,Real.sq_sqrt (Real.sqrt_nonneg _)]
  simp only [one_div]

theorem width_mean_tendsto (T : ℝ≥0) :
    Tendsto (fun N => ∫ Y, value (width N) T N Y ∂gaussianProduct) atTop (𝓝 0) := by
  have hb (N : ℕ) : (∫ Y, value (width N) T N Y ∂gaussianProduct) ≤
      3*(T:ℝ)^2/Real.sqrt (N+1:ℝ) := by
    have h := mean_bound (width N) (width_pos N) T N
    rw [width_sq] at h
    convert h using 1
    have hs := Real.sq_sqrt (by positivity : (0:ℝ) ≤ N+1)
    have hp : Real.sqrt (N+1:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    have hn : (N+1:ℝ) ≠ 0 := by positivity
    field_simp
    nlinarith
  exact squeeze_zero (fun N => integral_nonneg (value_nonneg (width N) T N)) hb
    (tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)))

end OperatorDerivativeRewrite.Foundation.IBMClippedClockTail
