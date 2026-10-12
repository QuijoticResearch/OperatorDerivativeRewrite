import Foundation.GaussianHermiteTimeKernel

/-! Continuous adapted Gaussian L2 curves: genuine left-step convergence in
product L2 and convergence of the existing predictable stochastic integrals.
No path continuity, derivative formula, or stochastic representation is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianContinuousIntegrands
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProcess
open GaussianTimeProductL2 GaussianProductDerivative GaussianBochnerDerivative
open GaussianPredictableFull GaussianBrownianQuadraticVariation

/-- Left endpoint sampling of an actual Gaussian L2 curve. -/
def stepValue (v : ℝ≥0 → GaussianL2) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0)
    (x : ℝ) : GaussianL2 :=
  ∑ i : Fin m, (Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)).indicator
    (fun _ => v (τ i.castSucc)) x

def horizonValue (v : ℝ≥0 → GaussianL2) (T : ℝ≥0) : ℝ → GaussianL2 :=
  (Ioc 0 (T : ℝ)).indicator (fun x => v x.toNNReal)

theorem stepValue_on_interval (v : ℝ≥0 → GaussianL2) {m : ℕ}
    (τ : Fin (m + 1) → ℝ≥0) (hτ : Monotone τ) (i : Fin m) (x : ℝ)
    (hx : x ∈ Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)) :
    stepValue v τ x = v (τ i.castSucc) := by
  rw [stepValue, Finset.sum_eq_single i, indicator_of_mem hx]
  · intro j _ hji
    apply indicator_of_notMem
    intro hj
    rcases lt_or_gt_of_ne hji with hjlt | hjgt
    · have hle : (τ j.succ : ℝ) ≤ τ i.castSucc := hτ (Fin.succ_le_castSucc_iff.mpr hjlt)
      linarith [hx.1, hj.2]
    · have hle : (τ i.succ : ℝ) ≤ τ j.castSucc := hτ (Fin.succ_le_castSucc_iff.mpr hjgt)
      linarith [hj.1, hx.2]
  · simp

theorem stepValue_outside (v : ℝ≥0 → GaussianL2) {m : ℕ}
    (τ : Fin (m + 1) → ℝ≥0) (hτ : Monotone τ) (x : ℝ)
    (hx : x ∉ Ioc (τ 0 : ℝ) (τ (Fin.last m) : ℝ)) : stepValue v τ x = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply indicator_of_notMem
  intro hi
  exact hx ⟨lt_of_le_of_lt (hτ (Fin.zero_le _)) hi.1, hi.2.trans (hτ (Fin.le_last _))⟩

theorem stepValue_tendsto (v : ℝ≥0 → GaussianL2) (hv : Continuous v)
    (T : ℝ≥0) (x : ℝ) :
    Tendsto (fun N => stepValue v (uniformTime T N) x) atTop (𝓝 (horizonValue v T x)) := by
  by_cases hx : x ∈ Ioc 0 (T : ℝ)
  · choose i hi using fun N => GaussianQuadraticIto.uniformTime_covers T N x hx
    have hb (N : ℕ) : ‖(uniformTime T N (i N).castSucc : ℝ) - x‖ ≤ (T : ℝ) / (N + 1) := by
      rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (hi N).1.le)]
      have hs := uniformTime_step T N (i N)
      linarith [(hi N).2]
    have ht : Tendsto (fun N : ℕ => (T : ℝ) / (N + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have hr := tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun N => norm_nonneg _) hb ht)
    have hnn := continuous_real_toNNReal.continuousAt.tendsto.comp hr
    simp only [Function.comp_def, Real.toNNReal_coe] at hnn
    have hc := hv.continuousAt.tendsto.comp hnn
    rw [horizonValue, indicator_of_mem hx]
    convert hc using 1
    funext N
    exact stepValue_on_interval v _ (uniformTime_monotone T N) (i N) x (hi N)
  · have hz (N : ℕ) : stepValue v (uniformTime T N) x = 0 := by
      apply stepValue_outside v _ (uniformTime_monotone T N) x
      simpa only [(uniformTime_endpoints T N).1, (uniformTime_endpoints T N).2,
        NNReal.coe_zero] using hx
    simp only [hz, horizonValue, indicator_of_notMem hx]
    exact tendsto_const_nhds

theorem scalarCurry_partition (v : ℝ≥0 → GaussianL2) {m : ℕ}
    (τ : Fin (m + 1) → ℝ≥0) :
    scalarCurry (partitionL2 τ (fun i => v (τ i.castSucc))) =ᵐ[volume] stepValue v τ := by
  rw [partitionL2, map_sum]
  simp only [scalarCurry_productTensor]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin m =>
    BochnerClosedOperator.tensor volume (intervalVector (τ i.castSucc) (τ i.succ))
      (v (τ i.castSucc))), ae_all_iff.mpr (fun i : Fin m =>
        BochnerClosedOperator.tensor_coeFn volume (intervalVector (τ i.castSucc) (τ i.succ))
          (v (τ i.castSucc))), ae_all_iff.mpr (fun i : Fin m =>
            intervalVector_coeFn (τ i.castSucc) (τ i.succ))] with x hs ht hi
  rw [hs]
  simp only [Finset.sum_apply, stepValue]
  apply Finset.sum_congr rfl
  intro i _
  rw [ht i, hi i]
  by_cases hx : x ∈ Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ) <;> simp [hx]

theorem horizonValue_memLp (v : ℝ≥0 → GaussianL2) (hv : Continuous v) (T : ℝ≥0) :
    MemLp (horizonValue v T) 2 volume :=
  GaussianHermiteTimeKernel.continuous_interval_memLp _
    (hv.comp continuous_real_toNNReal) T

/-- The running field is defined independently as the actual product L2 class
with slices `1_(0,T] v(t)`, not as a stochastic-sum limit. -/
def runningField (v : ℝ≥0 → GaussianL2) (hv : Continuous v) (T : ℝ≥0) : TimeProbabilityL2 :=
  scalarCurry.symm ((horizonValue_memLp v hv T).toLp _)

theorem runningField_slices (v : ℝ≥0 → GaussianL2) (hv : Continuous v) (T : ℝ≥0) :
    scalarCurry (runningField v hv T) =ᵐ[volume] horizonValue v T := by
  rw [runningField, scalarCurry.apply_symm_apply]
  exact MemLp.coeFn_toLp _

theorem stepValue_bound (v : ℝ≥0 → GaussianL2) (T : ℝ≥0) (M : ℝ) (_hM : 0 ≤ M)
    (hv : ∀ t ≤ T, ‖v t‖ ≤ M) (N : ℕ) (x : ℝ) :
    ‖stepValue v (uniformTime T N) x‖ ≤ (Ioc 0 (T : ℝ)).indicator (fun _ => M) x := by
  by_cases hx : x ∈ Ioc 0 (T : ℝ)
  · obtain ⟨i, hi⟩ := GaussianQuadraticIto.uniformTime_covers T N x hx
    rw [stepValue_on_interval v _ (uniformTime_monotone T N) i x hi, indicator_of_mem hx]
    apply hv
    change (uniformTime T N i.castSucc : ℝ) ≤ T
    exact (hi.1.trans_le hx.2).le
  · rw [indicator_of_notMem hx, stepValue_outside v _ (uniformTime_monotone T N) x]
    · simp
    · simpa only [(uniformTime_endpoints T N).1, (uniformTime_endpoints T N).2,
        NNReal.coe_zero] using hx

/-- Strong product-L2 convergence, obtained by dominated convergence on a
compact time interval and continuity in Gaussian L2. -/
theorem partition_tendsto (v : ℝ≥0 → GaussianL2) (hv : Continuous v) (T : ℝ≥0) :
    Tendsto (fun N => partitionL2 (uniformTime T N)
      (fun i => v (uniformTime T N i.castSucc))) atTop (𝓝 (runningField v hv T)) := by
  let P (N : ℕ) := scalarCurry (partitionL2 (uniformTime T N)
    (fun i => v (uniformTime T N i.castSucc)))
  let V := (horizonValue_memLp v hv T).toLp (horizonValue v T)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hv.comp continuous_real_toNNReal).continuousOn (s := Icc 0 (T : ℝ))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, T.coe_nonneg⟩)
  have hMv : ∀ t : ℝ≥0, t ≤ T → ‖v t‖ ≤ M := by
    intro t ht
    simpa using hM t ⟨t.coe_nonneg, ht⟩
  let B : ℝ → ℝ := (Ioc 0 (T : ℝ)).indicator (fun _ => 4 * M ^ 2)
  have hB : Integrable B volume := IntegrableOn.integrable_indicator (integrableOn_const (by simp)) measurableSet_Ioc
  have hV : V =ᵐ[volume] horizonValue v T := MemLp.coeFn_toLp _
  have hi := tendsto_integral_of_dominated_convergence B
    (F := fun N x => ‖P N x - V x‖ ^ 2) (f := fun _ => (0 : ℝ))
    (fun N => ((Lp.aestronglyMeasurable (P N)).sub (Lp.aestronglyMeasurable V)).norm.pow 2)
    hB (fun N => ?_) ?_
  · have he (N : ℕ) : ‖P N - V‖ ^ 2 = ∫ x, ‖P N x - V x‖ ^ 2 := by
      rw [BochnerL2Dominated.norm_sq_integral]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (P N) V] with x hx
      simp only [hx, Pi.sub_apply]
    simp only [integral_zero] at hi
    have hn : Tendsto (fun N => ‖P N - V‖ ^ 2) atTop (𝓝 0) := by simpa only [he] using hi
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hn
    simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hs
    simpa only [Function.comp_def, P, V, runningField, scalarCurry.symm_apply_apply] using scalarCurry.symm.continuous.continuousAt.tendsto.comp
      (tendsto_iff_norm_sub_tendsto_zero.mpr hs)
  · filter_upwards [scalarCurry_partition v (uniformTime T N), hV] with x hp hq
    change P N x = _ at hp
    rw [hp, hq, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    by_cases hx : x ∈ Ioc 0 (T : ℝ)
    · have hb := stepValue_bound v T M hM0 hMv N x
      rw [indicator_of_mem hx] at hb
      have hc := hMv x.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hx.2)
      rw [horizonValue, indicator_of_mem hx]
      change _ ≤ B x
      dsimp only [B]
      rw [indicator_of_mem hx]
      have hd := norm_sub_le (stepValue v (uniformTime T N) x) (v x.toNNReal)
      nlinarith [norm_nonneg (stepValue v (uniformTime T N) x - v x.toNNReal)]
    · have hb := stepValue_bound v T M hM0 hMv N x
      rw [indicator_of_notMem hx] at hb
      have hz := norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
      simp [hz, horizonValue, B, hx]
  · filter_upwards [ae_all_iff.mpr (fun N => scalarCurry_partition v (uniformTime T N)), hV]
      with x hp hq
    have ht := stepValue_tendsto v hv T x
    change ∀ N, P N x = _ at hp
    simpa only [hp, hq, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      ((ht.sub (tendsto_const_nhds (x := horizonValue v T x))).norm.pow 2)

theorem runningField_mem (v : ℝ≥0 → GaussianL2) (hv : Continuous v)
    (ha : ∀ t, AEStronglyMeasurable[naturalFiltration t] (v t) gaussianProduct)
    (T : ℝ≥0) : runningField v hv T ∈ fullPredictable := by
  apply fullPredictable_isClosed.mem_of_tendsto (partition_tendsto v hv T)
  apply Eventually.of_forall
  intro N
  exact fullPredictable.sum_mem fun _i _ => past_step_mem_fullPredictable _ _ _ (ha _)

def predictableField (v : ℝ≥0 → GaussianL2) (hv : Continuous v)
    (ha : ∀ t, AEStronglyMeasurable[naturalFiltration t] (v t) gaussianProduct)
    (T : ℝ≥0) : fullPredictable := ⟨runningField v hv T, runningField_mem v hv ha T⟩

def predictableStep (v : ℝ≥0 → GaussianL2)
    (ha : ∀ t, AEStronglyMeasurable[naturalFiltration t] (v t) gaussianProduct)
    (T : ℝ≥0) (N : ℕ) : fullPredictable :=
  ⟨partitionL2 (uniformTime T N) (fun i => v (uniformTime T N i.castSucc)),
    fullPredictable.sum_mem fun _i _ => past_step_mem_fullPredictable _ _ _ (ha _)⟩

theorem predictableStep_tendsto (v : ℝ≥0 → GaussianL2) (hv : Continuous v)
    (ha : ∀ t, AEStronglyMeasurable[naturalFiltration t] (v t) gaussianProduct) (T : ℝ≥0) :
    Tendsto (predictableStep v ha T) atTop (𝓝 (predictableField v hv ha T)) :=
  tendsto_subtype_rng.mpr (partition_tendsto v hv T)

/-- Stochastic sums converge to J of the independently identified running field. -/
theorem integral_step_tendsto (v : ℝ≥0 → GaussianL2) (hv : Continuous v)
    (ha : ∀ t, AEStronglyMeasurable[naturalFiltration t] (v t) gaussianProduct) (T : ℝ≥0) :
    Tendsto (fun N => itoIntegral (predictableStep v ha T N)) atTop
      (𝓝 (itoIntegral (predictableField v hv ha T))) :=
  itoIntegral.continuous.continuousAt.tendsto.comp (predictableStep_tendsto v hv ha T)

/-- The existing J of each adapted step has the actual stochastic-sum representative. -/
theorem integral_step_coeFn (v : ℝ≥0 → GaussianL2)
    (ha : ∀ t, AEStronglyMeasurable[naturalFiltration t] (v t) gaussianProduct)
    (T : ℝ≥0) (N : ℕ) :
    itoIntegral (predictableStep v ha T N) =ᵐ[gaussianProduct] fun ω =>
      ∑ i : Fin (N + 1), v (uniformTime T N i.castSucc) ω *
        (process (uniformTime T N i.succ) ω - process (uniformTime T N i.castSucc) ω) := by
  have he : predictableStep v ha T N = domainEquiv.symm (GaussianPastStepCompletion.pastPartition (uniformTime T N) (uniformTime_monotone T N) (fun i => v (uniformTime T N i.castSucc)) (fun i => ha _)) := by
    apply Subtype.ext
    change partitionL2 _ _ = (GaussianPastStepCompletion.pastPartition _ _ _ _ : TimeProbabilityL2)
    exact (GaussianPastStepCompletion.pastPartition_coe _ _ _ _).symm
  rw [he]
  exact itoIntegral_past_partition (uniformTime T N) (uniformTime_monotone T N) _ (fun i => ha _)

theorem stepValue_integrable (v : ℝ≥0 → GaussianL2) {m : ℕ}
    (τ : Fin (m + 1) → ℝ≥0) : Integrable (stepValue v τ) volume := by
  apply integrable_finsetSum
  intro i _
  exact IntegrableOn.integrable_indicator (integrableOn_const (by simp)) measurableSet_Ioc

theorem stepValue_integral (v : ℝ≥0 → GaussianL2) {m : ℕ}
    (τ : Fin (m + 1) → ℝ≥0) (hτ : Monotone τ) :
    (∫ x, stepValue v τ x) =
      ∑ i : Fin m, ((τ i.succ : ℝ) - τ i.castSucc) • v (τ i.castSucc) := by
  simp only [stepValue]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_indicator measurableSet_Ioc, setIntegral_const, Real.volume_real_Ioc,
      max_eq_left (sub_nonneg.mpr (show (τ i.castSucc : ℝ) ≤ τ i.succ from
        hτ (Fin.castSucc_le_succ i)))]
  · intro i _
    exact IntegrableOn.integrable_indicator (integrableOn_const (by simp)) measurableSet_Ioc

/-- Ordinary left Riemann sums converge in Gaussian L2 to the genuine Bochner
integral. No adaptation is needed for this deterministic statement. -/
theorem drift_sum_tendsto (v : ℝ≥0 → GaussianL2) (hv : Continuous v) (T : ℝ≥0) :
    Tendsto (fun N => ∑ i : Fin (N + 1),
      ((uniformTime T N i.succ : ℝ) - uniformTime T N i.castSucc) •
        v (uniformTime T N i.castSucc)) atTop
      (𝓝 (∫ x in 0..(T : ℝ), v x.toNNReal)) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hv.comp continuous_real_toNNReal).continuousOn (s := Icc 0 (T : ℝ))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, T.coe_nonneg⟩)
  have hMv : ∀ t : ℝ≥0, t ≤ T → ‖v t‖ ≤ M := by
    intro t ht
    simpa using hM t ⟨t.coe_nonneg, ht⟩
  have hB : Integrable ((Ioc 0 (T : ℝ)).indicator (fun _ => M)) volume :=
    IntegrableOn.integrable_indicator (integrableOn_const (by simp)) measurableSet_Ioc
  have ht := tendsto_integral_of_dominated_convergence _
    (fun N => (stepValue_integrable v (uniformTime T N)).aestronglyMeasurable) hB
    (fun N => Eventually.of_forall (stepValue_bound v T M hM0 hMv N))
    (Eventually.of_forall (stepValue_tendsto v hv T))
  simp only [stepValue_integral v _ (uniformTime_monotone T _), horizonValue,
    integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le T.coe_nonneg] at ht
  exact ht

end OperatorDerivativeRewrite.Foundation.GaussianContinuousIntegrands




