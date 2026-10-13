import Foundation.GaussianContinuousIntegrands
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianRefiningPartitions
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 GaussianProductDerivative
open GaussianPredictableFull GaussianContinuousIntegrands

theorem covers {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (x : ℝ)
    (hx : x ∈ Ioc (τ 0 : ℝ) (τ (Fin.last n) : ℝ)) :
    ∃ k : Fin n, x ∈ Ioc (τ k.castSucc : ℝ) (τ k.succ : ℝ) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    by_cases h : x ≤ (τ (Fin.last n).castSucc : ℝ)
    · obtain ⟨k, hk⟩ := ih (fun i => τ i.castSucc) ⟨hx.1, h⟩
      exact ⟨k.castSucc, hk⟩
    · exact ⟨Fin.last n, lt_of_not_ge h, hx.2⟩


/-- Strong sampling convergence on any monotone refining mesh with fixed endpoints. -/
theorem step_tendsto (v : ℝ≥0 → GaussianL2) (hv : Continuous v)
    (m : ℕ → ℕ) (τ : (N : ℕ) → Fin (m N+1) → ℝ≥0)
    (hτ : ∀ N, Monotone (τ N)) (T : ℝ≥0)
    (hstart : ∀ N, τ N 0 = 0) (hend : ∀ N, τ N (Fin.last (m N)) = T)
    (ε : ℕ → ℝ) (hlim : Tendsto ε atTop (𝓝 0))
    (hmesh : ∀ N (k : Fin (m N)), (τ N k.succ:ℝ)-τ N k.castSucc ≤ ε N) (x : ℝ) :
    Tendsto (fun N => stepValue v (τ N) x) atTop (𝓝 (horizonValue v T x)) := by
  by_cases hx : x ∈ Ioc 0 (T:ℝ)
  · have hc (N : ℕ) : ∃ k : Fin (m N), x ∈ Ioc (τ N k.castSucc:ℝ) (τ N k.succ:ℝ) :=
      covers (τ N) x (by simpa only [hstart, hend, NNReal.coe_zero] using hx)
    choose i hi using hc
    have hb (N : ℕ) : ‖(τ N (i N).castSucc:ℝ)-x‖ ≤ ε N := by
      rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (hi N).1.le)]
      linarith [(hi N).2, hmesh N (i N)]
    have hr := tendsto_iff_norm_sub_tendsto_zero.mpr
      (squeeze_zero (fun N => norm_nonneg _) hb hlim)
    have hnn := continuous_real_toNNReal.continuousAt.tendsto.comp hr
    simp only [Function.comp_def, Real.toNNReal_coe] at hnn
    have hc := hv.continuousAt.tendsto.comp hnn
    rw [horizonValue, indicator_of_mem hx]
    convert hc using 1
    funext N
    exact stepValue_on_interval v _ (hτ N) (i N) x (hi N)
  · have hz (N : ℕ) : stepValue v (τ N) x = 0 := by
      apply stepValue_outside v _ (hτ N) x
      simpa only [hstart, hend, NNReal.coe_zero] using hx
    simp only [hz, horizonValue, indicator_of_notMem hx]
    exact tendsto_const_nhds

theorem step_bound (v : ℝ≥0 → GaussianL2) (T : ℝ≥0) (M : ℝ)
    (hv : ∀ t ≤ T, ‖v t‖ ≤ M) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ)
    (hstart : τ 0 = 0) (hend : τ (Fin.last n) = T) (x : ℝ) :
    ‖stepValue v τ x‖ ≤ (Ioc 0 (T:ℝ)).indicator (fun _ => M) x := by
  by_cases hx : x ∈ Ioc 0 (T:ℝ)
  · obtain ⟨i, hi⟩ := covers τ x (by simpa only [hstart, hend, NNReal.coe_zero] using hx)
    rw [stepValue_on_interval v τ hτ i x hi, indicator_of_mem hx]
    exact hv _ ((hi.1.trans_le hx.2).le : (τ i.castSucc:ℝ) ≤ T)
  · rw [indicator_of_notMem hx, stepValue_outside v τ hτ x]
    · simp
    · simpa only [hstart, hend, NNReal.coe_zero] using hx
/-- Product-L2 convergence to the independently defined running field. -/
theorem partition_tendsto (v : ℝ≥0 → GaussianL2) (hv : Continuous v)
    (m : ℕ → ℕ) (τ : (N : ℕ) → Fin (m N+1) → ℝ≥0)
    (hτ : ∀ N, Monotone (τ N)) (T : ℝ≥0)
    (hstart : ∀ N, τ N 0 = 0) (hend : ∀ N, τ N (Fin.last (m N)) = T)
    (ε : ℕ → ℝ) (hlim : Tendsto ε atTop (𝓝 0))
    (hmesh : ∀ N (k : Fin (m N)), (τ N k.succ:ℝ)-τ N k.castSucc ≤ ε N) :
    Tendsto (fun N => partitionL2 (τ N) (fun i => v (τ N i.castSucc)))
      atTop (𝓝 (runningField v hv T)) := by
  let P (N : ℕ) := scalarCurry (partitionL2 (τ N)
    (fun i => v (τ N i.castSucc)))
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
  · filter_upwards [scalarCurry_partition v (τ N), hV] with x hp hq
    change P N x = _ at hp
    rw [hp, hq, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    by_cases hx : x ∈ Ioc 0 (T : ℝ)
    · have hb := step_bound v T M hMv (τ N) (hτ N) (hstart N) (hend N) x
      rw [indicator_of_mem hx] at hb
      have hc := hMv x.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hx.2)
      rw [horizonValue, indicator_of_mem hx]
      change _ ≤ B x
      dsimp only [B]
      rw [indicator_of_mem hx]
      have hd := norm_sub_le (stepValue v (τ N) x) (v x.toNNReal)
      nlinarith [norm_nonneg (stepValue v (τ N) x - v x.toNNReal)]
    · have hb := step_bound v T M hMv (τ N) (hτ N) (hstart N) (hend N) x
      rw [indicator_of_notMem hx] at hb
      have hz := norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
      simp [hz, horizonValue, B, hx]
  · filter_upwards [ae_all_iff.mpr (fun N => scalarCurry_partition v (τ N)), hV]
      with x hp hq
    have ht := step_tendsto v hv m τ hτ T hstart hend ε hlim hmesh x
    change ∀ N, P N x = _ at hp
    simpa only [hp, hq, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      ((ht.sub (tendsto_const_nhds (x := horizonValue v T x))).norm.pow 2)

/-- Bochner drift convergence on the same general refining mesh. -/
theorem drift_sum_tendsto (v : ℝ≥0 → GaussianL2) (hv : Continuous v)
    (m : ℕ → ℕ) (τ : (N : ℕ) → Fin (m N+1) → ℝ≥0)
    (hτ : ∀ N, Monotone (τ N)) (T : ℝ≥0)
    (hstart : ∀ N, τ N 0 = 0) (hend : ∀ N, τ N (Fin.last (m N)) = T)
    (ε : ℕ → ℝ) (hlim : Tendsto ε atTop (𝓝 0))
    (hmesh : ∀ N (k : Fin (m N)), (τ N k.succ:ℝ)-τ N k.castSucc ≤ ε N) :
    Tendsto (fun N => ∑ i : Fin (m N), ((τ N i.succ:ℝ)-τ N i.castSucc) • v (τ N i.castSucc))
      atTop (𝓝 (∫ x in 0..(T:ℝ), v x.toNNReal)) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hv.comp continuous_real_toNNReal).continuousOn (s := Icc 0 (T : ℝ))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, T.coe_nonneg⟩)
  have hMv : ∀ t : ℝ≥0, t ≤ T → ‖v t‖ ≤ M := by
    intro t ht
    simpa using hM t ⟨t.coe_nonneg, ht⟩
  have hB : Integrable ((Ioc 0 (T : ℝ)).indicator (fun _ => M)) volume :=
    IntegrableOn.integrable_indicator (integrableOn_const (by simp)) measurableSet_Ioc
  have ht := tendsto_integral_of_dominated_convergence _
    (fun N => (stepValue_integrable v (τ N)).aestronglyMeasurable) hB
    (fun N => Eventually.of_forall (step_bound v T M hMv (τ N) (hτ N) (hstart N) (hend N)))
    (Eventually.of_forall (step_tendsto v hv m τ hτ T hstart hend ε hlim hmesh))
  simp only [stepValue_integral v _ (hτ _), horizonValue,
    integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le T.coe_nonneg] at ht
  exact ht


/-- Actual adapted step in the existing independently defined predictable space. -/
def predictableStep (v : ℝ≥0 → GaussianL2)
    (ha : ∀ t, AEStronglyMeasurable[naturalFiltration t] (v t) gaussianProduct)
    {n : ℕ} (τ : Fin (n+1) → ℝ≥0) : fullPredictable :=
  ⟨partitionL2 τ (fun i => v (τ i.castSucc)),
    fullPredictable.sum_mem fun _i _ => past_step_mem_fullPredictable _ _ _ (ha _)⟩

theorem predictableStep_tendsto (v : ℝ≥0 → GaussianL2) (hv : Continuous v)
    (ha : ∀ t, AEStronglyMeasurable[naturalFiltration t] (v t) gaussianProduct)
    (m : ℕ → ℕ) (τ : (N : ℕ) → Fin (m N+1) → ℝ≥0)
    (hτ : ∀ N, Monotone (τ N)) (T : ℝ≥0)
    (hstart : ∀ N, τ N 0 = 0) (hend : ∀ N, τ N (Fin.last (m N)) = T)
    (ε : ℕ → ℝ) (hlim : Tendsto ε atTop (𝓝 0))
    (hmesh : ∀ N (k : Fin (m N)), (τ N k.succ:ℝ)-τ N k.castSucc ≤ ε N) :
    Tendsto (fun N => predictableStep v ha (τ N)) atTop
      (𝓝 (predictableField v hv ha T)) :=
  tendsto_subtype_rng.mpr (partition_tendsto v hv m τ hτ T hstart hend ε hlim hmesh)

theorem integral_step_tendsto (v : ℝ≥0 → GaussianL2) (hv : Continuous v)
    (ha : ∀ t, AEStronglyMeasurable[naturalFiltration t] (v t) gaussianProduct)
    (m : ℕ → ℕ) (τ : (N : ℕ) → Fin (m N+1) → ℝ≥0)
    (hτ : ∀ N, Monotone (τ N)) (T : ℝ≥0)
    (hstart : ∀ N, τ N 0 = 0) (hend : ∀ N, τ N (Fin.last (m N)) = T)
    (ε : ℕ → ℝ) (hlim : Tendsto ε atTop (𝓝 0))
    (hmesh : ∀ N (k : Fin (m N)), (τ N k.succ:ℝ)-τ N k.castSucc ≤ ε N) :
    Tendsto (fun N => itoIntegral (predictableStep v ha (τ N))) atTop
      (𝓝 (itoIntegral (predictableField v hv ha T))) :=
  itoIntegral.continuous.continuousAt.tendsto.comp
    (predictableStep_tendsto v hv ha m τ hτ T hstart hend ε hlim hmesh)

theorem integral_step_coeFn (v : ℝ≥0 → GaussianL2)
    (ha : ∀ t, AEStronglyMeasurable[naturalFiltration t] (v t) gaussianProduct)
    {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ) :
    itoIntegral (predictableStep v ha τ) =ᵐ[gaussianProduct] fun ω =>
      ∑ i : Fin n, v (τ i.castSucc) ω * (process (τ i.succ) ω-process (τ i.castSucc) ω) := by
  have he : predictableStep v ha τ = domainEquiv.symm
      (GaussianPastStepCompletion.pastPartition τ hτ (fun i => v (τ i.castSucc)) (fun i => ha _)) := by
    apply Subtype.ext
    change partitionL2 _ _ = (GaussianPastStepCompletion.pastPartition _ _ _ _ : TimeProbabilityL2)
    exact (GaussianPastStepCompletion.pastPartition_coe _ _ _ _).symm
  rw [he]
  exact itoIntegral_past_partition τ hτ _ (fun i => ha _)

/-- Capping never enlarges a cell of a monotone mesh. -/
theorem cap_mesh_bound {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ)
    (r : ℝ≥0) (ε : ℝ) (hmesh : ∀ k : Fin n, (τ k.succ:ℝ)-τ k.castSucc ≤ ε)
    (k : Fin n) : (min (τ k.succ) r:ℝ)-min (τ k.castSucc) r ≤ ε := by
  have hs : τ k.castSucc ≤ τ k.succ := hτ (Fin.castSucc_le_succ k)
  by_cases h : τ k.castSucc ≤ r
  · rw [min_eq_left h]
    exact (sub_le_sub_right (show (min (τ k.succ) r:ℝ) ≤ τ k.succ from min_le_left _ _) _).trans (hmesh k)
  · have hr : r ≤ τ k.castSucc := (le_of_not_ge h)
    rw [min_eq_right hr, min_eq_right (show (r:ℝ) ≤ τ k.succ from hr.trans hs), sub_self]
    exact (sub_nonneg.mpr (show (τ k.castSucc:ℝ) ≤ τ k.succ from hs)).trans (hmesh k)

theorem cap_monotone {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ) (r : ℝ≥0) :
    Monotone (fun k => min (τ k) r) := fun _ _ h => min_le_min (hτ h) le_rfl

theorem capped_drift_sum_tendsto (v : ℝ≥0 → GaussianL2) (hv : Continuous v)
    (m : ℕ → ℕ) (τ : (N : ℕ) → Fin (m N+1) → ℝ≥0)
    (hτ : ∀ N, Monotone (τ N)) (T r : ℝ≥0)
    (hstart : ∀ N, τ N 0 = 0) (hend : ∀ N, τ N (Fin.last (m N)) = T)
    (ε : ℕ → ℝ) (hlim : Tendsto ε atTop (𝓝 0))
    (hmesh : ∀ N (k : Fin (m N)), (τ N k.succ:ℝ)-τ N k.castSucc ≤ ε N) :
    Tendsto (fun N => ∑ i : Fin (m N),
      ((min (τ N i.succ) r:ℝ)-min (τ N i.castSucc) r) • v (min (τ N i.castSucc) r))
      atTop (𝓝 (∫ x in 0..(min T r:ℝ), v x.toNNReal)) := by
  exact drift_sum_tendsto v hv m (fun N k => min (τ N k) r)
    (fun N => cap_monotone (τ N) (hτ N) r) (min T r)
    (fun N => by simp [hstart N]) (fun N => by simp [hend N]) ε hlim
    (fun N => cap_mesh_bound (τ N) (hτ N) r (ε N) (hmesh N))

theorem capped_integral_step_tendsto (v : ℝ≥0 → GaussianL2) (hv : Continuous v)
    (ha : ∀ t, AEStronglyMeasurable[naturalFiltration t] (v t) gaussianProduct)
    (m : ℕ → ℕ) (τ : (N : ℕ) → Fin (m N+1) → ℝ≥0)
    (hτ : ∀ N, Monotone (τ N)) (T r : ℝ≥0)
    (hstart : ∀ N, τ N 0 = 0) (hend : ∀ N, τ N (Fin.last (m N)) = T)
    (ε : ℕ → ℝ) (hlim : Tendsto ε atTop (𝓝 0))
    (hmesh : ∀ N (k : Fin (m N)), (τ N k.succ:ℝ)-τ N k.castSucc ≤ ε N) :
    Tendsto (fun N => itoIntegral (predictableStep v ha (fun k => min (τ N k) r))) atTop
      (𝓝 (itoIntegral (predictableField v hv ha (min T r)))) := by
  exact integral_step_tendsto v hv ha m (fun N k => min (τ N k) r)
    (fun N => cap_monotone (τ N) (hτ N) r) (min T r)
    (fun N => by simp [hstart N]) (fun N => by simp [hend N]) ε hlim
    (fun N => cap_mesh_bound (τ N) (hτ N) r (ε N) (hmesh N))

end OperatorDerivativeRewrite.Foundation.GaussianRefiningPartitions
