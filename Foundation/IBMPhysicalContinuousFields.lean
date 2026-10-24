import Foundation.IBMPhysicalCorrectionContinuity
import Foundation.ProductL2Equivalence
import Foundation.GaussianRefiningPartitions
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! Genuine physical product-L2 realization and deterministic mesh approximation.
The target is physical H^-1; no spatial Wiener extension is used. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalContinuousFields
open InfiniteGaussian GaussianTimeHilbert GaussianBrownianQuadraticVariation
open IBMPhysicalWeakWiener
local instance : InnerProductSpace ℝ Kernel := InnerProductSpace.rclikeToReal ℂ _
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
local instance : SecondCountableTopology Kernel :=
  (BesselPotentialSpace.toLpₗᵢ ℝ ℂ (-1 : ℝ) 2).isometry.isEmbedding.secondCountableTopology

def curry : Lp Kernel 2 GaussianTimeProductL2.timeProbability ≃ₗᵢ[ℝ]
    Lp (Lp Kernel 2 gaussianProduct) 2 (volume : Measure ℝ) :=
  ProductL2Curry.curryEquiv volume gaussianProduct

def partition {m : ℕ} (τ : Fin (m+1) → ℝ≥0)
    (A : Fin m → Lp Kernel 2 gaussianProduct) :
    Lp Kernel 2 GaussianTimeProductL2.timeProbability :=
  ∑ i : Fin m, ProductL2Curry.productTensor volume gaussianProduct
    (intervalVector (τ i.castSucc) (τ i.succ)) (A i)

def stepValue (v : ℝ≥0 → (Lp Kernel 2 gaussianProduct)) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0)
    (x : ℝ) : (Lp Kernel 2 gaussianProduct) :=
  ∑ i : Fin m, (Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)).indicator
    (fun _ => v (τ i.castSucc)) x

def horizonValue (v : ℝ≥0 → (Lp Kernel 2 gaussianProduct)) (T : ℝ≥0) : ℝ → (Lp Kernel 2 gaussianProduct) :=
  (Ioc 0 (T : ℝ)).indicator (fun x => v x.toNNReal)

theorem stepValue_on_interval (v : ℝ≥0 → (Lp Kernel 2 gaussianProduct)) {m : ℕ}
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

theorem stepValue_outside (v : ℝ≥0 → (Lp Kernel 2 gaussianProduct)) {m : ℕ}
    (τ : Fin (m + 1) → ℝ≥0) (hτ : Monotone τ) (x : ℝ)
    (hx : x ∉ Ioc (τ 0 : ℝ) (τ (Fin.last m) : ℝ)) : stepValue v τ x = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply indicator_of_notMem
  intro hi
  exact hx ⟨lt_of_le_of_lt (hτ (Fin.zero_le _)) hi.1, hi.2.trans (hτ (Fin.le_last _))⟩

theorem step_tendsto (v : ℝ≥0 → (Lp Kernel 2 gaussianProduct)) (hv : Continuous v)
    (m : ℕ → ℕ) (τ : (N : ℕ) → Fin (m N+1) → ℝ≥0)
    (hτ : ∀ N, Monotone (τ N)) (T : ℝ≥0)
    (hstart : ∀ N, τ N 0 = 0) (hend : ∀ N, τ N (Fin.last (m N)) = T)
    (ε : ℕ → ℝ) (hlim : Tendsto ε atTop (𝓝 0))
    (hmesh : ∀ N (k : Fin (m N)), (τ N k.succ:ℝ)-τ N k.castSucc ≤ ε N) (x : ℝ) :
    Tendsto (fun N => stepValue v (τ N) x) atTop (𝓝 (horizonValue v T x)) := by
  by_cases hx : x ∈ Ioc 0 (T:ℝ)
  · have hc (N : ℕ) : ∃ k : Fin (m N), x ∈ Ioc (τ N k.castSucc:ℝ) (τ N k.succ:ℝ) :=
      GaussianRefiningPartitions.covers (τ N) x (by simpa only [hstart, hend, NNReal.coe_zero] using hx)
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

theorem step_bound (v : ℝ≥0 → (Lp Kernel 2 gaussianProduct)) (T : ℝ≥0) (M : ℝ)
    (hv : ∀ t ≤ T, ‖v t‖ ≤ M) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ)
    (hstart : τ 0 = 0) (hend : τ (Fin.last n) = T) (x : ℝ) :
    ‖stepValue v τ x‖ ≤ (Ioc 0 (T:ℝ)).indicator (fun _ => M) x := by
  by_cases hx : x ∈ Ioc 0 (T:ℝ)
  · obtain ⟨i, hi⟩ := GaussianRefiningPartitions.covers τ x (by simpa only [hstart, hend, NNReal.coe_zero] using hx)
    rw [stepValue_on_interval v τ hτ i x hi, indicator_of_mem hx]
    exact hv _ ((hi.1.trans_le hx.2).le : (τ i.castSucc:ℝ) ≤ T)
  · rw [indicator_of_notMem hx, stepValue_outside v τ hτ x]
    · simp
    · simpa only [hstart, hend, NNReal.coe_zero] using hx
theorem curry_partition (v : ℝ≥0 → (Lp Kernel 2 gaussianProduct)) {m : ℕ}
    (τ : Fin (m + 1) → ℝ≥0) :
    curry (partition τ (fun i => v (τ i.castSucc))) =ᵐ[volume] stepValue v τ := by
  rw [partition, map_sum]
  change (∑ i : Fin m, ProductL2Curry.curry volume gaussianProduct
    (ProductL2Curry.productTensor volume gaussianProduct
      (intervalVector (τ i.castSucc) (τ i.succ)) (v (τ i.castSucc)))) =ᵐ[volume] _
  simp only [ProductL2Curry.curry_productTensor]
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

theorem horizonValue_memLp (v : ℝ≥0 → (Lp Kernel 2 gaussianProduct)) (hv : Continuous v) (T : ℝ≥0) :
    MemLp (horizonValue v T) 2 volume :=
  GaussianHermiteTimeKernel.continuous_interval_memLp _
    (hv.comp continuous_real_toNNReal) T

/-- The running field is defined independently as the actual product L2 class
with slices `1_(0,T] v(t)`, not as a stochastic-sum limit. -/
def field (v : ℝ≥0 → (Lp Kernel 2 gaussianProduct)) (hv : Continuous v) (T : ℝ≥0) : (Lp Kernel 2 GaussianTimeProductL2.timeProbability) :=
  curry.symm ((horizonValue_memLp v hv T).toLp _)

theorem field_slices (v : ℝ≥0 → (Lp Kernel 2 gaussianProduct)) (hv : Continuous v) (T : ℝ≥0) :
    curry (field v hv T) =ᵐ[volume] horizonValue v T := by
  rw [field, curry.apply_symm_apply]
  exact MemLp.coeFn_toLp _

theorem partition_tendsto (v : ℝ≥0 → (Lp Kernel 2 gaussianProduct)) (hv : Continuous v)
    (m : ℕ → ℕ) (τ : (N : ℕ) → Fin (m N+1) → ℝ≥0)
    (hτ : ∀ N, Monotone (τ N)) (T : ℝ≥0)
    (hstart : ∀ N, τ N 0 = 0) (hend : ∀ N, τ N (Fin.last (m N)) = T)
    (ε : ℕ → ℝ) (hlim : Tendsto ε atTop (𝓝 0))
    (hmesh : ∀ N (k : Fin (m N)), (τ N k.succ:ℝ)-τ N k.castSucc ≤ ε N) :
    Tendsto (fun N => partition (τ N) (fun i => v (τ N i.castSucc)))
      atTop (𝓝 (field v hv T)) := by
  let P (N : ℕ) := curry (partition (τ N)
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
    simpa only [Function.comp_def, P, V, field, curry.symm_apply_apply] using curry.symm.continuous.continuousAt.tendsto.comp
      (tendsto_iff_norm_sub_tendsto_zero.mpr hs)
  · filter_upwards [curry_partition v (τ N), hV] with x hp hq
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
  · filter_upwards [ae_all_iff.mpr (fun N => curry_partition v (τ N)), hV]
      with x hp hq
    have ht := step_tendsto v hv m τ hτ T hstart hend ε hlim hmesh x
    change ∀ N, P N x = _ at hp
    simpa only [hp, hq, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      ((ht.sub (tendsto_const_nhds (x := horizonValue v T x))).norm.pow 2)


end OperatorDerivativeRewrite.Foundation.IBMPhysicalContinuousFields
