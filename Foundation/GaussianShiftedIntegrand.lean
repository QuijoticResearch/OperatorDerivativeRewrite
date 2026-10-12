import Foundation.GaussianShiftedRepresentation

/-! Actual shifted predictable Hermite fields, identified by Gaussian L2 slices. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianShiftedIntegrand
open InfiniteGaussian GaussianTimeSpaceHermite GaussianShiftedHermite GaussianShiftedRepresentation
open GaussianBrownianQuadraticVariation GaussianPredictableFull GaussianTimeProductL2
open GaussianProductDerivative GaussianTimeHilbert

theorem incrementCore_continuous (s : ℝ≥0) (n : ℕ) : Continuous (fun t : ℝ≥0 => (incrementCore s t n : GaussianL2)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hc : Continuous (fun r : ℝ≥0 => ‖(incrementCore s r n : GaussianL2) - incrementCore s t n‖ ^ 2) := by
    simp_rw [norm_sub_sq_real, incrementCore_norm_sq, incrementCore_inner]
    simp only [if_true]
    fun_prop
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp (hc.continuousAt (x := t)).tendsto
  simp only [Function.comp_def, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] at hs
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hs

def stepValue (s : ℝ≥0) (n : ℕ) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) (x : ℝ) : GaussianL2 :=
  ∑ i : Fin m, (Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)).indicator
    (fun _ => (incrementCore s (τ i.castSucc) n : GaussianL2)) x

theorem stepValue_on_interval (s : ℝ≥0) (n : ℕ) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) (hτ : Monotone τ)
    (i : Fin m) (x : ℝ) (hx : x ∈ Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)) :
    stepValue s n τ x = incrementCore s (τ i.castSucc) n := by
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

theorem stepValue_outside (s : ℝ≥0) (n : ℕ) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) (hτ : Monotone τ)
    (x : ℝ) (hx : x ∉ Ioc (τ 0 : ℝ) (τ (Fin.last m) : ℝ)) : stepValue s n τ x = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply indicator_of_notMem
  intro hi
  exact hx ⟨lt_of_le_of_lt (hτ (Fin.zero_le _)) hi.1, hi.2.trans (hτ (Fin.le_last _))⟩

def horizonValue (s : ℝ≥0) (n : ℕ) (T : ℝ≥0) (x : ℝ) : GaussianL2 :=
  (Ioc 0 (T : ℝ)).indicator (fun r => (incrementCore s r.toNNReal n : GaussianL2)) x

theorem stepValue_tendsto (s : ℝ≥0) (n : ℕ) (T : ℝ≥0) (x : ℝ) :
    Tendsto (fun N => stepValue s n (uniformTime T N) x) atTop (𝓝 (horizonValue s n T x)) := by
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
    have hc := (incrementCore_continuous s n).continuousAt.tendsto.comp hnn
    rw [horizonValue, indicator_of_mem hx]
    convert hc using 1
    funext N
    exact stepValue_on_interval s n _ (uniformTime_monotone T N) (i N) x (hi N)
  · have hz (N : ℕ) : stepValue s n (uniformTime T N) x = 0 := by
      apply stepValue_outside s n _ (uniformTime_monotone T N) x
      simpa only [(uniformTime_endpoints T N).1, (uniformTime_endpoints T N).2,
        NNReal.coe_zero] using hx
    simp only [hz, horizonValue, indicator_of_notMem hx]
    exact tendsto_const_nhds


theorem shifted_indicator (s a b : ℝ≥0) (x : ℝ) (F : GaussianL2) :
    (Ioc (s + a : ℝ≥0) (s + b : ℝ≥0) : Set ℝ).indicator (fun _ => F) x =
      (Ioc (a : ℝ) b).indicator (fun _ => F) (x - s) := by
  have he : x ∈ (Ioc (s + a : ℝ≥0) (s + b : ℝ≥0) : Set ℝ) ↔ x - s ∈ Ioc (a : ℝ) b := by
    simp only [mem_Ioc, NNReal.coe_add]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  simp only [indicator, he]

theorem scalarCurry_stepSum (s : ℝ≥0) (n : ℕ) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) :
    scalarCurry (stepSum s n τ : TimeProbabilityL2) =ᵐ[volume] fun x => stepValue s n τ (x - s) := by
  rw [stepSum_coe, partitionL2, map_sum]
  simp only [scalarCurry_productTensor, NNReal.coe_add]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin m =>
    BochnerClosedOperator.tensor volume (intervalVector (s + τ i.castSucc) (s + τ i.succ))
      (incrementCore s (τ i.castSucc) n : GaussianL2)), ae_all_iff.mpr (fun i : Fin m =>
        BochnerClosedOperator.tensor_coeFn volume (intervalVector (s + τ i.castSucc) (s + τ i.succ))
          (incrementCore s (τ i.castSucc) n : GaussianL2)), ae_all_iff.mpr (fun i : Fin m =>
            intervalVector_coeFn (s + τ i.castSucc) (s + τ i.succ))] with x hs ht hi
  rw [hs]
  simp only [Finset.sum_apply, stepValue]
  apply Finset.sum_congr rfl
  intro i _
  rw [ht i, hi i, ← shifted_indicator s (τ i.castSucc) (τ i.succ) x]
  simp only [NNReal.coe_add]
  by_cases hx : x ∈ Ioc ((s : ℝ) + τ i.castSucc) ((s : ℝ) + τ i.succ) <;> simp [hx]

theorem hermiteIntegrand_slices (s : ℝ≥0) (n : ℕ) (T : ℝ≥0) :
    scalarCurry (hermiteIntegrand s n T : TimeProbabilityL2) =ᵐ[volume]
      fun x => horizonValue s n T (x - s) := by
  have ht := (scalarCurry.continuous.comp continuous_subtype_val).continuousAt.tendsto.comp
    (stepSum_tendsto s n T)
  obtain ⟨ns, hns, hn⟩ := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae
  have ha := ae_all_iff.mpr (fun N => scalarCurry_stepSum s n (uniformTime T N))
  filter_upwards [hn, ha] with x hn ha
  have hstep := (stepValue_tendsto s n T (x - s)).comp hns.tendsto_atTop
  change Tendsto (fun N => scalarCurry (stepSum s n (uniformTime T (ns N)) : TimeProbabilityL2) x)
    atTop (𝓝 (scalarCurry (hermiteIntegrand s n T : TimeProbabilityL2) x)) at hn
  simp only [ha] at hn
  exact tendsto_nhds_unique hn hstep

theorem shifted_hermite_stochastic_identity (s : ℝ≥0) (n : ℕ) (T : ℝ≥0) :
    (fun ω => value (n + 1) (GaussianTimeProcess.process (s + T) ω - GaussianTimeProcess.process s ω) T)
      =ᵐ[gaussianProduct] fun ω => (n + 1 : ℝ) * itoIntegral (hermiteIntegrand s n T) ω := by
  have he := hermite_representation s n T
  filter_upwards [incrementCore_coeFn s T (n + 1),
    Lp.coeFn_smul (n + 1 : ℝ) (itoIntegral (hermiteIntegrand s n T))] with ω hc hs
  have hi := congrArg (fun f : GaussianL2 => f ω) he
  rw [hc, hs] at hi
  exact hi

theorem hermiteIntegrand_integrable_sq (s : ℝ≥0) (n : ℕ) (T : ℝ≥0) :
    Integrable (fun z => ((hermiteIntegrand s n T : TimeProbabilityL2) z) ^ 2)
      (volume.prod gaussianProduct) := (Lp.memLp _).integrable_sq

theorem hermiteIntegrand_zero_duration (s : ℝ≥0) (n : ℕ) : hermiteIntegrand s n 0 = 0 := by
  have hn : (incrementCore s 0 (n + 1) : GaussianL2) = 0 := by
    have h := incrementCore_norm_sq s 0 (n + 1)
    simp only [NNReal.coe_zero, zero_pow (Nat.succ_ne_zero n), mul_zero] at h
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (incrementCore s 0 (n + 1) : GaussianL2)])
  simp [hermiteIntegrand, hn]

theorem integral_hermiteIntegrand_order_one (s T : ℝ≥0) :
    itoIntegral (hermiteIntegrand s 0 T) =
      GaussianTimeProcess.wienerL2 (s + T) - GaussianTimeProcess.wienerL2 s := by
  rw [integral_hermiteIntegrand]
  norm_num
  apply Lp.ext
  filter_upwards [incrementCore_coeFn s T 1,
    Lp.coeFn_sub (GaussianTimeProcess.wienerL2 (s + T)) (GaussianTimeProcess.wienerL2 s)] with ω hc hs
  simp only [value_one, GaussianTimeProcess.process] at hc
  exact hc.trans hs.symm

end OperatorDerivativeRewrite.Foundation.GaussianShiftedIntegrand
