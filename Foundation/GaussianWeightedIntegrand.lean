import Foundation.GaussianWeightedHermite

/-! Identification of the past-weighted Hermite representer with its actual running coefficient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianWeightedIntegrand
open InfiniteGaussian GaussianTimeSpaceHermite GaussianWeightedHermite
open GaussianBrownianQuadraticVariation GaussianPredictableFull GaussianTimeProductL2
open GaussianProductDerivative GaussianTimeHilbert

def stepValue (s : ℝ≥0) (a : (Iic s → ℝ) → ℝ) (ha : Measurable a)
    (hA : MemLp (GaussianPredictableStep.pastCoefficient GaussianTimeProcess.process s a) 2 gaussianProduct) (n : ℕ) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) (x : ℝ) : GaussianL2 :=
  ∑ i : Fin m, (Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)).indicator
    (fun _ => (coefficient s a ha hA (τ i.castSucc) n : GaussianL2)) x

theorem stepValue_on_interval (s : ℝ≥0) (a : (Iic s → ℝ) → ℝ) (ha : Measurable a)
    (hA : MemLp (GaussianPredictableStep.pastCoefficient GaussianTimeProcess.process s a) 2 gaussianProduct) (n : ℕ) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) (hτ : Monotone τ)
    (i : Fin m) (x : ℝ) (hx : x ∈ Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)) :
    stepValue s a ha hA n τ x = coefficient s a ha hA (τ i.castSucc) n := by
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

theorem stepValue_outside (s : ℝ≥0) (a : (Iic s → ℝ) → ℝ) (ha : Measurable a)
    (hA : MemLp (GaussianPredictableStep.pastCoefficient GaussianTimeProcess.process s a) 2 gaussianProduct) (n : ℕ) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) (hτ : Monotone τ)
    (x : ℝ) (hx : x ∉ Ioc (τ 0 : ℝ) (τ (Fin.last m) : ℝ)) : stepValue s a ha hA n τ x = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply indicator_of_notMem
  intro hi
  exact hx ⟨lt_of_le_of_lt (hτ (Fin.zero_le _)) hi.1, hi.2.trans (hτ (Fin.le_last _))⟩

def horizonValue (s : ℝ≥0) (a : (Iic s → ℝ) → ℝ) (ha : Measurable a)
    (hA : MemLp (GaussianPredictableStep.pastCoefficient GaussianTimeProcess.process s a) 2 gaussianProduct) (n : ℕ) (T : ℝ≥0) (x : ℝ) : GaussianL2 :=
  (Ioc 0 (T : ℝ)).indicator (fun r => (coefficient s a ha hA r.toNNReal n : GaussianL2)) x

theorem stepValue_tendsto (s : ℝ≥0) (a : (Iic s → ℝ) → ℝ) (ha : Measurable a)
    (hA : MemLp (GaussianPredictableStep.pastCoefficient GaussianTimeProcess.process s a) 2 gaussianProduct) (n : ℕ) (T : ℝ≥0) (x : ℝ) :
    Tendsto (fun N => stepValue s a ha hA n (uniformTime T N) x) atTop (𝓝 (horizonValue s a ha hA n T x)) := by
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
    have hc := (coefficient_continuous s a ha hA n).continuousAt.tendsto.comp hnn
    rw [horizonValue, indicator_of_mem hx]
    convert hc using 1
    funext N
    exact stepValue_on_interval s a ha hA n _ (uniformTime_monotone T N) (i N) x (hi N)
  · have hz (N : ℕ) : stepValue s a ha hA n (uniformTime T N) x = 0 := by
      apply stepValue_outside s a ha hA n _ (uniformTime_monotone T N) x
      simpa only [(uniformTime_endpoints T N).1, (uniformTime_endpoints T N).2,
        NNReal.coe_zero] using hx
    simp only [hz, horizonValue, indicator_of_notMem hx]
    exact tendsto_const_nhds


theorem scalarCurry_stepSum (s : ℝ≥0) (a : (Iic s → ℝ) → ℝ) (ha : Measurable a)
    (hA : MemLp (GaussianPredictableStep.pastCoefficient GaussianTimeProcess.process s a) 2 gaussianProduct) (n : ℕ) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) :
    scalarCurry (stepSum s a ha hA n τ : TimeProbabilityL2) =ᵐ[volume] fun x => stepValue s a ha hA n τ (x - s) := by
  rw [stepSum_coe, partitionL2, map_sum]
  simp only [scalarCurry_productTensor, NNReal.coe_add]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin m =>
    BochnerClosedOperator.tensor volume (intervalVector (s + τ i.castSucc) (s + τ i.succ))
      (coefficient s a ha hA (τ i.castSucc) n : GaussianL2)), ae_all_iff.mpr (fun i : Fin m =>
        BochnerClosedOperator.tensor_coeFn volume (intervalVector (s + τ i.castSucc) (s + τ i.succ))
          (coefficient s a ha hA (τ i.castSucc) n : GaussianL2)), ae_all_iff.mpr (fun i : Fin m =>
            intervalVector_coeFn (s + τ i.castSucc) (s + τ i.succ))] with x hs ht hi
  rw [hs]
  simp only [Finset.sum_apply, stepValue]
  apply Finset.sum_congr rfl
  intro i _
  rw [ht i, hi i, ← GaussianShiftedIntegrand.shifted_indicator s (τ i.castSucc) (τ i.succ) x]
  simp only [NNReal.coe_add]
  by_cases hx : x ∈ Ioc ((s : ℝ) + τ i.castSucc) ((s : ℝ) + τ i.succ) <;> simp [hx]

theorem hermiteIntegrand_slices (s : ℝ≥0) (a : (Iic s → ℝ) → ℝ) (ha : Measurable a)
    (hA : MemLp (GaussianPredictableStep.pastCoefficient GaussianTimeProcess.process s a) 2 gaussianProduct) (n : ℕ) (T : ℝ≥0) :
    scalarCurry (hermiteIntegrand s a ha hA n T : TimeProbabilityL2) =ᵐ[volume]
      fun x => horizonValue s a ha hA n T (x - s) := by
  have ht := (scalarCurry.continuous.comp continuous_subtype_val).continuousAt.tendsto.comp
    (stepSum_tendsto s a ha hA n T)
  obtain ⟨ns, hns, hn⟩ := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae
  have hsteps := ae_all_iff.mpr (fun N => scalarCurry_stepSum s a ha hA n (uniformTime T N))
  filter_upwards [hn, hsteps] with x hn hsteps
  have hstep := (stepValue_tendsto s a ha hA n T (x - s)).comp hns.tendsto_atTop
  change Tendsto (fun N => scalarCurry (stepSum s a ha hA n (uniformTime T (ns N)) : TimeProbabilityL2) x)
    atTop (𝓝 (scalarCurry (hermiteIntegrand s a ha hA n T : TimeProbabilityL2) x)) at hn
  simp only [hsteps] at hn
  exact tendsto_nhds_unique hn hstep


theorem weighted_hermite_stochastic_identity (s : ℝ≥0) (a : (Iic s → ℝ) → ℝ)
    (ha : Measurable a)
    (hA : MemLp (GaussianPredictableStep.pastCoefficient GaussianTimeProcess.process s a) 2 gaussianProduct)
    (n : ℕ) (T : ℝ≥0) :
    (fun ω => GaussianPredictableStep.pastCoefficient GaussianTimeProcess.process s a ω *
      value (n + 1) (GaussianTimeProcess.process (s + T) ω - GaussianTimeProcess.process s ω) T)
      =ᵐ[gaussianProduct] fun ω => (n + 1 : ℝ) * itoIntegral (hermiteIntegrand s a ha hA n T) ω := by
  have he := hermite_representation s a ha hA n T
  filter_upwards [coefficient_coeFn s a ha hA T (n + 1),
    Lp.coeFn_smul (n + 1 : ℝ) (itoIntegral (hermiteIntegrand s a ha hA n T))] with ω hc hs
  have hi := congrArg (fun f : GaussianL2 => f ω) he
  rw [hc, hs] at hi
  exact hi

theorem hermiteIntegrand_integrable_sq (s : ℝ≥0) (a : (Iic s → ℝ) → ℝ) (ha : Measurable a)
    (hA : MemLp (GaussianPredictableStep.pastCoefficient GaussianTimeProcess.process s a) 2 gaussianProduct)
    (n : ℕ) (T : ℝ≥0) :
    Integrable (fun z => ((hermiteIntegrand s a ha hA n T : TimeProbabilityL2) z) ^ 2)
      (volume.prod gaussianProduct) := (Lp.memLp _).integrable_sq

/-- The measurable-past parametrization introduces no finite-coordinate or boundedness restriction. -/
theorem exists_unique_weighted_representation (s T : ℝ≥0) (n : ℕ) (G : SampleSpace → ℝ)
    (hG : Measurable[GaussianTimeProcess.naturalFiltration s] G) (hG2 : MemLp G 2 gaussianProduct) :
    ∃! U : fullPredictable,
      (fun ω => G ω * value (n + 1)
        (GaussianTimeProcess.process (s + T) ω - GaussianTimeProcess.process s ω) T)
        =ᵐ[gaussianProduct] fun ω => (n + 1 : ℝ) * itoIntegral U ω := by
  obtain ⟨a, ha, rfl⟩ := (GaussianPredictableStep.measurable_natural_iff_exists_pastCoefficient
    (fun t => (GaussianTimeProcess.process_stronglyMeasurable t).measurable) s G).mp hG
  refine ⟨hermiteIntegrand s a ha hG2 n T, weighted_hermite_stochastic_identity s a ha hG2 n T, ?_⟩
  intro U hU
  apply itoIntegral.injective
  apply Lp.ext
  filter_upwards [hU, weighted_hermite_stochastic_identity s a ha hG2 n T] with ω hu hv
  exact mul_left_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0) (hu.symm.trans hv)

end OperatorDerivativeRewrite.Foundation.GaussianWeightedIntegrand
