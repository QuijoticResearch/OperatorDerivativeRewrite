import Foundation.GaussianQuadraticRepresentation
import Mathlib.Order.Interval.Set.Union

/-! Identification of the limiting integrand by its actual Bochner slices,
and the Brownian quadratic Ito formula for the existing predictable integral. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianQuadraticIto
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProcess GaussianTimeDivergence
open GaussianTimeProductL2 GaussianProductDerivative GaussianPredictableFull
open GaussianQuadraticRepresentation GaussianBrownianQuadraticVariation

def stepValue {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (x : ℝ) : GaussianL2 :=
  ∑ i : Fin n, (Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)).indicator
    (fun _ => wienerL2 (τ i.castSucc)) x

theorem stepValue_on_interval {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (i : Fin n) (x : ℝ) (hx : x ∈ Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)) :
    stepValue τ x = wienerL2 (τ i.castSucc) := by
  rw [stepValue, Finset.sum_eq_single i, indicator_of_mem hx]
  · intro j _ hji
    apply indicator_of_notMem
    intro hj
    rcases lt_or_gt_of_ne hji with hjlt | hjgt
    · have hle : (τ j.succ : ℝ) ≤ τ i.castSucc :=
        hτ (Fin.succ_le_castSucc_iff.mpr hjlt)
      linarith [hx.1, hj.2]
    · have hle : (τ i.succ : ℝ) ≤ τ j.castSucc :=
        hτ (Fin.succ_le_castSucc_iff.mpr hjgt)
      linarith [hj.1, hx.2]
  · simp

theorem stepValue_outside {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (x : ℝ) (hx : x ∉ Ioc (τ 0 : ℝ) (τ (Fin.last n) : ℝ)) : stepValue τ x = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply indicator_of_notMem
  intro hi
  apply hx
  exact ⟨lt_of_le_of_lt (hτ (Fin.zero_le _)) hi.1,
    hi.2.trans (hτ (Fin.le_last _))⟩

theorem uniformTime_covers (T : ℝ≥0) (n : ℕ) (x : ℝ) (hx : x ∈ Ioc 0 (T : ℝ)) :
    ∃ i : Fin (n + 1), x ∈ Ioc (uniformTime T n i.castSucc : ℝ)
      (uniformTime T n i.succ : ℝ) := by
  let a : ℕ → ℝ := fun k => (T : ℝ) * k / (n + 1)
  have h0 : a 0 = 0 := by simp [a]
  have hN : a (n + 1) = T := by simp only [a, Nat.cast_add, Nat.cast_one]; field_simp
  have hs := Ioc_subset_biUnion_Ioc (n + 1) a
  rw [h0, hN] at hs
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs hx)
  refine ⟨⟨i, Finset.mem_range.mp hi⟩, ?_⟩
  simpa only [uniformTime, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast,
    Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one,
    NNReal.coe_add, NNReal.coe_one, a] using hxi

def horizonValue (T : ℝ≥0) (x : ℝ) : GaussianL2 :=
  (Ioc 0 (T : ℝ)).indicator (fun s => wienerL2 s.toNNReal) x

theorem stepValue_tendsto (T : ℝ≥0) (x : ℝ) :
    Tendsto (fun n => stepValue (uniformTime T n) x) atTop (𝓝 (horizonValue T x)) := by
  by_cases hx : x ∈ Ioc 0 (T : ℝ)
  · have hx0 : 0 ≤ x := hx.1.le
    have hb (n : ℕ) : ‖stepValue (uniformTime T n) x - wienerL2 x.toNNReal‖ ^ 2 ≤
        (T : ℝ) / (n + 1) := by
      obtain ⟨i, hi⟩ := uniformTime_covers T n x hx
      rw [stepValue_on_interval _ (uniformTime_monotone T n) i x hi, norm_sub_rev]
      have hle : uniformTime T n i.castSucc ≤ x.toNNReal := by
        change (uniformTime T n i.castSucc : ℝ) ≤ (x.toNNReal : ℝ)
        rw [Real.coe_toNNReal _ hx0]
        exact hi.1.le
      rw [wienerL2_sub_norm_sq _ _ hle, Real.coe_toNNReal _ hx0]
      have hs := uniformTime_step T n i
      linarith [hi.2]
    have ht : Tendsto (fun n : ℕ => (T : ℝ) / (n + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have hz := squeeze_zero (fun n => sq_nonneg _) hb ht
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hz
    simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hs
    rw [horizonValue, indicator_of_mem hx]
    exact tendsto_iff_norm_sub_tendsto_zero.mpr hs
  · have hz (n : ℕ) : stepValue (uniformTime T n) x = 0 := by
      apply stepValue_outside _ (uniformTime_monotone T n) x
      simpa only [(uniformTime_endpoints T n).1, (uniformTime_endpoints T n).2,
        NNReal.coe_zero] using hx
    simp only [hz, horizonValue, indicator_of_notMem hx]
    exact tendsto_const_nhds

theorem scalarCurry_leftStepField {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) :
    scalarCurry (leftStepField τ : TimeProbabilityL2) =ᵐ[volume] stepValue τ := by
  have he : scalarCurry (leftStepField τ : TimeProbabilityL2) =
      ∑ i : Fin n, BochnerClosedOperator.tensor volume
        (intervalVector (τ i.castSucc) (τ i.succ)) (wienerL2 (τ i.castSucc)) := by
    simp only [leftStepField, Submodule.coe_sum]
    change scalarCurry (∑ i : Fin n, productTensor (intervalVector (τ i.castSucc) (τ i.succ))
      (pastCoefficient (fun _ : Fin 1 => τ i.castSucc) (MvPolynomial.X 0))) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [scalarCurry_productTensor]
    congr 1
    apply Lp.ext
    filter_upwards [pastCoefficient_coeFn (fun _ : Fin 1 => τ i.castSucc) (MvPolynomial.X 0)]
      with ω hp
    simpa only [MvPolynomial.eval_X, process] using hp
  rw [he]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin n =>
    BochnerClosedOperator.tensor volume (intervalVector (τ i.castSucc) (τ i.succ))
      (wienerL2 (τ i.castSucc))), ae_all_iff.mpr (fun i : Fin n =>
        BochnerClosedOperator.tensor_coeFn volume (intervalVector (τ i.castSucc) (τ i.succ))
          (wienerL2 (τ i.castSucc))), ae_all_iff.mpr (fun i : Fin n =>
            intervalVector_coeFn (τ i.castSucc) (τ i.succ))] with x hs ht hi
  rw [hs]
  simp only [Finset.sum_apply, stepValue]
  apply Finset.sum_congr rfl
  intro i _
  rw [ht i, hi i]
  by_cases hx : x ∈ Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ) <;> simp [hx]

/-- The constructed predictable integrand has the intended actual Gaussian L2
slice at almost every time; no path-continuity version was assumed. -/
theorem quadraticIntegrand_slices (T : ℝ≥0) :
    scalarCurry (quadraticIntegrand T : TimeProbabilityL2) =ᵐ[volume] horizonValue T := by
  have ht := (scalarCurry.continuous.comp continuous_subtype_val).continuousAt.tendsto.comp
    (leftStepField_tendsto T)
  obtain ⟨ns, hns, hn⟩ := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae
  have ha := ae_all_iff.mpr (fun n => scalarCurry_leftStepField (uniformTime T n))
  filter_upwards [hn, ha] with x hn ha
  have hstep := (stepValue_tendsto T x).comp hns.tendsto_atTop
  change Tendsto (fun n => scalarCurry (leftStepField (uniformTime T (ns n)) : TimeProbabilityL2) x)
    atTop (𝓝 (scalarCurry (quadraticIntegrand T : TimeProbabilityL2) x)) at hn
  simp only [ha] at hn
  exact tendsto_nhds_unique hn hstep

/-- Genuine quadratic Ito identity for the existing stochastic integral, with
its running Brownian integrand independently identified by quadraticIntegrand_slices. -/
theorem brownian_quadratic_ito (T : ℝ≥0) :
    (fun ω => (process T ω) ^ 2) =ᵐ[gaussianProduct]
      fun ω => 2 * itoIntegral (quadraticIntegrand T) ω + (T : ℝ) := by
  have he := integral_quadraticIntegrand T
  filter_upwards [terminalSquare_coeFn T,
    Lp.coeFn_smul (1 / 2 : ℝ) (terminalSquare T)] with ω hf hs
  have hi := congrArg (fun f : GaussianL2 => f ω) he
  rw [hs] at hi
  simp only [Pi.smul_apply, smul_eq_mul, hf] at hi
  linarith

end OperatorDerivativeRewrite.Foundation.GaussianQuadraticIto
