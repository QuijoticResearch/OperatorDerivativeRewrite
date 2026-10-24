import Foundation.IBMSpatialNativeApproximation

/-! The sharp fourth-moment bound for the ACTUAL continuous-time spatial
integral, obtained from genuine native sums and Fatou's lemma. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialIntegralFourth
open InfiniteGaussian GaussianTimeHilbert IBMSpatialNativeFourth IBMSpatialNativeApproximation
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable

def grid (T : ℝ≥0) (N j : ℕ) : ℝ≥0 := T * (min j (N+1)) / (N+1 : ℕ)

theorem grid_monotone (T : ℝ≥0) (N : ℕ) : Monotone (grid T N) := by
  intro i j hij
  unfold grid
  gcongr

theorem grid_zero (T : ℝ≥0) (N : ℕ) : grid T N 0 = 0 := by simp [grid]

theorem grid_end (T : ℝ≥0) (N : ℕ) : grid T N (N+1) = T := by simp [grid]

theorem grid_step (T : ℝ≥0) (N j : ℕ) (hj : j < N+1) :
    (grid T N (j+1) : ℝ)-grid T N j = (T : ℝ)/(N+1) := by
  simp only [grid, min_eq_left (Nat.succ_le_of_lt hj), min_eq_left (Nat.le_of_lt hj),
    NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast, Nat.cast_add, Nat.cast_one,
    Nat.cast_succ, NNReal.coe_add, NNReal.coe_one]
  ring

theorem uniform_tendsto (r : ℕ) (T : ℝ≥0) :
    Tendsto (fun N => IBMSpatialPredictableSteps.integral T
      (nativeInput r T (grid T N) (N+1))) atTop
        (𝓝 (IBMSpatialPointClockEnergy.integralValue r T)) := by
  apply integral_tendsto r T (fun N => N+1) (grid T) (grid_monotone T)
    (grid_zero T) (grid_end T) (fun N => (T : ℝ)/(N+1))
  · exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  · intro N j hj
    exact (grid_step T N j hj).le

theorem integral_fourth (r : ℕ) (T : ℝ≥0) :
    Integrable (fun Y => ‖IBMSpatialPointClockEnergy.integralValue r T Y‖^4) gaussianProduct ∧
      (∫ Y, ‖IBMSpatialPointClockEnergy.integralValue r T Y‖^4 ∂gaussianProduct) ≤
        3*(T : ℝ)^2*‖IBMPhysicalWhiteNoiseObstruction.profile r‖^4 := by
  let U (N : ℕ) := IBMSpatialPredictableSteps.integral T (nativeInput r T (grid T N) (N+1))
  let V := IBMSpatialPointClockEnergy.integralValue r T
  let C := 3*(T : ℝ)^2*‖IBMPhysicalWhiteNoiseObstruction.profile r‖^4
  have hU4 (N : ℕ) : MemLp (U N) 4 gaussianProduct :=
    native_integral_memLp_four r T (grid T N) (grid_monotone T N) (N+1)
      (grid_end T N).le
  have hB (N : ℕ) : (∫ Y, ‖U N Y‖^4 ∂gaussianProduct) ≤ C := by
    simpa only [grid_end, grid_zero, NNReal.coe_zero, sub_zero] using
      native_integral_fourth r T (grid T N) (grid_monotone T N) (N+1) (grid_end T N).le
  obtain ⟨ns, _hns, ha⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (uniform_tendsto r T)).exists_seq_tendsto_ae
  let f (i : ℕ) (Y : SampleSpace) := ENNReal.ofReal (‖U (ns i) Y‖^4)
  have hm (i : ℕ) : AEMeasurable (f i) gaussianProduct :=
    ((Lp.aestronglyMeasurable (U (ns i))).norm.pow 4).aemeasurable.ennreal_ofReal
  have ht : ∀ᵐ Y ∂gaussianProduct,
      Tendsto (fun i => f i Y) atTop (𝓝 (ENNReal.ofReal (‖V Y‖^4))) := by
    filter_upwards [ha] with Y hy
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hy.norm.pow 4)
  have hb (i : ℕ) : (∫⁻ Y, f i Y ∂gaussianProduct) ≤ ENNReal.ofReal C := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hU4 (ns i)).integrable_norm_pow'
      (Filter.Eventually.of_forall (fun Y => pow_nonneg (norm_nonneg _) 4))]
    exact ENNReal.ofReal_le_ofReal (hB (ns i))
  have hf : (∫⁻ Y, ENNReal.ofReal (‖V Y‖^4) ∂gaussianProduct) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ Y, liminf (fun i => f i Y) atTop ∂gaussianProduct :=
        lintegral_congr_ae (ht.mono (fun Y hy => hy.liminf_eq.symm))
      _ ≤ liminf (fun i => ∫⁻ Y, f i Y ∂gaussianProduct) atTop := lintegral_liminf_le' hm
      _ ≤ ENNReal.ofReal C := liminf_le_of_frequently_le' (Filter.Eventually.of_forall hb).frequently
  have hi : Integrable (fun Y => ‖V Y‖^4) gaussianProduct :=
    (lintegral_ofReal_ne_top_iff_integrable
      ((Lp.aestronglyMeasurable V).norm.pow 4)
      (Filter.Eventually.of_forall (fun Y => pow_nonneg (norm_nonneg _) 4))).mp
        (ne_of_lt (hf.trans_lt ENNReal.ofReal_lt_top))
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun Y => pow_nonneg (norm_nonneg _) 4))] at hf
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ C)).mp hf

theorem integral_memLp_four (r : ℕ) (T : ℝ≥0) :
    MemLp (IBMSpatialPointClockEnergy.integralValue r T) 4 gaussianProduct := by
  apply (integrable_norm_rpow_iff (Lp.aestronglyMeasurable _)
    (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num)).mp
  simpa using (integral_fourth r T).1

end OperatorDerivativeRewrite.Foundation.IBMSpatialIntegralFourth
