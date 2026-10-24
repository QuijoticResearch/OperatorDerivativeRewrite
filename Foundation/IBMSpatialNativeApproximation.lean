import Foundation.IBMSpatialNativeFourth

/-! Native spatial time-L2 approximation of the independently constructed
signed mollifier clock field. The jump at zero is handled on actual paths. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialNativeApproximation
open InfiniteGaussian GaussianTimeProcess GaussianTimeHilbert IBMSpatialNativeFourth
open IBMConstructedSources BrownianClockWeightedEnergy
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable

theorem spatial_continuousAt (r : ℕ) (x : ℝ) (hx : x ≠ 0) :
    ContinuousAt (IBMSpatialPointClockEnergy.spatial r) x := by
  have hs : ContinuousAt BrownianSignIntegral.signum x := by
    rcases lt_or_gt_of_ne hx with hn | hp
    · have he : BrownianSignIntegral.signum =ᶠ[𝓝 x] fun _ => (-1 : ℝ) := by
        filter_upwards [gt_mem_nhds hn] with y hy
        simp [BrownianSignIntegral.signum, hy, not_lt_of_gt hy]
      exact continuousAt_const.congr_of_eventuallyEq he
    · have he : BrownianSignIntegral.signum =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
        filter_upwards [lt_mem_nhds hp] with y hy
        simp [BrownianSignIntegral.signum, hy]
      exact continuousAt_const.congr_of_eventuallyEq he
  exact hs.smul ((IBMClockOccupationConvolution.profileClass_continuous r).continuousAt.comp
    continuous_abs.continuousAt)

def step (r : ℕ) (τ : ℕ → ℝ≥0) (n : ℕ) (z : ℝ × SampleSpace) : TimeHilbert :=
  ∑ j ∈ Finset.range n, (Ioc (τ j : ℝ) (τ (j+1) : ℝ)).indicator
    (fun _ => IBMSpatialPointClockEnergy.spatial r (process (τ j) z.2)) z.1

theorem step_on_cell (r : ℕ) (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (n j : ℕ)
    (hj : j < n) (z : ℝ × SampleSpace) (hz : z.1 ∈ Ioc (τ j : ℝ) (τ (j+1) : ℝ)) :
    step r τ n z = IBMSpatialPointClockEnergy.spatial r (process (τ j) z.2) := by
  rw [step, Finset.sum_eq_single j, indicator_of_mem hz]
  · intro i _ hij
    apply indicator_of_notMem
    intro hi
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hle : (τ (i+1) : ℝ) ≤ τ j := hτ (Nat.succ_le_of_lt hlt)
      linarith [hz.1, hi.2]
    · have hle : (τ (j+1) : ℝ) ≤ τ i := hτ (Nat.succ_le_of_lt hgt)
      linarith [hi.1, hz.2]
  · simp [hj]

private theorem cell_exists (T : ℝ≥0) (τ : ℕ → ℝ≥0) (n : ℕ)
    (hstart : τ 0 = 0) (hend : τ n = T) (z : ℝ × SampleSpace)
    (hz : z ∈ PredictableRealL2.horizon T) :
    ∃ j, j < n ∧ z.1 ∈ Ioc (τ j : ℝ) (τ (j+1) : ℝ) := by
  obtain ⟨i, hi⟩ := GaussianRefiningPartitions.covers
    (fun i : Fin (n+1) => τ i.val) z.1
    (by simpa only [Fin.val_zero, Fin.val_last, hstart, hend, NNReal.coe_zero] using hz.1)
  exact ⟨i.val, i.isLt, hi⟩

theorem step_bound (r : ℕ) (T : ℝ≥0) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (n : ℕ) (hstart : τ 0 = 0) (hend : τ n = T) (z : ℝ × SampleSpace)
    (hz : z ∈ PredictableRealL2.horizon T) :
    ‖step r τ n z‖ ≤ ‖IBMPhysicalWhiteNoiseObstruction.profile r‖ := by
  obtain ⟨j, hj, hi⟩ := cell_exists T τ n hstart hend z hz
  rw [step_on_cell r τ hτ n j hj z hi]
  exact IBMSpatialPointClockEnergy.spatial_bound r _

theorem step_tendsto_ae (r : ℕ) (T : ℝ≥0) (m : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0)
    (hτ : ∀ N, Monotone (τ N)) (hstart : ∀ N, τ N 0 = 0) (hend : ∀ N, τ N (m N) = T)
    (ε : ℕ → ℝ) (hlim : Tendsto ε atTop (𝓝 0))
    (hmesh : ∀ N j, j < m N → (τ N (j+1) : ℝ)-τ N j ≤ ε N) :
    ∀ᵐ z ∂PredictableRealL2.horizonMeasure T gaussianProduct,
      Tendsto (fun N => step r (τ N) (m N) z) atTop
        (𝓝 (IBMSpatialPointClockEnergy.raw r z)) := by
  have hc := ae_all_iff.mpr (fun N : ℕ => ae_all_iff.mpr (fun j : ℕ =>
    ae_restrict_of_ae (s := PredictableRealL2.horizon T)
      ((Measure.quasiMeasurePreserving_snd
        (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae_eq_comp
          (clockPath_coordinate_ae (τ N j)))))
  filter_upwards [hc, sigma_nonzero T,
    ae_restrict_mem (PredictableRealL2.horizon_measurable T)] with z hc hn hz
  have hc (N j : ℕ) : clockPath z.2 (τ N j) = process (τ N j) z.2 := hc N j
  choose i hi using fun N => cell_exists T (τ N) (m N) (hstart N) (hend N) z hz
  have hb (N : ℕ) : ‖(τ N (i N) : ℝ)-z.1‖ ≤ ε N := by
    rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (hi N).2.1.le)]
    linarith [(hi N).2.2, hmesh N (i N) (hi N).1]
  have ht := tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun N => norm_nonneg _) hb hlim)
  have hnn := continuous_real_toNNReal.continuousAt.tendsto.comp ht
  simp only [Function.comp_def, Real.toNNReal_coe] at hnn
  have hp := (clockPath z.2).continuous.continuousAt.tendsto.comp hnn
  have hs := (spatial_continuousAt r (sigma z) hn).tendsto.comp hp
  have he : (fun N => step r (τ N) (m N) z) =
      (fun N => IBMSpatialPointClockEnergy.spatial r (clockPath z.2 (τ N (i N)))) := by
    funext N
    rw [step_on_cell r (τ N) (hτ N) (m N) (i N) (hi N).1 z (hi N).2, ← hc N (i N)]
  rw [he]
  simpa only [Function.comp_def, IBMSpatialPointClockEnergy.raw] using hs

theorem input_tendsto (r : ℕ) (T : ℝ≥0) (m : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0)
    (hτ : ∀ N, Monotone (τ N)) (hstart : ∀ N, τ N 0 = 0) (hend : ∀ N, τ N (m N) = T)
    (ε : ℕ → ℝ) (hlim : Tendsto ε atTop (𝓝 0))
    (hmesh : ∀ N j, j < m N → (τ N (j+1) : ℝ)-τ N j ≤ ε N) :
    Tendsto (fun N => (nativeInput r T (τ N) (m N)).val) atTop
      (𝓝 (IBMSpatialPointClockEnergy.input r T).val) := by
  let U (N : ℕ) := (nativeInput r T (τ N) (m N)).val
  let V := (IBMSpatialPointClockEnergy.input r T).val
  let κ := ‖IBMPhysicalWhiteNoiseObstruction.profile r‖
  have hV := IBMSpatialPointClockEnergy.input_ae r T
  have hU (N : ℕ) : U N =ᵐ[PredictableRealL2.horizonMeasure T gaussianProduct]
      step r (τ N) (m N) := nativeInput_ae r T (τ N) (m N)
  have hi := tendsto_integral_of_dominated_convergence (fun _ => 4*κ^2)
    (F := fun N z => ‖U N z-V z‖^2) (f := fun _ => (0 : ℝ))
    (fun N => ((Lp.aestronglyMeasurable (U N)).sub (Lp.aestronglyMeasurable V)).norm.pow 2)
    (integrable_const _) (fun N => ?_) ?_
  · have he (N : ℕ) : ‖U N-V‖^2 = ∫ z, ‖U N z-V z‖^2
        ∂PredictableRealL2.horizonMeasure T gaussianProduct := by
      rw [BochnerL2Dominated.norm_sq_integral]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (U N) V] with z hz
      simp only [hz, Pi.sub_apply]
    simp only [integral_zero] at hi
    have hn : Tendsto (fun N => ‖U N-V‖^2) atTop (𝓝 0) := by simpa only [he] using hi
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hn
    simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hs
    exact tendsto_iff_norm_sub_tendsto_zero.mpr hs
  · filter_upwards [hU N, hV,
      ae_restrict_mem (PredictableRealL2.horizon_measurable T)] with z hu hv hz
    rw [hu, hv, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb := step_bound r T (τ N) (hτ N) (m N) (hstart N) (hend N) z hz
    have hc := IBMSpatialPointClockEnergy.spatial_bound r (sigma z)
    have hd := norm_sub_le (step r (τ N) (m N) z) (IBMSpatialPointClockEnergy.raw r z)
    change _ ≤ 4*‖IBMPhysicalWhiteNoiseObstruction.profile r‖^2
    change ‖IBMSpatialPointClockEnergy.raw r z‖ ≤ _ at hc
    nlinarith [norm_nonneg (step r (τ N) (m N) z-IBMSpatialPointClockEnergy.raw r z)]
  · filter_upwards [ae_all_iff.mpr hU, hV,
      step_tendsto_ae r T m τ hτ hstart hend ε hlim hmesh] with z hu hv ht
    change V z = IBMSpatialPointClockEnergy.raw r z at hv
    simpa only [hu, hv, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      ((ht.sub (tendsto_const_nhds (x := IBMSpatialPointClockEnergy.raw r z))).norm.pow 2)

theorem integral_tendsto (r : ℕ) (T : ℝ≥0) (m : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0)
    (hτ : ∀ N, Monotone (τ N)) (hstart : ∀ N, τ N 0 = 0) (hend : ∀ N, τ N (m N) = T)
    (ε : ℕ → ℝ) (hlim : Tendsto ε atTop (𝓝 0))
    (hmesh : ∀ N j, j < m N → (τ N (j+1) : ℝ)-τ N j ≤ ε N) :
    Tendsto (fun N => IBMSpatialPredictableSteps.integral T (nativeInput r T (τ N) (m N)))
      atTop (𝓝 (IBMSpatialPointClockEnergy.integralValue r T)) := by
  have hu : Tendsto (fun N => nativeInput r T (τ N) (m N)) atTop
      (𝓝 (IBMSpatialPointClockEnergy.input r T)) :=
    tendsto_subtype_rng.mpr (input_tendsto r T m τ hτ hstart hend ε hlim hmesh)
  have hc := ((GaussianParameterizedIto.realIntegral (volume : Measure ℝ) T).continuous.comp
    (IBMSpatialPredictableSteps.trim T).continuous).continuousAt.tendsto.comp hu
  exact hc

end OperatorDerivativeRewrite.Foundation.IBMSpatialNativeApproximation
