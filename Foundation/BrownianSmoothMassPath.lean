import Foundation.BrownianTanakaResidual

/-! Actual continuous increasing paths for the smooth curvature drifts.
These approximants do not assume a limiting local-time path. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianSmoothMassPath
open InfiniteGaussian IBMConstructedSources SmoothAbsoluteApproximation RealSteklovApprox

theorem curvature_continuous {e : ℝ} (he : 0 < e) : Continuous (curvature e) := by
  unfold curvature
  exact continuous_const.div ((radius_smooth he 2).continuous.pow 3)
    (fun x => pow_ne_zero 3 (ne_of_gt (radius_pos he x)))

def rate (e : ℝ) (ω : SampleSpace) (t : ℝ) : ℝ := curvature e (clockPath ω t.toNNReal)

theorem rate_continuous {e : ℝ} (he : 0 < e) (ω : SampleSpace) : Continuous (rate e ω) :=
  (curvature_continuous he).comp ((clockPath ω).continuous.comp continuous_real_toNNReal)

theorem rate_joint {e : ℝ} (he : 0 < e) :
    Measurable (fun z : ℝ × SampleSpace => rate e z.2 z.1) :=
  (curvature_continuous he).measurable.comp BrownianClockWeightedEnergy.sigma_measurable

def primitive (n : ℕ) (ω : SampleSpace) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ s in 0..t, rate (width n) ω s

theorem primitive_hasDerivAt (n : ℕ) (ω : SampleSpace) (t : ℝ) :
    HasDerivAt (primitive n ω) ((1 / 2 : ℝ) * rate (width n) ω t) t := by
  have hc := rate_continuous (width_pos n) ω
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_mul (1 / 2 : ℝ)

theorem primitive_continuous (n : ℕ) (ω : SampleSpace) : Continuous (primitive n ω) :=
  continuous_iff_continuousAt.mpr (fun t => (primitive_hasDerivAt n ω t).continuousAt)

theorem primitive_monotone (n : ℕ) (ω : SampleSpace) : Monotone (primitive n ω) := by
  intro s t hst
  have hc := rate_continuous (width_pos n) ω
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := (volume : Measure ℝ))
    (hc.intervalIntegrable 0 s) (hc.intervalIntegrable s t)
  have hp : 0 ≤ ∫ r in s..t, rate (width n) ω r :=
    intervalIntegral.integral_nonneg_of_forall hst (fun r => curvature_nonneg (width_pos n) _)
  unfold primitive
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [← hi]
  linarith

def path (n : ℕ) (ω : SampleSpace) : C(ℝ≥0, ℝ) :=
  ⟨fun t => primitive n ω t, (primitive_continuous n ω).comp NNReal.continuous_coe⟩

theorem path_zero (n : ℕ) (ω : SampleSpace) : path n ω 0 = 0 := by
  simp [path, primitive]

theorem path_monotone (n : ℕ) (ω : SampleSpace) : Monotone (path n ω) :=
  fun _ _ h => primitive_monotone n ω h

theorem path_nonneg (n : ℕ) (ω : SampleSpace) (t : ℝ≥0) : 0 ≤ path n ω t := by
  rw [← path_zero n ω]
  exact path_monotone n ω (show (0 : ℝ≥0) ≤ t from t.property)

theorem path_coordinate_measurable (n : ℕ) (T : ℝ≥0) :
    Measurable (fun ω => path n ω T) := by
  have hm : StronglyMeasurable (fun z : SampleSpace × ℝ => rate (width n) z.1 z.2) :=
    ((rate_joint (width_pos n)).comp measurable_swap).stronglyMeasurable
  have hi := hm.integral_prod_right' (ν := volume.restrict (Ioc 0 (T : ℝ)))
  change Measurable (fun ω => (1 / 2 : ℝ) * ∫ s in 0..(T : ℝ), rate (width n) ω s)
  simp only [intervalIntegral.integral_of_le T.coe_nonneg]
  exact hi.measurable.const_mul (1 / 2 : ℝ)

theorem path_measurable (n : ℕ) : Measurable (path n) :=
  ContinuousMap.measurable_iff_eval.mpr (path_coordinate_measurable n)

theorem path_joint (n : ℕ) :
    Measurable (fun z : ℝ≥0 × SampleSpace => path n z.2 z.1) :=
  measurable_uncurry_of_continuous_of_measurable (fun ω => (path n ω).continuous)
    (path_coordinate_measurable n)

end OperatorDerivativeRewrite.Foundation.BrownianSmoothMassPath
