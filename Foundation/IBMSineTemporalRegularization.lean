import Foundation.IBMTimeWeightedIntrinsicCore
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Actual intrinsic-domain temporal difference quotients of the nonlinear
IBM sine average. Their values and scenery derivatives recover the point. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSineTemporalRegularization
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
open IBMActualSineDomainObstruction IBMTimeWeightedIntrinsicCore IBMClockOverlapEnergy
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe

def valuePrimitive (r : ℝ) : IntrinsicSpace := IBMSineAverageSimpson.average r.toNNReal

theorem valuePrimitive_integral (r : ℝ) (hr : 0 ≤ r) :
    valuePrimitive r = ∫ t in (0:ℝ)..r, sinePoint t.toNNReal := by
  rw [valuePrimitive,← actual_one]
  unfold IBMTimeWeightedSineValue.actual
  simp only [one_smul,window,Real.coe_toNNReal _ hr]
  exact (intervalIntegral.integral_of_le hr).symm

theorem valuePrimitive_hasDerivAt (T : ℝ≥0) (hT : 0 < T) :
    HasDerivAt valuePrimitive (sinePoint T) (T:ℝ) := by
  have hc := sinePoint_continuous.comp continuous_real_toNNReal
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable (0:ℝ) (T:ℝ))
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have h : HasDerivAt (fun r : ℝ => ∫ t in (0:ℝ)..r, sinePoint t.toNNReal)
      (sinePoint T) (T:ℝ) := by simpa only [Function.comp_def,Real.toNNReal_coe] using hd
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (show (0:ℝ) < T from hT)] with r hr
  exact valuePrimitive_integral r hr.le

def sourcePrimitive (r : ℝ) : FieldSpace := IBMSineAverageIntrinsicCalculus.gradient r.toNNReal 0

theorem sourcePrimitive_integral (r : ℝ) (hr : 0 ≤ r) :
    sourcePrimitive r = ∫ t in (0:ℝ)..r, sineSourceGradient t.toNNReal := by
  rw [sourcePrimitive,← IBMSineSourceIntegral.sourceIntegral_eq_gradient]
  unfold IBMSineSourceIntegral.sourceIntegral window
  rw [Real.coe_toNNReal _ hr]
  exact (intervalIntegral.integral_of_le hr).symm

theorem sourcePrimitive_hasDerivAt (T : ℝ≥0) (hT : 0 < T) :
    HasDerivAt sourcePrimitive (sineSourceGradient T) (T:ℝ) := by
  have hc := IBMSineAverageStrongJoint.sourceGradient_continuous
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable (0:ℝ) (T:ℝ))
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have h : HasDerivAt (fun r : ℝ => ∫ t in (0:ℝ)..r, sineSourceGradient t.toNNReal)
      (sineSourceGradient T) (T:ℝ) := by simpa only [Real.toNNReal_coe] using hd
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (show (0:ℝ) < T from hT)] with r hr
  exact sourcePrimitive_integral r hr.le

def regularized (T : ℝ≥0) (e : ℝ) : jointDerivative.domain :=
  e⁻¹ • (IBMSineAverageIntrinsicCalculus.domainAverage ((T:ℝ)+e).toNNReal -
    IBMSineAverageIntrinsicCalculus.domainAverage T)

theorem regularized_value (T : ℝ≥0) (e : ℝ) :
    (regularized T e : IntrinsicSpace) = e⁻¹ • (valuePrimitive ((T:ℝ)+e)-valuePrimitive T) := by
  simp only [regularized,valuePrimitive,Real.toNNReal_coe]
  rfl

theorem regularized_gradient (T : ℝ≥0) (e : ℝ) :
    jointDerivative (regularized T e) = e⁻¹ •
      (IBMSineAverageIntrinsicCalculus.gradient ((T:ℝ)+e).toNNReal -
        IBMSineAverageIntrinsicCalculus.gradient T) := by
  unfold regularized
  change jointDerivative.toFun (e⁻¹ •
    (IBMSineAverageIntrinsicCalculus.domainAverage ((T:ℝ)+e).toNNReal -
      IBMSineAverageIntrinsicCalculus.domainAverage T)) = _
  rw [map_smul,map_sub]
  rfl

theorem regularized_source (T : ℝ≥0) (e : ℝ) :
    jointDerivative (regularized T e) 0 = e⁻¹ •
      (sourcePrimitive ((T:ℝ)+e)-sourcePrimitive T) := by
  rw [regularized_gradient]
  simp only [sourcePrimitive,Real.toNNReal_coe]
  rfl

theorem parameter_tendsto {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (hne : ∀ n, e n ≠ 0) : Tendsto e atTop (𝓝[≠] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨he,Eventually.of_forall fun n => hne n⟩

attribute [local irreducible] regularized jointDerivative sinePoint sineSourceGradient

theorem value_tendsto (T : ℝ≥0) (hT : 0 < T) (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0)) (hne : ∀ n, e n ≠ 0) :
    Tendsto (fun n => (regularized T (e n) : IntrinsicSpace)) atTop (𝓝 (sinePoint T)) := by
  simpa only [regularized_value,Function.comp_def] using
    (valuePrimitive_hasDerivAt T hT).tendsto_slope_zero.comp (parameter_tendsto he hne)

theorem source_tendsto (T : ℝ≥0) (hT : 0 < T) (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0)) (hne : ∀ n, e n ≠ 0) :
    Tendsto (fun n => jointDerivative (regularized T (e n)) 0) atTop
      (𝓝 (sineSourceGradient T)) := by
  simpa only [regularized_source,Function.comp_def] using
    (sourcePrimitive_hasDerivAt T hT).tendsto_slope_zero.comp (parameter_tendsto he hne)

theorem regularized_actual_ae (T : ℝ≥0) (e : ℝ) :
    (regularized T e : JointL2) =ᵐ[IBMSourceLaws.jointMeasure] fun p => e⁻¹ *
      ((∫ t in (0:ℝ)..(((T:ℝ)+e).toNNReal:ℝ),
        Real.sin (IBMConstructedSources.ibmValue t.toNNReal p)) -
       (∫ t in (0:ℝ)..(T:ℝ), Real.sin (IBMConstructedSources.ibmValue t.toNNReal p))) := by
  have hv : (regularized T e : JointL2) = e⁻¹ •
      ((IBMSineAverageSimpson.average ((T:ℝ)+e).toNNReal : JointL2) -
        (IBMSineAverageSimpson.average T : JointL2)) := by unfold regularized; rfl
  rw [hv]
  filter_upwards [Lp.coeFn_smul e⁻¹
      ((IBMSineAverageSimpson.average ((T:ℝ)+e).toNNReal : JointL2) -
        (IBMSineAverageSimpson.average T : JointL2)),
    Lp.coeFn_sub (IBMSineAverageSimpson.average ((T:ℝ)+e).toNNReal : JointL2)
      (IBMSineAverageSimpson.average T : JointL2),
    IBMSineAverageSimpson.average_actual_ae ((T:ℝ)+e).toNNReal,
    IBMSineAverageSimpson.average_actual_ae T] with p hs hd ha hb
  rw [hs,Pi.smul_apply,hd,Pi.sub_apply,ha,hb]
  rfl

theorem clipped_increment_bound (T : ℝ≥0) (e : ℝ) :
    |(((T:ℝ)+e).toNNReal:ℝ)-(T:ℝ)| ≤ |e| := by
  by_cases hp : 0 ≤ (T:ℝ)+e
  · rw [Real.coe_toNNReal _ hp]
    simp only [add_sub_cancel_left,le_refl]
  · rw [Real.toNNReal_of_nonpos (le_of_not_ge hp),NNReal.coe_zero,zero_sub,abs_neg]
    have hnorm : |(T:ℝ)| = (T:ℝ) := abs_of_nonneg T.property
    rw [hnorm]
    have hn : e ≤ 0 := by linarith [T.property]
    rw [abs_of_nonpos hn]
    linarith

theorem actual_normalized_bound (T : ℝ≥0) (e : ℝ) (p : IBMSourceLaws.JointSample) :
    |e⁻¹ *
      ((∫ t in (0:ℝ)..(((T:ℝ)+e).toNNReal:ℝ),
        Real.sin (IBMConstructedSources.ibmValue t.toNNReal p)) -
       (∫ t in (0:ℝ)..(T:ℝ), Real.sin (IBMConstructedSources.ibmValue t.toNNReal p)))| ≤ 1 := by
  by_cases he : e = 0
  · simp only [he,inv_zero,zero_mul,abs_zero,zero_le_one]
  let f : ℝ → ℝ := fun t => Real.sin (IBMConstructedSources.ibmValue t.toNNReal p)
  have hc : Continuous f := Real.continuous_sin.comp
    ((IBMConstructedSources.ibmValue_continuous p).comp continuous_real_toNNReal)
  have ha := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable (0:ℝ) (T:ℝ))
    (hc.intervalIntegrable (T:ℝ) (((T:ℝ)+e).toNNReal:ℝ))
  have hb : |(∫ t in (0:ℝ)..(((T:ℝ)+e).toNNReal:ℝ), f t)-
      (∫ t in (0:ℝ)..(T:ℝ), f t)| ≤ |e| := by
    have hh : (∫ t in (0:ℝ)..(((T:ℝ)+e).toNNReal:ℝ), f t)-
        (∫ t in (0:ℝ)..(T:ℝ), f t) =
        ∫ t in (T:ℝ)..(((T:ℝ)+e).toNNReal:ℝ), f t := by linarith
    rw [hh]
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := f) (a := (T:ℝ)) (b := (((T:ℝ)+e).toNNReal:ℝ))
      (fun t _ => Real.abs_sin_le_one (IBMConstructedSources.ibmValue t.toNNReal p))
    have hi' : |∫ t in (T:ℝ)..(((T:ℝ)+e).toNNReal:ℝ), f t| ≤
        |(((T:ℝ)+e).toNNReal:ℝ)-(T:ℝ)| := by
      simpa only [Real.norm_eq_abs,one_mul] using hi
    exact hi'.trans (clipped_increment_bound T e)
  change |e⁻¹ * ((∫ t in (0:ℝ)..(((T:ℝ)+e).toNNReal:ℝ), f t)-
    (∫ t in (0:ℝ)..(T:ℝ), f t))| ≤ 1
  rw [abs_mul,abs_inv]
  exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (abs_nonneg e))).trans_eq
    (inv_mul_cancel₀ (abs_ne_zero.mpr he))

theorem regularized_bounded (T : ℝ≥0) (e : ℝ) :
    ∀ᵐ p ∂IBMSourceLaws.jointMeasure, |(regularized T e : JointL2) p| ≤ 1 :=
  (regularized_actual_ae T e).mono fun p hp => hp ▸ actual_normalized_bound T e p

end OperatorDerivativeRewrite.Foundation.IBMSineTemporalRegularization
