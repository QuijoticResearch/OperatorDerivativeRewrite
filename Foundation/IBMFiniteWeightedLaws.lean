import Foundation.IBMFiniteAverageCore
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-! Finite positive weighted observation laws for the actual IBM intrinsic-core
annihilator. Signed weights are separated before characteristic uniqueness. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMFiniteWeightedLaws
open InfiniteGaussian IBMTimeAveragedObservable IBMFiniteAverageCore
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local irreducible] IBMConstructedSources.ibmValue IBMConstructedSources.clockPath

theorem weighted_integral_difference {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (H v : X → ℝ) (hm : Measurable H) (hi : Integrable H μ)
    (hv : AEStronglyMeasurable v μ) (C : ℝ) (hb : ∀ᵐ x ∂μ, ‖v x‖ ≤ C) :
    (∫ x, v x ∂μ.withDensity (fun x => ENNReal.ofReal (H x))) -
      (∫ x, v x ∂μ.withDensity (fun x => ENNReal.ofReal (-H x))) = ∫ x, H x * v x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top) v,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top) v]
  simp only [ENNReal.toReal_ofReal', smul_eq_mul]
  rw [← integral_sub (hi.pos_part.mul_bdd hv hb) (hi.neg_part.mul_bdd hv hb)]
  congr 1
  funext x
  have he : max (H x) 0 - max (-H x) 0 = H x := by
    rcases le_total 0 (H x) with hh | hh
    · rw [max_eq_left hh, max_eq_right (neg_nonpos.mpr hh)]
      ring
    · rw [max_eq_right hh, max_eq_left (neg_nonneg.mpr hh)]
      ring
  rw [← sub_mul, he]

theorem weighted_integral_balance {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (H v : X → ℝ) (hm : Measurable H) (hi : Integrable H μ)
    (hv : AEStronglyMeasurable v μ) (C : ℝ) (hb : ∀ᵐ x ∂μ, ‖v x‖ ≤ C)
    (hz : (∫ x, H x * v x ∂μ) = 0) :
    (∫ x, v x ∂μ.withDensity (fun x => ENNReal.ofReal (H x))) =
      ∫ x, v x ∂μ.withDensity (fun x => ENNReal.ofReal (-H x)) := by
  apply sub_eq_zero.mp
  rw [weighted_integral_difference μ H v hm hi hv C hb, hz]

theorem finite_measure_eq_of_cos_sin {I : Type*} [Fintype I]
    (μ ν : Measure (EuclideanSpace ℝ I)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hc : ∀ w, (∫ x, Real.cos (inner ℝ x w) ∂μ) = ∫ x, Real.cos (inner ℝ x w) ∂ν)
    (hs : ∀ w, (∫ x, Real.sin (inner ℝ x w) ∂μ) = ∫ x, Real.sin (inner ℝ x w) ∂ν) :
    μ = ν := by
  apply Measure.ext_of_charFun
  funext w
  have hi (ρ : Measure (EuclideanSpace ℝ I)) [IsFiniteMeasure ρ] :
      Integrable (fun x => Complex.exp ((inner ℝ x w : ℂ) * Complex.I)) ρ := by
    exact BoundedContinuousFunction.integrable ρ (BoundedContinuousFunction.innerProbChar w)
  apply Complex.ext
  · change RCLike.re (charFun μ w) = RCLike.re (charFun ν w)
    rw [charFun_apply, charFun_apply, ← integral_re (hi μ), ← integral_re (hi ν)]
    simpa [Complex.exp_re] using hc w
  · change RCLike.im (charFun μ w) = RCLike.im (charFun ν w)
    rw [charFun_apply, charFun_apply, ← integral_im (hi μ), ← integral_im (hi ν)]
    simpa [Complex.exp_im] using hs w

def pointObservation {I : Type*} [Fintype I] (t : I → ℝ) (ω : IBMSourceLaws.JointSample) :
    EuclideanSpace ℝ I := WithLp.toLp 2 (fun i => IBMConstructedSources.ibmValue (t i).toNNReal ω)

theorem pointObservation_measurable {I : Type*} [Fintype I] (t : I → ℝ) :
    Measurable (pointObservation t) := by
  apply (PiLp.continuous_toLp (p := 2) (fun _ : I => ℝ)).measurable.comp
  have hm (i : I) : Measurable (fun ω : IBMSourceLaws.JointSample =>
      IBMConstructedSources.ibmValue (t i).toNNReal ω) :=
    IBMConstructedSources.ibmValue_jointly_measurable.comp (measurable_const.prodMk measurable_id)
  exact Measurable.of_eval hm

/-- Equality of actual FINITE POSITIVE weighted point-observation laws.
No positivity of the original annihilator or Gaussian IBM law is assumed. -/
theorem annihilator_finite_weighted_laws {I : Type*} [Fintype I]
    (H : JointL2) (hH : H ∈ intrinsicCoreᗮ) (t : I → ℝ) (ht : ∀ i, 0 < t i) :
    (IBMSourceLaws.jointMeasure.withDensity (fun ω => ENNReal.ofReal (H ω))).map (pointObservation t) =
      (IBMSourceLaws.jointMeasure.withDensity (fun ω => ENNReal.ofReal (-H ω))).map (pointObservation t) := by
  have hi : Integrable H IBMSourceLaws.jointMeasure := (Lp.memLp H).integrable (by simp)
  let μ := IBMSourceLaws.jointMeasure.withDensity (fun ω => ENNReal.ofReal (H ω))
  let ν := IBMSourceLaws.jointMeasure.withDensity (fun ω => ENNReal.ofReal (-H ω))
  letI : IsFiniteMeasure μ := isFiniteMeasure_withDensity_ofReal hi.hasFiniteIntegral
  letI : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hi.neg.hasFiniteIntegral
  apply finite_measure_eq_of_cos_sin
  · intro w
    rw [integral_map (pointObservation_measurable t).aemeasurable (by fun_prop),
      integral_map (pointObservation_measurable t).aemeasurable (by fun_prop)]
    apply weighted_integral_balance _ H _ (Lp.stronglyMeasurable H).measurable hi
      (((Real.continuous_cos.comp (continuous_id.inner continuous_const)).measurable.comp
        (pointObservation_measurable t)).aestronglyMeasurable) 1
      (ae_of_all _ (fun ω => by
        change |Real.cos (inner ℝ (pointObservation t ω) w)| ≤ 1
        exact Real.abs_cos_le_one _))
    convert (annihilator_point_fourier_moments H hH (fun i => w i) t ht).1 using 1
    simp [Function.comp_def, pointObservation, PiLp.inner_apply, mul_comm]
  · intro w
    rw [integral_map (pointObservation_measurable t).aemeasurable (by fun_prop),
      integral_map (pointObservation_measurable t).aemeasurable (by fun_prop)]
    apply weighted_integral_balance _ H _ (Lp.stronglyMeasurable H).measurable hi
      (((Real.continuous_sin.comp (continuous_id.inner continuous_const)).measurable.comp
        (pointObservation_measurable t)).aestronglyMeasurable) 1
      (ae_of_all _ (fun ω => by
        change |Real.sin (inner ℝ (pointObservation t ω) w)| ≤ 1
        exact Real.abs_sin_le_one _))
    convert (annihilator_point_fourier_moments H hH (fun i => w i) t ht).2 using 1
    simp [Function.comp_def, pointObservation, PiLp.inner_apply, mul_comm]

/-- Actual set integrals of the annihilator vanish on every finite positive-time
IBM observation event. This is stronger than just vanishing Fourier moments. -/
theorem annihilator_finite_event {I : Type*} [Fintype I]
    (H : JointL2) (hH : H ∈ intrinsicCoreᗮ) (t : I → ℝ) (ht : ∀ i, 0 < t i)
    (S : Set (EuclideanSpace ℝ I)) (hS : MeasurableSet S) :
    (∫ ω in pointObservation t ⁻¹' S, H ω ∂IBMSourceLaws.jointMeasure) = 0 := by
  have hi : Integrable H IBMSourceLaws.jointMeasure := (Lp.memLp H).integrable (by simp)
  let v : IBMSourceLaws.JointSample → ℝ := fun ω => S.indicator (fun _ => (1 : ℝ)) (pointObservation t ω)
  have htest : Measurable (S.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hS
  have hv : Measurable v := htest.comp (pointObservation_measurable t)
  have hb : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ‖v ω‖ ≤ 1 := ae_of_all _ fun ω => by
    by_cases h : pointObservation t ω ∈ S <;> simp [v, h]
  have heq : (∫ ω, v ω ∂IBMSourceLaws.jointMeasure.withDensity (fun ω => ENNReal.ofReal (H ω))) =
      ∫ ω, v ω ∂IBMSourceLaws.jointMeasure.withDensity (fun ω => ENNReal.ofReal (-H ω)) := by
    have ha := congrArg (fun ρ : Measure (EuclideanSpace ℝ I) =>
      ∫ y, S.indicator (fun _ => (1 : ℝ)) y ∂ρ)
      (annihilator_finite_weighted_laws H hH t ht)
    rw [integral_map (pointObservation_measurable t).aemeasurable htest.aestronglyMeasurable,
      integral_map (pointObservation_measurable t).aemeasurable htest.aestronglyMeasurable] at ha
    exact ha
  have hz : (∫ ω, H ω * v ω ∂IBMSourceLaws.jointMeasure) = 0 := by
    rw [← weighted_integral_difference _ H v (Lp.stronglyMeasurable H).measurable hi
      hv.aestronglyMeasurable 1 hb, heq, sub_self]
  rw [← integral_indicator (hS.preimage (pointObservation_measurable t))]
  convert hz using 1
  congr 1
  funext ω
  by_cases h : pointObservation t ω ∈ S <;> simp [v, h]

end OperatorDerivativeRewrite.Foundation.IBMFiniteWeightedLaws
