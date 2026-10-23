import Foundation.IBMWeightedSimpsonIntrinsic
import Foundation.IBMRawCosineSimpsonL2

/-! The actual nonlinear path time average int sin(Zt) dt is the strong L2
limit of UNCLIPPED ramp-weighted cosine Simpson stochastic sums.
No strong joint derivative-domain membership is claimed for this average. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSineAverageSimpson
open IBMSourceLaws IBMConstructedSources IBMTimeAveragedObservable
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
attribute [local irreducible] ibmValue clockPath sceneryPath

def weight (T : ℝ≥0) (t : ℝ) : ℝ := (T : ℝ)-t

theorem weight_smooth (T : ℝ≥0) : ContDiff ℝ 1 (weight T) := by
  unfold weight
  fun_prop

theorem weight_deriv (T : ℝ≥0) (t : ℝ) : deriv (weight T) t = -1 := by
  change deriv (fun x : ℝ => (T : ℝ)-x) t = -1
  exact ((hasDerivAt_id t).const_sub (T : ℝ)).deriv

def value (T : ℝ≥0) (n : ℕ) : IntrinsicSpace :=
  IBMWeightedSimpsonIntrinsic.intrinsicValue (weight T) Real.sin (weight_smooth T)
    (by fun_prop) 1 1 Real.abs_sin_le_one IBMRawCosineSimpsonL2.sine_fifth_bound T n

def average (T : ℝ≥0) : IntrinsicSpace :=
  IBMWeightedSimpsonIntrinsic.intrinsicTarget (weight T) Real.sin (weight_smooth T)
    (by fun_prop) 1 1 Real.abs_sin_le_one IBMRawCosineSimpsonL2.sine_fifth_bound T

theorem value_actual_ae (T : ℝ≥0) (n : ℕ) :
    (value T n : JointL2) =ᵐ[jointMeasure]
      IBMTimeWeightedSimpson.weighted (fun t => (T : ℝ)-t) Real.cos T n := by
  change (IBMWeightedSimpsonIntrinsic.intrinsicValue (weight T) Real.sin (weight_smooth T)
    (by fun_prop) 1 1 Real.abs_sin_le_one IBMRawCosineSimpsonL2.sine_fifth_bound T n : JointL2)
      =ᵐ[jointMeasure] IBMTimeWeightedSimpson.weighted (weight T) Real.cos T n
  simpa only [Real.deriv_sin] using
    IBMWeightedSimpsonIntrinsic.intrinsicValue_actual_ae (weight T) Real.sin (weight_smooth T)
      (by fun_prop) 1 1 Real.abs_sin_le_one IBMRawCosineSimpsonL2.sine_fifth_bound T n

/-- The limit is a time average of the nonlinear process, not a nonlinear
function of the old linear IBM time average. Zero-time equality is only AE. -/
theorem average_actual_ae (T : ℝ≥0) :
    (average T : JointL2) =ᵐ[jointMeasure]
      (fun ω => ∫ t in (0 : ℝ)..(T : ℝ), Real.sin (ibmValue (Real.toNNReal t) ω)) := by
  have h := IBMWeightedSimpsonIntrinsic.intrinsicTarget_actual_ae (weight T) Real.sin
    (weight_smooth T) (by fun_prop) 1 1 Real.abs_sin_le_one
      IBMRawCosineSimpsonL2.sine_fifth_bound T
  filter_upwards [h, IBMSimpsonGraphDual.sine_zero_ae] with ω he hz
  change (average T : JointL2) ω = _ at he ⊢
  rw [he,hz]
  simp only [weight_deriv, weight, sub_self, zero_mul, mul_zero, sub_zero,
    zero_sub, neg_one_mul, intervalIntegral.integral_neg, neg_neg]

theorem value_tendsto (T : ℝ≥0) : Tendsto (value T) atTop (𝓝 (average T)) :=
  IBMWeightedSimpsonIntrinsic.intrinsicValue_tendsto (weight T) Real.sin (weight_smooth T)
    (by fun_prop) 1 1 Real.abs_sin_le_one IBMRawCosineSimpsonL2.sine_fifth_bound T

theorem weakDerivative_tendsto (T : ℝ≥0) :
    Tendsto (fun n => IBMIntrinsicGraphDual.weakDerivative (value T n)) atTop
      (𝓝 (IBMIntrinsicGraphDual.weakDerivative (average T))) :=
  (IBMIntrinsicGraphDual.weakDerivative.continuous.tendsto _).comp (value_tendsto T)

end OperatorDerivativeRewrite.Foundation.IBMSineAverageSimpson
