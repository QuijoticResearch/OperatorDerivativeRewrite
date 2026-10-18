import Foundation.IBMQuarticSecondPrimitive

/-! Strong Gaussian-L² convergence of the actual quartic primitive and
its deterministic spatial test integrals. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMQuarticPrimitiveLimit
open InfiniteGaussian IBMQuarticSecondPrimitive IBMQuadraticSpatialCalculus
open IBMQuarticSecondChaos IBMQuarticSecondGeometry GaussianTimeSpaceHermite
open IBMContinuousScenery IBMVarianceClockGeometry IBMGaussianSteinMoments

def baseCoefficient (r : ℝ) : CoefficientSpace :=
  firstChaosEmbedding.toContinuousLinearMap.adjoint (sourceScenery r)

theorem coefficient_tendsto (r : ℝ) :
    Tendsto (fun n => tripleCoefficient n r 0) atTop (𝓝 (baseCoefficient r)) := by
  have he := firstChaosEmbedding.toContinuousLinearMap.adjoint.continuous.tendsto
    (sourceScenery r) |>.comp (concreteMollifier_tendsto r)
  have hz (n : ℕ) : firstChaosEmbedding.toContinuousLinearMap.adjoint
      (wholeLineScenery (IBMMollifier.kernel n) r) = tripleCoefficient n r 0 := by
    simpa [IBMJointMollifierGaussian.derivativeKernel] using adjoint_scenery n r 0
  change Tendsto (fun n => firstChaosEmbedding.toContinuousLinearMap.adjoint
    (wholeLineScenery (IBMMollifier.kernel n) r)) atTop _ at he
  simpa only [hz, baseCoefficient] using he

def primitiveLimit (r : ℝ) : GaussianL2 :=
  (1/4 : ℝ) • (|r| • (wick (baseCoefficient r) 2 : GaussianL2))

theorem primitive_tendsto (r : ℝ) :
    Tendsto (fun n => primitive n r) atTop (𝓝 (primitiveLimit r)) := by
  have hw := (GaussianWickContinuity.wick_continuous 2).tendsto _ |>.comp (coefficient_tendsto r)
  have he := ((variance_tendsto r).smul hw).const_smul (1/4 : ℝ)
  simpa only [Function.comp_def, primitive, primitiveLimit] using he

theorem primitive_continuous (n : ℕ) : Continuous (primitive n) :=
  continuous_iff_continuousAt.mpr fun r => (primitive_hasDerivAt n r).continuousAt

theorem primitiveLimit_continuous : Continuous primitiveLimit := by
  have hc : Continuous baseCoefficient :=
    firstChaosEmbedding.toContinuousLinearMap.adjoint.continuous.comp sourceScenery_continuous
  change Continuous (fun r : ℝ => (1/4 : ℝ) • (|r| • (wick (baseCoefficient r) 2 : GaussianL2)))
  have ha : Continuous (fun r : ℝ => |r|) := continuous_abs
  have hw : Continuous (fun r => (wick (baseCoefficient r) 2 : GaussianL2)) :=
    (GaussianWickContinuity.wick_continuous 2).comp hc
  exact (ha.smul hw).const_smul (1/4 : ℝ)

theorem primitive_bound (n : ℕ) (r : ℝ) : ‖primitive n r‖ ≤ (|r|+2)^2 := by
  have hw : ‖(wick (tripleCoefficient n r 0) 2 : GaussianL2)‖ ≤
      2*‖tripleCoefficient n r 0‖^2 := by
    rw [← cross_self]
    simpa only [pow_two, mul_assoc] using cross_norm_le (tripleCoefficient n r 0) (tripleCoefficient n r 0)
  have hc : 0 ≤ variance n r := sq_nonneg _
  have hb : variance n r ≤ |r|+2 :=
    (le_abs_self _).trans (variance_bound n r)
  rw [primitive, norm_smul, norm_smul]
  norm_num [Real.norm_eq_abs, abs_of_nonneg hc]
  have he := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ (1/4 : ℝ)*variance n r)
  rw [coefficient_variance] at he
  nlinarith [sq_nonneg (|r|+2-variance n r)]

theorem primitiveLimit_bound (r : ℝ) : ‖primitiveLimit r‖ ≤ (|r|+2)^2 :=
  le_of_tendsto (primitive_tendsto r).norm (Eventually.of_forall fun n => primitive_bound n r)

/-- Strong Gaussian-L² convergence of every finite-interval continuous
spatial test integral of the actual primitive. -/
theorem test_integral_tendsto (ψ : ℝ → ℝ) (hψ : Continuous ψ) (a b : ℝ) :
    Tendsto (fun n => ∫ r in Set.Icc a b, ψ r • primitive n r) atTop
      (𝓝 (∫ r in Set.Icc a b, ψ r • primitiveLimit r)) := by
  apply tendsto_integral_of_dominated_convergence (fun r => ‖ψ r‖*(|r|+2)^2)
  · intro n
    exact (hψ.smul (primitive_continuous n)).aestronglyMeasurable
  · exact ((hψ.norm).mul ((continuous_abs.add continuous_const).pow 2)).integrableOn_Icc
  · intro n
    exact Eventually.of_forall fun r => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (primitive_bound n r) (norm_nonneg _)
  · exact Eventually.of_forall fun r => (primitive_tendsto r).const_smul (ψ r)

end OperatorDerivativeRewrite.Foundation.IBMQuarticPrimitiveLimit
