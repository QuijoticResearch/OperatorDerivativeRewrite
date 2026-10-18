import Foundation.IBMQuadraticSpatialCalculus
import Foundation.IBMQuarticSecondGeometry

/-! A genuine Gaussian-L² second spatial primitive of the quartic
second-source correction, including the finite origin layer. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.IBMQuarticSecondPrimitive
open InfiniteGaussian IBMContinuousScenery IBMMollifier IBMGaussianSteinMoments
open IBMQuarticSecondChaos IBMQuadraticSpatialCalculus IBMQuarticSecondGeometry
open GaussianTimeSpaceHermite IBMVarianceClockGeometry

theorem adjoint_embedding (u : CoefficientSpace) :
    firstChaosEmbedding.toContinuousLinearMap.adjoint (firstChaosEmbedding u) = u := by
  have he := congrArg (fun L : CoefficientSpace →L[ℝ] CoefficientSpace => L u)
    firstChaosEmbedding.adjoint_comp_self
  exact he

theorem adjoint_scenery (n : ℕ) (r : ℝ) (i : Fin 3) :
    firstChaosEmbedding.toContinuousLinearMap.adjoint
      (wholeLineScenery (IBMJointMollifierGaussian.derivativeKernel n i) r) =
        tripleCoefficient n r i := by
  rw [← IBMOriginalBoundaryResidual.triple_embedding, adjoint_embedding]

theorem coefficient_zero_hasDerivAt (n : ℕ) (r : ℝ) :
    HasDerivAt (fun x => tripleCoefficient n x 0) (tripleCoefficient n r 1) r := by
  have he := firstChaosEmbedding.toContinuousLinearMap.adjoint.hasFDerivAt.comp_hasDerivAt r
    (wholeLineScenery_hasDerivAt (kernel_compactSupport n)
      ((kernel_smooth n).of_le (by norm_num)) r)
  have hz (x : ℝ) : firstChaosEmbedding.toContinuousLinearMap.adjoint
      (wholeLineScenery (kernel n) x) = tripleCoefficient n x 0 := by
    simpa [IBMJointMollifierGaussian.derivativeKernel] using adjoint_scenery n x 0
  have ho : firstChaosEmbedding.toContinuousLinearMap.adjoint
      (wholeLineScenery (deriv (kernel n)) r) = tripleCoefficient n r 1 := by
    simpa [IBMJointMollifierGaussian.derivativeKernel] using adjoint_scenery n r 1
  change HasDerivAt (fun x => firstChaosEmbedding.toContinuousLinearMap.adjoint
    (wholeLineScenery (kernel n) x)) (firstChaosEmbedding.toContinuousLinearMap.adjoint
      (wholeLineScenery (deriv (kernel n)) r)) r at he
  simpa only [hz, ho] using he

theorem coefficient_one_hasDerivAt (n : ℕ) (r : ℝ) :
    HasDerivAt (fun x => tripleCoefficient n x 1) (tripleCoefficient n r 2) r := by
  have hd : ContDiff ℝ 1 (deriv (kernel n)) :=
    (contDiff_succ_iff_deriv.mp ((kernel_smooth n).of_le (by norm_num) :
      ContDiff ℝ 2 (kernel n))).2.2
  have he := firstChaosEmbedding.toContinuousLinearMap.adjoint.hasFDerivAt.comp_hasDerivAt r
    (wholeLineScenery_hasDerivAt (kernel_compactSupport n).deriv hd r)
  have ho (x : ℝ) : firstChaosEmbedding.toContinuousLinearMap.adjoint
      (wholeLineScenery (deriv (kernel n)) x) = tripleCoefficient n x 1 := by
    simpa [IBMJointMollifierGaussian.derivativeKernel] using adjoint_scenery n x 1
  have ht : firstChaosEmbedding.toContinuousLinearMap.adjoint
      (wholeLineScenery (deriv (deriv (kernel n))) r) = tripleCoefficient n r 2 := by
    simpa [IBMJointMollifierGaussian.derivativeKernel] using adjoint_scenery n r 2
  change HasDerivAt (fun x => firstChaosEmbedding.toContinuousLinearMap.adjoint
    (wholeLineScenery (deriv (kernel n)) x)) (firstChaosEmbedding.toContinuousLinearMap.adjoint
      (wholeLineScenery (deriv (deriv (kernel n))) r)) r at he
  simpa only [ho, ht] using he

def primitive (n : ℕ) (r : ℝ) : GaussianL2 :=
  (1/4 : ℝ) • (variance n r • (wick (tripleCoefficient n r 0) 2 : GaussianL2))

def slope (n : ℕ) (r : ℝ) : GaussianL2 :=
  (1/4 : ℝ) • (deriv (variance n) r • (wick (tripleCoefficient n r 0) 2 : GaussianL2) +
    variance n r • ((2 : ℝ) • cross (tripleCoefficient n r 0) (tripleCoefficient n r 1)))

theorem primitive_hasDerivAt (n : ℕ) (r : ℝ) :
    HasDerivAt (primitive n) (slope n r) r := by
  have hc := ((variance_smooth n).differentiable (by norm_num) r).hasDerivAt
  have hw := wickTwo_hasDerivAt (coefficient_zero_hasDerivAt n r)
  have he := (hc.smul hw).const_smul (1/4 : ℝ)
  convert he using 1
  · rfl
  · unfold slope
    module

theorem slope_hasDerivAt (n : ℕ) (r : ℝ) :
    HasDerivAt (slope n) (GaussianNumberSectors.projection 2 (spatialQuartic n r)) r := by
  have hc := ((variance_smooth n).differentiable (by norm_num) r).hasDerivAt
  have hc' := (((RealSteklovApprox.deriv_contDiff_one _ (variance_smooth n)).differentiable
    (by norm_num)) r).hasDerivAt
  have hw := wickTwo_hasDerivAt (coefficient_zero_hasDerivAt n r)
  have hx := cross_hasDerivAt (coefficient_zero_hasDerivAt n r) (coefficient_one_hasDerivAt n r)
  have he := ((hc'.smul hw).add (hc.smul (hx.const_smul (2 : ℝ)))).const_smul (1/4 : ℝ)
  rw [variance_second, cross_self] at he
  simp only [Pi.smul_apply] at he
  rw [spatialQuartic_projection_two]
  convert he using 1
  · rfl
  · module

/-- Literal Bochner-L² second derivative identity; no weak-limit or spatial
white-noise-coordinate identification is inferred. -/
theorem primitive_second_deriv (n : ℕ) (r : ℝ) :
    deriv (deriv (primitive n)) r = GaussianNumberSectors.projection 2 (spatialQuartic n r) := by
  have he : deriv (primitive n) = slope n := by
    funext x
    exact (primitive_hasDerivAt n x).deriv
  rw [he]
  exact (slope_hasDerivAt n r).deriv

end OperatorDerivativeRewrite.Foundation.IBMQuarticSecondPrimitive
