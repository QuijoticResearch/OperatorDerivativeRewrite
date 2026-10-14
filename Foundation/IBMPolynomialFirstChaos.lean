import Foundation.IBMSceneryCubicProjection

/-! Source Stein coefficients for arbitrary polynomial observations of the
actual mollified scenery triple. Covariance degeneracy is permitted. -/
noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false

namespace OperatorDerivativeRewrite.Foundation.IBMPolynomialFirstChaos
open InfiniteGaussian GaussianNumberSectors IBMCubicFirstChaos IBMGaussianSteinMoments

theorem adjoint_polynomial {ι : Type*} [Fintype ι]
    (h : ι → CoefficientSpace) (p : MvPolynomial ι ℝ) :
    firstChaosEmbedding.toContinuousLinearMap.adjoint (isonormalCylinderL2 h p) =
      ∑ i, (∫ ω, isonormalCylinderL2 h (MvPolynomial.pderiv i p) ω ∂gaussianProduct) • h i := by
  rw [show isonormalCylinderL2 h p = (cylinderCore h p : GaussianL2) from rfl,
    adjoint_eq_mean_derivative, cylinder_gradient_expansion]
  have hi (i : ι) : Integrable (fun ω =>
      (scalarTensor (h i) (cylinderCore h (MvPolynomial.pderiv i p))) ω) gaussianProduct :=
    (Lp.memLp _).integrable (by norm_num)
  calc
    _ = ∫ ω, ∑ i, (scalarTensor (h i) (cylinderCore h (MvPolynomial.pderiv i p))) ω
        ∂gaussianProduct := by
          apply integral_congr_ae
          filter_upwards [Lp.coeFn_finsetSum Finset.univ
            (fun i => scalarTensor (h i) (cylinderCore h (MvPolynomial.pderiv i p)))] with ω hw
          change (∑ i, scalarTensor (h i) (cylinderCore h (MvPolynomial.pderiv i p))) ω = _
          rw [hw]
          simp only [Finset.sum_apply]
    _ = ∑ i, ∫ ω, (scalarTensor (h i) (cylinderCore h (MvPolynomial.pderiv i p))) ω
        ∂gaussianProduct := integral_finset_sum _ (fun i _ => hi i)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_congr_ae (scalarTensor_coeFn (h i) (cylinderCore h (MvPolynomial.pderiv i p))),
        integral_smul_const]
      rfl

theorem projection_polynomial {ι : Type*} [Fintype ι]
    (h : ι → CoefficientSpace) (p : MvPolynomial ι ℝ) :
    GaussianPastFirstChaos.projection (isonormalCylinderL2 h p) =
      ∑ i, (∫ ω, isonormalCylinderL2 h (MvPolynomial.pderiv i p) ω ∂gaussianProduct) •
        firstChaosEmbedding (h i) := by
  change firstChaosEmbedding (firstChaosEmbedding.toContinuousLinearMap.adjoint _) = _
  rw [adjoint_polynomial, map_sum]
  simp only [map_smul]

/-- Every degree and every deterministic shift encoded in p is allowed;
no smooth nonpolynomial differentiation theorem is inferred. -/
theorem actual_scenery_polynomial_projection (n : ℕ) (x : ℝ) (p : MvPolynomial (Fin 3) ℝ) :
    GaussianPastFirstChaos.projection (isonormalCylinderL2 (tripleCoefficient n x) p) =
      ∑ i, (∫ ω, isonormalCylinderL2 (tripleCoefficient n x) (MvPolynomial.pderiv i p) ω
        ∂gaussianProduct) •
          IBMContinuousScenery.wholeLineScenery (IBMJointMollifierGaussian.derivativeKernel n i) x := by
  rw [projection_polynomial]
  congr 1
  funext i
  rw [show firstChaosEmbedding (tripleCoefficient n x i) =
      IBMContinuousScenery.wholeLineScenery (IBMJointMollifierGaussian.derivativeKernel n i) x from
    (IBMJointMollifierGaussian.wholeLineScenery_eq_sourceEmbedding _ _).symm]

end OperatorDerivativeRewrite.Foundation.IBMPolynomialFirstChaos
