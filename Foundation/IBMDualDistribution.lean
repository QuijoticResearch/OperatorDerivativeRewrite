import Foundation.IBMDualAssembly

/-! Sectionwise distribution identity for the two-channel H⁻¹ assembly. -/
noncomputable section
open MeasureTheory TemperedDistribution
open scoped BesselPotentialSpace SchwartzMap LineDeriv

namespace OperatorDerivativeRewrite.Foundation.IBMDualDistribution
open InfiniteGaussian IBMDualAssembly IBMNegativeSobolev
  IBMNegativeSobolevBounded IBMNegativeSobolevRandom
  IBMDeltaBoundary IBMRandomBoundary

/-- Almost every clock sample has the specified interior-plus-boundary
H⁻¹ section. -/
theorem assembly_apply_ae (u : InteriorInput) (a : BoundaryInput) :
    ∀ᵐ w ∂gaussianProduct,
      (dualAssemblyCLM (u, a)) w =
        l2Derivative (u w) + (a w) • deltaZeroHminusOne := by
  filter_upwards [Lp.coeFn_add (randomDerivativeCLM u) (randomBoundaryCLM a),
    randomDerivative_apply_ae u, randomBoundary_apply_ae a] with w hsum hder hboundary
  rw [dualAssemblyCLM_apply, hsum]
  change (randomDerivativeCLM u) w + (randomBoundaryCLM a) w = _
  rw [hder, hboundary, l2DerivativeCLM_apply]

/-- The assembled H⁻¹ field is exactly a distributional spatial derivative
plus a scalar multiple of the origin Dirac mass, for almost every clock sample. -/
theorem assembly_toDistr_ae (u : InteriorInput) (a : BoundaryInput) :
    ∀ᵐ w ∂gaussianProduct,
      ((dualAssemblyCLM (u, a)) w).toDistr =
        LineDeriv.lineDerivOp (1 : ℝ) ((u w : Lp ℂ 2 (volume : Measure ℝ)) : 𝓢'(ℝ, ℂ)) +
          (a w) • (deltaZeroHminusOne.toDistr) := by
  filter_upwards [assembly_apply_ae u a] with w hw
  rw [hw, BesselPotentialSpace.toDistr_add, BesselPotentialSpace.toDistr_smul,
    l2Derivative_toDistr]

end OperatorDerivativeRewrite.Foundation.IBMDualDistribution

