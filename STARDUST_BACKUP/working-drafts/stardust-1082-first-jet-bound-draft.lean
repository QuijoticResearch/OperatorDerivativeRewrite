import Foundation.IBMSchwartzPhysicalPrimitive
import Mathlib.Analysis.InnerProductSpace.Adjoint
noncomputable section
open OperatorDerivativeRewrite.Foundation
open InfiniteGaussian IBMCorrectionStein IBMShiftedJetMoments
open IBMSchwartzSourceDerivative IBMSchwartzPhysicalPrimitive
example (g : SchwartzMap ℝ ℝ) (a : ℝ) (j : ℕ) (u : CoefficientSpace) :
    |M g a u (j+1) 0| * ‖u‖ ≤ SchwartzMap.seminorm ℝ 0 0 (jet g j) := by
  have hc (f : GaussianL2) :
      ‖firstChaosEmbedding.toContinuousLinearMap.adjoint f‖ ≤ ‖f‖ := by
    calc
      _ ≤ ‖firstChaosEmbedding.toContinuousLinearMap.adjoint‖*‖f‖ :=
        firstChaosEmbedding.toContinuousLinearMap.adjoint.le_opNorm f
      _ = ‖firstChaosEmbedding.toContinuousLinearMap‖*‖f‖ := by
        rw [ContinuousLinearMap.adjoint.norm_map]
      _ ≤ 1*‖f‖ := mul_le_mul_of_nonneg_right
        firstChaosEmbedding.norm_toContinuousLinearMap_le (norm_nonneg f)
      _ = ‖f‖ := one_mul _
  have h := (hc (observable g a j u)).trans (observable_bound g a j u)
  rw [observable_adjoint, norm_smul, Real.norm_eq_abs] at h
  exact h
