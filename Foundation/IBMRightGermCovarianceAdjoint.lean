import Foundation.IBMRightGermFullDeterministicIntegral
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The actual deterministic IBM integral's covariance adjoint and exact
range reconstruction. This does not identify a native Malliavin derivative. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRightGermCovarianceAdjoint
open IBMTimeAveragedObservable IBMIntrinsicRightGerm IBMRightGermEnergyMeasure
open IBMRightGermDeterministicIntegral IBMRightGermFullDeterministicIntegral
set_option backward.isDefEq.respectTransparency false

def covarianceAdjoint : JointL2 →L[ℝ] TimeL2 := integral.toContinuousLinearMap.adjoint

theorem duality (f : TimeL2) (F : JointL2) :
    inner ℝ f (covarianceAdjoint F) = inner ℝ (integral f) F :=
  integral.toContinuousLinearMap.adjoint_inner_right f F

theorem adjoint_integral (f : TimeL2) : covarianceAdjoint (integral f) = f := by
  apply ext_inner_left ℝ
  intro g
  rw [duality, integral_inner]

def reconstruction (F : JointL2) : JointL2 := integral (covarianceAdjoint F)

def residual (F : JointL2) : JointL2 := F - reconstruction F

theorem residual_orthogonal (F : JointL2) (f : TimeL2) :
    inner ℝ (integral f) (residual F) = 0 := by
  rw [residual, reconstruction, inner_sub_right, integral_inner, duality, sub_self]

theorem reconstruction_idempotent (F : JointL2) :
    reconstruction (reconstruction F) = reconstruction F := by
  simp only [reconstruction, adjoint_integral]

theorem energy_decomposition (F : JointL2) :
    ‖F‖ ^ 2 = ‖covarianceAdjoint F‖ ^ 2 + ‖residual F‖ ^ 2 := by
  have he : F = reconstruction F + residual F := by unfold residual; abel
  have hi : inner ℝ (reconstruction F) (residual F) = 0 :=
    residual_orthogonal F (covarianceAdjoint F)
  have hn : ‖F‖ ^ 2 = ‖reconstruction F‖ ^ 2 + ‖residual F‖ ^ 2 := by
    conv_lhs => rw [he, norm_add_sq_real, hi]
    ring
  simpa only [reconstruction, integral_norm] using hn

theorem adjoint_norm_le (F : JointL2) : ‖covarianceAdjoint F‖ ≤ ‖F‖ := by
  have he := energy_decomposition F
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (by nlinarith [sq_nonneg ‖residual F‖])

theorem reconstruction_iff_range (F : JointL2) :
    reconstruction F = F ↔ F ∈ integral.toLinearMap.range := by
  constructor
  · intro h
    exact ⟨covarianceAdjoint F, h⟩
  · rintro ⟨f, rfl⟩
    exact congrArg integral (adjoint_integral f)

theorem residual_zero_iff (F : JointL2) :
    residual F = 0 ↔ F ∈ integral.toLinearMap.range := by
  rw [residual, sub_eq_zero, eq_comm, reconstruction_iff_range]

theorem interval_duality (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ u in Ioc s t, covarianceAdjoint F u ∂energyMeasure) =
      ∫ ω, (rightValue t ω - rightValue s ω) * F ω ∂IBMSourceLaws.jointMeasure := by
  have he := duality (indicatorConstLp 2 measurableSet_Ioc
    (energyMeasure_Ioc_finite s t).ne (1 : ℝ)) F
  rw [L2.inner_indicatorConstLp_one measurableSet_Ioc
    (energyMeasure_Ioc_finite s t).ne, integral_interval hst, L2.inner_def] at he
  refine he.trans (integral_congr_ae ?_)
  filter_upwards [Lp.coeFn_sub (rightLimitClass t) (rightLimitClass s)] with ω hω
  rw [hω, Real.inner_apply]
  rfl

theorem adjoint_interval {s t : ℝ≥0} (hst : s ≤ t) :
    covarianceAdjoint (rightLimitClass t - rightLimitClass s) =
      indicatorConstLp 2 measurableSet_Ioc (energyMeasure_Ioc_finite s t).ne (1 : ℝ) := by
  rw [← integral_interval hst, adjoint_integral]

end OperatorDerivativeRewrite.Foundation.IBMRightGermCovarianceAdjoint
