import Foundation.FourierPathRoughTransferObstruction
import Foundation.FourierPathDirectionalAdjoint

/-! A genuine continuous expectation component excluded from a path derivative's adjoint domain. -/
noncomputable section
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathRoughAdjointObstruction
open HigherHeatFourierBanach FourierPathRoughDirection FourierPathRoughTransferObstruction

def imaginaryExpectation (T : ℝ≥0) (hT : 0 < T) : StrongDual ℝ (TestSpace levels frequencies) :=
  Complex.imCLM.comp ((expectation levels frequencies 2 (by norm_num) T hT).restrictScalars ℝ)

theorem imaginaryExpectation_apply (T : ℝ≥0) (hT : 0 < T) (f : TestSpace levels frequencies) :
    imaginaryExpectation T hT f=(expectation levels frequencies 2 (by norm_num) T hT f).im := rfl

theorem expectation_not_in_adjoint_domain (T : ℝ≥0) (hT : 0 < T) :
    imaginaryExpectation T hT ∉
      (FourierPathDirectionalAdjoint.adjoint levels frequencies direction).domain := by
  intro hφ
  obtain ⟨L,hL⟩ := (FourierPathDirectionalAdjoint.adjoint_domain_iff_transfer
    levels frequencies direction (imaginaryExpectation T hT)).mp hφ
  apply no_real_dual_transfer T hT
  exact ⟨L,hL⟩

end OperatorDerivativeRewrite.Foundation.FourierPathRoughAdjointObstruction
