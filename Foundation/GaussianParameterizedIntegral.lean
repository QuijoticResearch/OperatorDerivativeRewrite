import Foundation.BochnerLinearIsometry
import Foundation.GaussianPredictableFull

/-! Parameterized integration of genuine predictable L2 classes.
The parameter can later be a Malliavin time, but membership of a derivative
field in this Bochner space is NOT assumed to follow from joint measurability. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianParameterizedIntegral
open InfiniteGaussian GaussianPredictableFull

variable {S : Type*} [MeasurableSpace S] (ν : Measure S)

def parameterIntegral : Lp fullPredictable 2 ν →ₗᵢ[ℝ] Lp GaussianL2 2 ν :=
  BochnerLinearIsometry.lift ν itoIntegral

theorem parameterIntegral_coeFn (u : Lp fullPredictable 2 ν) :
    parameterIntegral ν u =ᵐ[ν] fun s => itoIntegral (u s) :=
  BochnerLinearIsometry.lift_coeFn _ _ _

theorem parameterIntegral_norm (u : Lp fullPredictable 2 ν) :
    ‖parameterIntegral ν u‖ = ‖u‖ := (parameterIntegral ν).norm_map u

/-- Integrability on BOTH sides is inherited from genuine Bochner L2 membership. -/
theorem parameterIntegral_norm_sq_integrable (u : Lp fullPredictable 2 ν) :
    Integrable (fun s => ‖parameterIntegral ν u s‖ ^ 2) ν ∧
      Integrable (fun s => ‖u s‖ ^ 2) ν :=
  ⟨(Lp.memLp (parameterIntegral ν u)).norm.integrable_sq, (Lp.memLp u).norm.integrable_sq⟩

theorem parameterIntegral_isometry (u : Lp fullPredictable 2 ν) :
    (∫ s, ‖parameterIntegral ν u s‖ ^ 2 ∂ν) = ∫ s, ‖u s‖ ^ 2 ∂ν := by
  apply integral_congr_ae
  filter_upwards [parameterIntegral_coeFn ν u] with s hs
  rw [hs, itoIntegral_norm]

theorem parameterIntegral_centered (u : Lp fullPredictable 2 ν) :
    ∀ᵐ s ∂ν, (∫ ω, parameterIntegral ν u s ω ∂gaussianProduct) = 0 := by
  filter_upwards [parameterIntegral_coeFn ν u] with s hs
  rw [hs]
  exact itoIntegral_centered (u s)

theorem parameterIntegral_eq_zero_iff (u : Lp fullPredictable 2 ν) :
    parameterIntegral ν u = 0 ↔ u = 0 :=
  BochnerLinearIsometry.lift_eq_zero_iff _ _ _

end OperatorDerivativeRewrite.Foundation.GaussianParameterizedIntegral
