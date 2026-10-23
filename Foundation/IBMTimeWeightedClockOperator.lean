import Foundation.IBMTimeWeightedSineCalculus
import Foundation.L2GeneratingIndicators
import Foundation.BochnerL2Dominated
import Mathlib.MeasureTheory.PiSystem

/-! The original native clock integrals as uniformly bounded operators on
actual time-L2 classes. No gradient convergence is assumed in the bounds. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMTimeWeightedClockOperator
open InfiniteGaussian IBMClockOverlapEnergy IBMIntrinsicOperators
open IBMTimeWeightedSineClock
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
attribute [local irreducible] IBMNonlinearClockField.field IBMClockVectorTranspose.clockField

abbrev TimeL2 (T : ℝ≥0) := Lp ℝ 2 (window T)

def bound (T : ℝ≥0) : ℝ :=
  Real.sqrt (8*IBMFoldedTransitionBound.peak 1*(T:ℝ)*Real.sqrt T+4*(T:ℝ)^2)

theorem native_congr (n : ℕ) (g h : ℝ → ℝ) (T : ℝ≥0)
    (he : g =ᵐ[window T] h) : nativeGradient n g T = nativeGradient n h T := by
  unfold nativeGradient
  congr 1
  exact integral_congr_ae (he.mono fun t ht => congrArg
    (fun c : ℝ => c • IBMNonlinearClockField.field n t) ht)

def nativeLinear (n : ℕ) (T : ℝ≥0) : TimeL2 T →ₗ[ℝ] FieldSpace where
  toFun g := nativeGradient n g T
  map_add' g h := by
    rw [native_congr n _ _ T (Lp.coeFn_add g h)]
    unfold nativeGradient
    simp only [Pi.add_apply,add_smul]
    have hi := IBMClockTimeWeightEnergy.weighted_integrable n g T.property (Lp.memLp g)
    have hj := IBMClockTimeWeightEnergy.weighted_integrable n h T.property (Lp.memLp h)
    exact (congrArg IBMClockVectorTranspose.clockField (integral_add hi hj)).trans
      (map_add IBMClockVectorTranspose.clockField _ _)
  map_smul' c g := by
    change nativeGradient n (⇑(c • g)) T = c • nativeGradient n g T
    rw [native_congr n _ _ T (Lp.coeFn_smul c g)]
    unfold nativeGradient
    simp only [Pi.smul_apply,smul_eq_mul,mul_smul]
    exact (congrArg IBMClockVectorTranspose.clockField (integral_smul (μ := window T) c
      (fun t => g t • IBMNonlinearClockField.field n t))).trans
      (map_smul IBMClockVectorTranspose.clockField c _)

theorem nativeLinear_bound (n : ℕ) (T : ℝ≥0) (g : TimeL2 T) :
    ‖nativeLinear n T g‖ ≤ bound T * ‖g‖ := by
  have hb := native_energy n g T (Lp.memLp g)
  have he : (∫ t, (g t)^2 ∂window T) = ‖g‖^2 := by
    simpa only [Real.norm_eq_abs,sq_abs] using (BochnerL2Dominated.norm_sq_integral g).symm
  have hC : 0 ≤ 8*IBMFoldedTransitionBound.peak 1*(T:ℝ)*Real.sqrt T+4*(T:ℝ)^2 := by
    have hp := IBMFoldedTransitionBound.peak_nonneg (1 : ℝ≥0)
    positivity
  change ‖nativeGradient n g T‖^2 ≤ _ at hb
  dsimp only [energy] at hb
  rw [he] at hb
  change ‖nativeGradient n g T‖ ≤ _
  dsimp only [bound]
  have heq : (Real.sqrt
      (8*IBMFoldedTransitionBound.peak 1*(T:ℝ)*Real.sqrt T+4*(T:ℝ)^2)*‖g‖)^2 =
      (8*IBMFoldedTransitionBound.peak 1*(T:ℝ)*Real.sqrt T+4*(T:ℝ)^2)*‖g‖^2 := by
    rw [mul_pow,Real.sq_sqrt hC]
  have hpos := mul_nonneg (Real.sqrt_nonneg
    (8*IBMFoldedTransitionBound.peak 1*(T:ℝ)*Real.sqrt T+4*(T:ℝ)^2)) (norm_nonneg g)
  nlinarith [norm_nonneg (nativeGradient n g T)]

def nativeOperator (n : ℕ) (T : ℝ≥0) : TimeL2 T →L[ℝ] FieldSpace :=
  (nativeLinear n T).mkContinuous (bound T) (nativeLinear_bound n T)

theorem nativeOperator_difference (n : ℕ) (T : ℝ≥0) (g h : TimeL2 T) :
    dist (nativeOperator n T g) (nativeOperator n T h) ≤ bound T * dist g h := by
  rw [dist_eq_norm,dist_eq_norm,← map_sub]
  exact nativeLinear_bound n T (g-h)

end OperatorDerivativeRewrite.Foundation.IBMTimeWeightedClockOperator
