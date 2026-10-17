import Foundation.ComplexRootHeatTransformLimit

/-! Exact higher-heat normalization and absolute second-moment growth of genuine complex walks. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.ComplexRootScaledMoments
open ComplexFourthRootNoise ComplexFourthRootWalk ComplexRootWalkSecondMoment
open ComplexRootHeatTransformLimit ComplexRootOneStepCalculus

theorem amplitude_square (T : ℝ≥0) (n : ℕ) : (amplitude T n)^2 = Real.sqrt (6*(T : ℝ)/n) := by
  unfold amplitude
  exact Real.sq_sqrt (Real.sqrt_nonneg _)

theorem increment_fourth (T : ℝ≥0) (n : ℕ) :
    (∫ k, (noise (amplitude T n) k)^4 ∂ComplexFourthRootNoise.probability) =
      -24*((T : ℝ) : ℂ)/(n : ℂ) := by
  rw [fourth, ← Complex.ofReal_pow, amplitude_fourth]
  push_cast
  ring

theorem shifted_quartic (T : ℝ≥0) (n : ℕ) (z : ℂ) :
    (∫ k, (z + noise (amplitude T n) k)^4 ∂ComplexFourthRootNoise.probability) =
      z^4 - 24*((T : ℝ) : ℂ)/(n : ℂ) := by
  rw [shifted_fourth, ← Complex.ofReal_pow, amplitude_fourth]
  push_cast
  ring

theorem absolute_second_square (T : ℝ≥0) (n : ℕ) :
    (∫ ω, ‖terminal n (amplitude T n) ω‖^2 ∂probability n)^2 = 24*(T : ℝ)*n := by
  rw [terminal_absolute_second]
  calc
    _ = 4*(n : ℝ)^2*(amplitude T n)^4 := by ring
    _ = 4*(n : ℝ)^2*(6*(T : ℝ)/n) := by rw [amplitude_fourth]
    _ = _ := by
      by_cases hn : n = 0
      · simp [hn]
      · have hnr : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
        field_simp [hnr]
        ring

theorem absolute_second_eq_sqrt (T : ℝ≥0) (n : ℕ) :
    (∫ ω, ‖terminal n (amplitude T n) ω‖^2 ∂probability n) = Real.sqrt (24*(T : ℝ)*n) := by
  have hn : 0 ≤ ∫ ω, ‖terminal n (amplitude T n) ω‖^2 ∂probability n :=
    integral_nonneg (fun _ => sq_nonneg _)
  calc
    _ = Real.sqrt ((∫ ω, ‖terminal n (amplitude T n) ω‖^2 ∂probability n)^2) :=
      (Real.sqrt_sq hn).symm
    _ = _ := congrArg Real.sqrt (absolute_second_square T n)

theorem absolute_second_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => ∫ ω, ‖terminal n (amplitude T n) ω‖^2 ∂probability n) atTop atTop := by
  simp_rw [absolute_second_eq_sqrt]
  apply Real.tendsto_sqrt_atTop.comp
  exact (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).const_mul_atTop
    (by positivity : 0 < 24*(T : ℝ))

end OperatorDerivativeRewrite.Foundation.ComplexRootScaledMoments
