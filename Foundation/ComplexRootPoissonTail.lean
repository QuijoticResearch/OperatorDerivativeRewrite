import Foundation.ProbabilityTailBound
import Foundation.ComplexRootPoissonPositiveMoments

/-! Native positive L2 lower tails for the actual Poissonized heat approximations. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.ComplexRootPoissonTail
open ComplexRootPoissonPositiveMoments ComplexRootPoissonPolynomialDomain
open ComplexRootHeatTransformLimit

theorem norm_square_memLp (r : ℝ≥0) (a : ℝ) :
    MemLp (fun z : ℂ => ‖z‖^2) 2 (ComplexRootPoissonLaw.law r a) := by
  apply (integrable_norm_rpow_iff (p := 2) (f := fun z : ℂ => ‖z‖^2)
    (by fun_prop) (by norm_num) (by norm_num)).mp
  convert norm_power_integrable r a 4 using 1
  funext z
  norm_num [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖z‖), ← pow_mul]

theorem tail_mass_lower (T : ℝ≥0) (hT : 0 < T) (n : ℕ) (hn : n ≠ 0)
    (b : ℝ) (hb : 0 ≤ b)
    (hbm : 2*b ≤ ∫ z : ℂ, ‖z‖^2 ∂ComplexRootPoissonLaw.law (n : ℝ≥0) (amplitude T n)) :
    1/12 ≤ (ComplexRootPoissonLaw.law (n : ℝ≥0) (amplitude T n)).real {z | b < ‖z‖^2} := by
  let μ := ComplexRootPoissonLaw.law (n : ℝ≥0) (amplitude T n)
  let m : ℝ := ∫ z : ℂ, ‖z‖^2 ∂μ
  let p : ℝ := μ.real {z : ℂ | b < ‖z‖^2}
  have hm : 0 ≤ m := integral_nonneg (fun _ => sq_nonneg _)
  have hp : 0 ≤ p := ENNReal.toReal_nonneg
  have hms : 0 < m^2 := by
    change 0 < (∫ z : ℂ, ‖z‖^2 ∂ComplexRootPoissonLaw.law (n : ℝ≥0) (amplitude T n))^2
    rw [scaled_second_square]
    have hn' : 0 < n := Nat.pos_of_ne_zero hn
    positivity
  have hs := ProbabilityTailBound.mean_tail_square μ (fun z : ℂ => ‖z‖^2)
    (by fun_prop) (fun _ => sq_nonneg _) (norm_square_memLp _ _) b hb
    (by change b ≤ m; change 2*b ≤ m at hbm; linarith)
  simp only [← pow_mul, show 2*2=4 from rfl] at hs
  change (m-b)^2 ≤ (∫ z : ℂ, ‖z‖^4 ∂μ)*p at hs
  have hl : (m/2)^2 ≤ (m-b)^2 :=
    pow_le_pow_left₀ (by positivity) (by change 2*b ≤ m at hbm; linarith) 2
  have hu := mul_le_mul_of_nonneg_right (scaled_fourth_bound T n hn) hp
  change (∫ z : ℂ, ‖z‖^4 ∂μ)*p ≤ 3*m^2*p at hu
  have he : m^2*(1/12) ≤ m^2*p := by nlinarith
  exact le_of_mul_le_mul_left he hms

theorem absolute_second_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n : ℕ => ∫ z : ℂ, ‖z‖^2
      ∂ComplexRootPoissonLaw.law (n : ℝ≥0) (amplitude T n)) atTop atTop := by
  simpa only [absolute_second, NNReal.coe_natCast, ComplexRootWalkSecondMoment.terminal_absolute_second]
    using ComplexRootScaledMoments.absolute_second_tendsto T hT

end OperatorDerivativeRewrite.Foundation.ComplexRootPoissonTail
