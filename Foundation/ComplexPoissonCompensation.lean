import Foundation.PoissonEntireAlgebra

/-! Central complex compensation of genuine Poisson operator averages. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.ComplexPoissonCompensation

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B] [NormOneClass B]
local instance : NormedAlgebra ℚ B := NormedAlgebra.restrictScalars ℚ ℝ B
local instance : ContinuousSMul ℚ ℂ := by
  let : IsBoundedSMul ℚ ℂ := IsBoundedSMul.of_norm_smul_le fun q z => by
    change ‖(q : ℂ)*z‖ ≤ ‖q‖*‖z‖
    simp [← Rat.norm_cast_real, Real.norm_eq_abs]
  infer_instance

omit [NormOneClass B] in
theorem exp_compensated (b : B) (c : ℂ) (t : ℝ) :
    NormedSpace.exp (t • (b-c • (1 : B))) =
      Complex.exp (-(t : ℂ)*c) • NormedSpace.exp (t • b) := by
  have hc : Commute ((-(t : ℂ)*c) • (1 : B)) (t • b) :=
    ((Commute.one_left b).smul_left (-(t : ℂ)*c)).smul_right t
  have he : t • (b-c • (1 : B)) = (-(t : ℂ)*c) • (1 : B) + t • b := by
    rw [smul_sub, ← smul_assoc, Complex.real_smul, neg_mul, neg_smul]
    abel
  have hs : NormedSpace.exp ((-(t : ℂ)*c) • (1 : B)) =
      Complex.exp (-(t : ℂ)*c) • (1 : B) := by
    rw [← Algebra.algebraMap_eq_smul_one, ← NormedSpace.algebraMap_exp_comm,
      ← Complex.exp_eq_exp_ℂ, Algebra.algebraMap_eq_smul_one]
  rw [he, NormedSpace.exp_add_of_commute hc, hs, smul_mul_assoc, one_mul]

theorem exp_compensated_average (b : B) (c : ℂ) (r : ℝ≥0) :
    NormedSpace.exp ((r : ℝ) • (b-c • (1 : B))) =
      Complex.exp ((r : ℂ)*(1-c)) • PoissonContractionAlgebra.average b r := by
  rw [exp_compensated, PoissonEntireAlgebra.average_eq_scaled_exp]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  have he : Complex.exp ((r : ℂ)*(1-c)) * (Real.exp (-(r : ℝ)) : ℂ) =
      Complex.exp (-(r : ℂ)*c) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  change _ = (Complex.exp ((r : ℂ)*(1-c)) * (Real.exp (-(r : ℝ)) : ℂ)) • _
  rw [he]

end OperatorDerivativeRewrite.Foundation.ComplexPoissonCompensation
