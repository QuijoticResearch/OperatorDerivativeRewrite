import Foundation.PoissonContractionAlgebra
import Foundation.PoissonEntireMoments

/-! The existing Poisson operator calculus extends to every bounded algebra element. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.PoissonEntireAlgebra
open PoissonContractionAlgebra

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B] [NormOneClass B]
local instance : NormedAlgebra ℚ B := NormedAlgebra.restrictScalars ℚ ℝ B

omit [NormedAlgebra ℝ B] [CompleteSpace B] in
theorem powers_integrable (b : B) (r : ℝ≥0) :
    Integrable (fun n : ℕ => b^n) (poissonMeasure r) := by
  exact (PoissonEntireMoments.real_powers_integrable r ‖b‖).mono'
    StronglyMeasurable.of_discrete.aestronglyMeasurable
    (Eventually.of_forall (norm_pow_le b))

theorem average_hasSum (b : B) (r : ℝ≥0) :
    HasSum (fun n : ℕ => (Real.exp (-(r : ℝ)) * (r : ℝ)^n / n.factorial) • b^n)
      (average b r) := hasSum_integral_poissonMeasure (powers_integrable b r)

theorem average_eq_scaled_exp (b : B) (r : ℝ≥0) :
    average b r = Real.exp (-(r : ℝ)) • NormedSpace.exp ((r : ℝ) • b) := by
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ((r : ℝ) • b)).const_smul
    (Real.exp (-(r : ℝ)))
  have he : (fun n : ℕ => (Real.exp (-(r : ℝ)) * (r : ℝ)^n / n.factorial) • b^n) =
      (fun n => Real.exp (-(r : ℝ)) • ((n.factorial : ℝ)⁻¹ • ((r : ℝ) • b)^n)) := by
    funext n
    rw [smul_pow, smul_smul, smul_smul]
    congr 1
    simp only [div_eq_mul_inv]
    ring
  exact (average_hasSum b r).unique (he ▸ hs)

theorem average_eq_evolution (b : B) (r : ℝ≥0) :
    average b r = evolution b r := by
  rw [average_eq_scaled_exp b r]
  have hc : Commute ((-(r : ℝ)) • (1 : B)) ((r : ℝ) • b) :=
    ((Commute.one_left b).smul_left (-(r : ℝ))).smul_right (r : ℝ)
  have he : ((r : ℝ) • (b-1)) = (-(r : ℝ)) • (1 : B) + (r : ℝ) • b := by
    simp only [smul_sub, neg_smul]
    abel
  have hs : NormedSpace.exp ((-(r : ℝ)) • (1 : B)) = Real.exp (-(r : ℝ)) • (1 : B) := by
    rw [← Algebra.algebraMap_eq_smul_one, ← NormedSpace.algebraMap_exp_comm,
      ← Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one]
  rw [evolution, he, NormedSpace.exp_add_of_commute hc, hs, smul_mul_assoc, one_mul]

omit [CompleteSpace B] in
theorem average_norm_bound (b : B) (r : ℝ≥0) :
    ‖average b r‖ ≤ Real.exp ((r : ℝ)*(‖b‖-1)) := by
  calc
    ‖average b r‖ ≤ ∫ n : ℕ, ‖b^n‖ ∂poissonMeasure r := norm_integral_le_integral_norm _
    _ ≤ ∫ n : ℕ, ‖b‖^n ∂poissonMeasure r :=
      integral_mono_ae (powers_integrable b r).norm
        (PoissonEntireMoments.real_powers_integrable r ‖b‖)
        (Eventually.of_forall (norm_pow_le b))
    _ = _ := PoissonEntireMoments.real_powers_integral r ‖b‖

end OperatorDerivativeRewrite.Foundation.PoissonEntireAlgebra
