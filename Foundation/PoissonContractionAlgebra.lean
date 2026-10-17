import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! Genuine Poisson averages of contractions and their bounded exponential semigroup. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.PoissonContractionAlgebra

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B] [NormOneClass B]

local instance : NormedAlgebra ℚ B := NormedAlgebra.restrictScalars ℚ ℝ B

def average (b : B) (r : ℝ≥0) : B := ∫ n : ℕ, b^n ∂poissonMeasure r

theorem powers_integrable (b : B) (hb : ‖b‖ ≤ 1) (r : ℝ≥0) :
    Integrable (fun n : ℕ => b^n) (poissonMeasure r) := by
  apply Integrable.of_bound StronglyMeasurable.of_discrete.aestronglyMeasurable 1
  exact Eventually.of_forall (fun n =>
    (norm_pow_le b n).trans (by simpa using pow_le_pow_left₀ (norm_nonneg b) hb n))

theorem average_norm (b : B) (hb : ‖b‖ ≤ 1) (r : ℝ≥0) : ‖average b r‖ ≤ 1 := by
  unfold average
  simpa using norm_integral_le_of_norm_le_const (μ := poissonMeasure r)
    (Eventually.of_forall (fun n : ℕ =>
      (norm_pow_le b n).trans (by simpa using pow_le_pow_left₀ (norm_nonneg b) hb n)))

theorem average_hasSum (b : B) (hb : ‖b‖ ≤ 1) (r : ℝ≥0) :
    HasSum (fun n : ℕ => (Real.exp (-(r : ℝ)) * (r : ℝ)^n / n.factorial) • b^n)
      (average b r) := hasSum_integral_poissonMeasure (powers_integrable b hb r)

theorem average_eq_scaled_exp (b : B) (hb : ‖b‖ ≤ 1) (r : ℝ≥0) :
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
  exact (average_hasSum b hb r).unique (he ▸ hs)

def evolution (b : B) (t : ℝ) : B := NormedSpace.exp (t • (b-1))

theorem average_eq_evolution (b : B) (hb : ‖b‖ ≤ 1) (r : ℝ≥0) :
    average b r = evolution b r := by
  rw [average_eq_scaled_exp b hb r]
  have hc : Commute ((-(r : ℝ)) • (1 : B)) ((r : ℝ) • b) :=
    ((Commute.one_left b).smul_left (-(r : ℝ))).smul_right (r : ℝ)
  have he : ((r : ℝ) • (b-1)) = (-(r : ℝ)) • (1 : B) + (r : ℝ) • b := by
    simp only [smul_sub, neg_smul]
    abel
  have hs : NormedSpace.exp ((-(r : ℝ)) • (1 : B)) = Real.exp (-(r : ℝ)) • (1 : B) := by
    rw [← Algebra.algebraMap_eq_smul_one, ← NormedSpace.algebraMap_exp_comm,
      ← Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one]
  rw [evolution, he, NormedSpace.exp_add_of_commute hc, hs, smul_mul_assoc, one_mul]

theorem evolution_zero (b : B) : evolution b 0 = 1 := by simp [evolution]

theorem evolution_add (b : B) (s t : ℝ) :
    evolution b (s+t) = evolution b s * evolution b t := by
  have hc : Commute (s • (b-1)) (t • (b-1)) :=
    ((Commute.refl (b-1)).smul_left s).smul_right t
  rw [evolution, add_smul, NormedSpace.exp_add_of_commute hc]
  rfl

theorem evolution_continuous (b : B) : Continuous (evolution b) :=
  NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

theorem evolution_hasDerivAt (b : B) (t : ℝ) :
    HasDerivAt (evolution b) (evolution b t * (b-1)) t :=
  hasDerivAt_exp_smul_const (b-1) t

theorem evolution_norm (b : B) (hb : ‖b‖ ≤ 1) (r : ℝ≥0) : ‖evolution b r‖ ≤ 1 := by
  rw [← average_eq_evolution b hb r]
  exact average_norm b hb r

end OperatorDerivativeRewrite.Foundation.PoissonContractionAlgebra
