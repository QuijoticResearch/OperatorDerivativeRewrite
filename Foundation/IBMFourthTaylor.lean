import Foundation.IBMConditionalQuarticPair
import Foundation.GaussianBrownianQuadraticVariation
import Mathlib.Analysis.Calculus.Taylor

/-! Fourth-order finite-step Taylor calculus for supplied continuous IBM paths. -/
noncomputable section
open Set Filter
open scoped NNReal Topology

namespace OperatorDerivativeRewrite.Foundation.IBMFourthTaylor
open GaussianBrownianQuadraticVariation

/-- The genuine order-four Taylor remainder using Mathlib's fourth-degree
Taylor polynomial on the segment between the endpoints. -/
def remainder (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  f y - taylorWithinEval f 4 (uIcc x y) x y

/-- An explicit fifth-derivative bound on the fourth-order remainder. -/
theorem remainder_bound (f : ℝ → ℝ) (hf : ContDiff ℝ 5 f) (M : ℝ)
    (hM : ∀ z, ‖iteratedDeriv 5 f z‖ ≤ M) (x y : ℝ) :
    ‖remainder f x y‖ ≤ (M / 120) * |y-x|^5 := by
  by_cases hxy : x = y
  · subst y
    simp [remainder]
  obtain ⟨z, _, hz⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 4) hxy hf.contDiffOn
  change remainder f x y = _ at hz
  rw [hz]
  norm_num
  have hp : |iteratedDeriv 5 f z| ≤ M := by simpa [Real.norm_eq_abs] using hM z
  calc
    |iteratedDeriv 5 f z| * |y-x|^5 / 120 ≤ M * |y-x|^5 / 120 := by
      gcongr
    _ = M / 120 * |y-x|^5 := by ring

/-- The fourth Taylor polynomial uses the actual iterated derivatives
of `f` at the left endpoint. -/
theorem taylor_four_explicit (f : ℝ → ℝ) (hf : ContDiff ℝ 5 f)
    (x y : ℝ) (hxy : x ≠ y) :
    taylorWithinEval f 4 (uIcc x y) x y =
      f x + iteratedDeriv 1 f x * (y-x) +
      (1/2 : ℝ) * iteratedDeriv 2 f x * (y-x)^2 +
      (1/6 : ℝ) * iteratedDeriv 3 f x * (y-x)^3 +
      (1/24 : ℝ) * iteratedDeriv 4 f x * (y-x)^4 := by
  have hder (n : ℕ) (hn : n ≤ 4) :
      iteratedDerivWithin n f (uIcc x y) x = iteratedDeriv n f x :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hxy)
      (hf.of_le (by exact_mod_cast (Nat.le_trans hn (by decide : 4 ≤ 5)))).contDiffAt (left_mem_uIcc)
  rw [taylorWithinEval_succ f 3, taylorWithinEval_succ f 2,
    taylorWithinEval_succ f 1, taylorWithinEval_succ f 0,
    taylor_within_zero_eval,
    hder 1 (by decide), hder 2 (by decide),
    hder 3 (by decide), hder 4 (by decide)]
  norm_num [smul_eq_mul]
  ring

/-- Exact fourth-order finite increment identity, with a rigorously
controlled remainder but no assertion that any stochastic sum converges. -/
theorem increment_identity (f : ℝ → ℝ) (hf : ContDiff ℝ 5 f)
    (x y : ℝ) :
    f y - f x =
      iteratedDeriv 1 f x * (y-x) +
      (1/2 : ℝ) * iteratedDeriv 2 f x * (y-x)^2 +
      (1/6 : ℝ) * iteratedDeriv 3 f x * (y-x)^3 +
      (1/24 : ℝ) * iteratedDeriv 4 f x * (y-x)^4 +
      remainder f x y := by
  by_cases hxy : x = y
  · subst y
    simp [remainder]
  rw [remainder, taylor_four_explicit f hf x y hxy]
  ring


/-- Exact fourth-order decomposition along any finite real path; all four
Taylor ranks and the controlled remainder are retained separately. -/
theorem finite_path_identity (f : ℝ → ℝ) (hf : ContDiff ℝ 5 f)
    {n : ℕ} (x : Fin (n+1) → ℝ) :
    f (x (Fin.last n)) - f (x 0) =
      ∑ k : Fin n,
        (iteratedDeriv 1 f (x k.castSucc) * (x k.succ - x k.castSucc) +
        (1/2 : ℝ) * iteratedDeriv 2 f (x k.castSucc) *
          (x k.succ - x k.castSucc)^2 +
        (1/6 : ℝ) * iteratedDeriv 3 f (x k.castSucc) *
          (x k.succ - x k.castSucc)^3 +
        (1/24 : ℝ) * iteratedDeriv 4 f (x k.castSucc) *
          (x k.succ - x k.castSucc)^4 +
        remainder f (x k.castSucc) (x k.succ)) := by
  rw [← sum_fin_differences (fun i => f (x i))]
  apply Finset.sum_congr rfl
  intro k hk
  exact increment_identity f hf (x k.castSucc) (x k.succ)

open IBMContinuousComposition IBMSourceLaws InfiniteGaussian

/-- The exact finite fourth-order Taylor decomposition for the supplied
continuous IBM composition. It is a pathwise identity, with no stochastic
limit or Itô integral asserted. -/
theorem conditional_ibm_partition_identity
    (f : ℝ → ℝ) (hf : ContDiff ℝ 5 f)
    (X : SampleSpace → C(ℝ, ℝ)) (Y : SampleSpace → C(ℝ≥0, ℝ))
    {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (ω : JointSample) :
    f (value X Y (τ (Fin.last n)) ω) - f (value X Y (τ 0) ω) =
      ∑ k : Fin n,
        (iteratedDeriv 1 f (value X Y (τ k.castSucc) ω) *
          (value X Y (τ k.succ) ω - value X Y (τ k.castSucc) ω) +
        (1/2 : ℝ) * iteratedDeriv 2 f (value X Y (τ k.castSucc) ω) *
          (value X Y (τ k.succ) ω - value X Y (τ k.castSucc) ω)^2 +
        (1/6 : ℝ) * iteratedDeriv 3 f (value X Y (τ k.castSucc) ω) *
          (value X Y (τ k.succ) ω - value X Y (τ k.castSucc) ω)^3 +
        (1/24 : ℝ) * iteratedDeriv 4 f (value X Y (τ k.castSucc) ω) *
          (value X Y (τ k.succ) ω - value X Y (τ k.castSucc) ω)^4 +
        remainder f (value X Y (τ k.castSucc) ω)
          (value X Y (τ k.succ) ω)) :=
  finite_path_identity f hf (fun i => value X Y (τ i) ω)
end OperatorDerivativeRewrite.Foundation.IBMFourthTaylor
