import Foundation.IBMIntrinsicMartingaleGrid

/-! Actual interval refinement and uniform energy control for the intrinsic
IBM martingale. These identities preserve the original random coefficients. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMIntrinsicMartingaleRefinement
open IBMNaturalFiltrationObstruction IBMTimeAveragedObservable
open IBMIntrinsicQuadraticMartingale IBMIntrinsicMartingaleStep IBMIntrinsicMartingaleGrid
set_option backward.isDefEq.respectTransparency false

def constant (s : ℝ≥0) (c : ℝ) : Coefficient s where
  function := fun _ => c
  adapted := stronglyMeasurable_const
  bound := ‖c‖
  bounded := ae_of_all _ fun _ => le_rfl

def later {s u : ℝ≥0} (hsu : s ≤ u) (a : Coefficient s) : Coefficient u where
  function := a.function
  adapted := a.adapted.mono (naturalFiltration.mono hsu)
  bound := a.bound
  bounded := a.bounded

theorem split_step {s u : ℝ≥0} (hsu : s ≤ u) (t : ℝ≥0) (a : Coefficient s) :
    step s u a + step u t (later hsu a) = step s t a := by
  funext ω
  simp only [step, increment, later, Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
  ring

def constantAlong (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (a : Coefficient (τ 0))
    (i : ℕ) : Coefficient (τ i) := later (hτ (Nat.zero_le i)) a

/-- Arbitrarily many subdivisions of one actual interval leave its stochastic
integral unchanged when its original coefficient is retained. -/
theorem refined_sum (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (a : Coefficient (τ 0)) (n : ℕ) :
    sum τ (constantAlong τ hτ a) n = step (τ 0) (τ n) a := by
  funext ω
  induction n with
  | zero => simp [sum, step, increment]
  | succ n ih =>
    simp only [sum, Finset.sum_range_succ, Pi.add_apply] at *
    rw [ih]
    simp only [step, increment, constantAlong, later, Pi.mul_apply, Pi.sub_apply]
    ring

theorem refined_sumClass (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : Coefficient (τ 0)) (n : ℕ) :
    sumClass τ (constantAlong τ hτ a) n = stepClass (τ 0) (τ n) a := by
  apply Lp.ext
  exact (sumClass_ae τ (constantAlong τ hτ a) n).trans
    ((Filter.EventuallyEq.of_eq (refined_sum τ hτ a n)).trans
      (stepClass_ae (τ 0) (τ n) a).symm)

theorem unit_stepClass (s t : ℝ≥0) :
    stepClass s t (constant s 1) = (valueClass t : JointL2) - (valueClass s : JointL2) := by
  apply Lp.ext
  filter_upwards [stepClass_ae s t (constant s 1), valueClass_ae t, valueClass_ae s,
    Lp.coeFn_sub (valueClass t : JointL2) (valueClass s : JointL2)] with ω hs ht hu hd
  rw [hs, hd, Pi.sub_apply, ht, hu]
  simp [step, constant, increment]

theorem unit_energy_bound {s t : ℝ≥0} (hst : s ≤ t) :
    ‖stepClass s t (constant s 1)‖ ^ 2 ≤ 2 * (t : ℝ) ^ 2 := by
  have ho := past_inner_step_zero hst (constant s 1) (valueClass s : JointL2)
    (valueClass s).property
  have he : (valueClass t : JointL2) =
      (valueClass s : JointL2) + stepClass s t (constant s 1) := by
    rw [unit_stepClass]; abel
  have hn := valueClass_bound_sq t
  change ‖(valueClass t : JointL2)‖ ^ 2 ≤ _ at hn
  rw [he, norm_add_sq_real, ho] at hn
  nlinarith [sq_nonneg ‖(valueClass s : JointL2)‖]

theorem step_norm_bound (s t : ℝ≥0) (a : Coefficient s) (C : ℝ)
    (hC : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ‖a.function ω‖ ≤ C) :
    ‖stepClass s t a‖ ≤ C * ‖stepClass s t (constant s 1)‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [stepClass_ae s t a, stepClass_ae s t (constant s 1), hC] with ω ha hu hc
  rw [ha, hu]
  simp only [step, constant, Pi.mul_apply, one_mul]
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)

theorem grid_energy_bound (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i)) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ‖(a i).function ω‖ ≤ C) (n : ℕ) :
    ‖sumClass τ a n‖ ^ 2 ≤ C ^ 2 * (2 * (τ n : ℝ) ^ 2) := by
  have hu : (fun i => constant (τ i) 1) = constantAlong τ hτ (constant (τ 0) 1) := by
    funext i
    rfl
  calc
    _ = ∑ i ∈ Finset.range n, ‖stepClass (τ i) (τ (i + 1)) (a i)‖ ^ 2 := energy_identity τ hτ a n
    _ ≤ ∑ i ∈ Finset.range n, C ^ 2 * ‖stepClass (τ i) (τ (i + 1)) (constant (τ i) 1)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hb := step_norm_bound (τ i) (τ (i + 1)) (a i) C (ha i)
      simpa only [mul_pow] using (sq_le_sq₀
        (norm_nonneg (stepClass (τ i) (τ (i + 1)) (a i)))
        (mul_nonneg hC (norm_nonneg (stepClass (τ i) (τ (i + 1)) (constant (τ i) 1))))).mpr hb
    _ = C ^ 2 * ‖sumClass τ (fun i => constant (τ i) 1) n‖ ^ 2 := by
      rw [energy_identity τ hτ, Finset.mul_sum]
    _ = C ^ 2 * ‖stepClass (τ 0) (τ n) (constant (τ 0) 1)‖ ^ 2 := by
      rw [hu, refined_sumClass]
    _ ≤ _ := mul_le_mul_of_nonneg_left (unit_energy_bound (hτ (Nat.zero_le n))) (sq_nonneg C)

end OperatorDerivativeRewrite.Foundation.IBMIntrinsicMartingaleRefinement
