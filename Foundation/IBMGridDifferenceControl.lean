import Foundation.IBMGridIntersection

/-! Actual stochastic difference identification and control across two grids. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMGridDifferenceControl
open IBMTimeAveragedObservable IBMNaturalFiltrationObstruction IBMRawObservedMartingale
open IBMIntrinsicMartingaleStep (Coefficient)
open IBMIntrinsicPredictableProcess (timeStep timeSum)
open IBMTerminalPredictableStep IBMTerminalPredictableGrid
open IBMGridIntersection
set_option backward.isDefEq.respectTransparency false

def negate {s : ℝ≥0} (a : Coefficient s) : Coefficient s where
  function := -a.function
  adapted := a.adapted.neg
  bound := a.bound
  bounded := by
    filter_upwards [a.bounded] with ω hω
    simpa only [Pi.neg_apply, norm_neg] using hω

theorem timeStep_negate {s : ℝ≥0} (t : ℝ≥0) (a : Coefficient s) (r : ℝ≥0)
    (ω : IBMSourceLaws.JointSample) : timeStep s t (negate a) r ω = -timeStep s t a r ω := by
  by_cases hr : r ∈ Ioc s t <;> simp [timeStep, negate, hr]

theorem stepClass_negate (F : JointL2) {s : ℝ≥0} (t : ℝ≥0) (a : Coefficient s) :
    stepClass F s t (negate a) = -stepClass F s t a := by
  apply Lp.ext
  filter_upwards [stepClass_ae F s t (negate a), stepClass_ae F s t a,
    Lp.coeFn_neg (stepClass F s t a)] with ω hn ha hneg
  rw [hn, hneg, Pi.neg_apply, ha]
  simp only [step, negate, Pi.mul_apply, Pi.neg_apply, neg_mul]

def integral (F : JointL2) (τ σ : ℕ → ℝ≥0) (a : ∀ i, Coefficient (τ i))
    (b : ∀ j, Coefficient (σ j)) (n m : ℕ) : JointL2 :=
  ∑ p ∈ cells τ σ n m, stepClass F (left τ σ p) (right τ σ p) (coefficient τ σ a b p)

theorem integral_ae (F : JointL2) (τ σ : ℕ → ℝ≥0) (a : ∀ i, Coefficient (τ i))
    (b : ∀ j, Coefficient (σ j)) (n m : ℕ) :
    integral F τ σ a b n m =ᵐ[IBMSourceLaws.jointMeasure]
      (fun ω => ∑ p ∈ cells τ σ n m,
        step F (left τ σ p) (right τ σ p) (coefficient τ σ a b p) ω) := by
  classical
  have hh := IBMFiniteIntervalIdentification.finiteClass_ae F
    (fun p : cells τ σ n m => left τ σ p) (fun p => right τ σ p)
    (fun p => coefficient τ σ a b p)
  have hc : (∑ p : cells τ σ n m,
      stepClass F (left τ σ p) (right τ σ p) (coefficient τ σ a b p)) =
        integral F τ σ a b n m := Finset.sum_coe_sort (cells τ σ n m)
          (fun p => stepClass F (left τ σ p) (right τ σ p) (coefficient τ σ a b p))
  rw [hc] at hh
  exact hh.trans (EventuallyEq.of_eq (funext fun ω => Finset.sum_coe_sort (cells τ σ n m)
    (fun p => step F (left τ σ p) (right τ σ p) (coefficient τ σ a b p) ω)))

theorem integral_difference (F : JointL2) (τ σ : ℕ → ℝ≥0)
    (hτ : Monotone τ) (hσ : Monotone σ)
    (a : ∀ i, Coefficient (τ i)) (b : ∀ j, Coefficient (σ j)) (n m : ℕ)
    (hstart : τ 0 = σ 0) (hend : τ n = σ m) :
    integral F τ σ a b n m = sumClass F τ a n - sumClass F σ b m := by
  classical
  let s : Fin n ⊕ Fin m → ℝ≥0 := Sum.elim (fun i => τ i) (fun j => σ j)
  let t : Fin n ⊕ Fin m → ℝ≥0 := Sum.elim (fun i => τ (i.val+1)) (fun j => σ (j.val+1))
  let c : (k : Fin n ⊕ Fin m) → Coefficient (s k)
    | .inl i => a i
    | .inr j => negate (b j)
  have hh := IBMFiniteIntervalIdentification.stochastic_integral_identification F s t c
    (fun p : cells τ σ n m => left τ σ p) (fun p => right τ σ p)
    (fun p => coefficient τ σ a b p)
    (by intro k; cases k with
        | inl i => exact hτ (Nat.le_succ i.val)
        | inr j => exact hσ (Nat.le_succ j.val))
    (fun p => (cells_positive τ σ n m p.property).le) (by
      intro r
      filter_upwards [] with ω
      have hproc := process_difference τ σ hτ hσ a b n m hstart hend r ω
      have hsource : (∑ k, timeStep (s k) (t k) (c k) r ω) =
          timeSum τ a n r ω - timeSum σ b m r ω := by
        simp only [Fintype.sum_sum_type, s, t, c, Sum.elim_inl, Sum.elim_inr]
        simp_rw [timeStep_negate, Finset.sum_neg_distrib]
        rw [← sub_eq_add_neg]
        exact congrArg₂ (fun x y : ℝ => x-y)
          (Fin.sum_univ_eq_sum_range (fun i => timeStep (τ i) (τ (i+1)) (a i) r ω) n)
          (Fin.sum_univ_eq_sum_range (fun j => timeStep (σ j) (σ (j+1)) (b j) r ω) m)
      exact hsource.trans (hproc.symm.trans (Finset.sum_coe_sort (cells τ σ n m)
        (fun p => timeStep (left τ σ p) (right τ σ p) (coefficient τ σ a b p) r ω)).symm))
  have hs : (∑ k, stepClass F (s k) (t k) (c k)) = sumClass F τ a n - sumClass F σ b m := by
    simp only [Fintype.sum_sum_type, s, t, c, Sum.elim_inl, Sum.elim_inr]
    simp_rw [stepClass_negate, Finset.sum_neg_distrib]
    rw [← sub_eq_add_neg]
    exact congrArg₂ (fun x y : JointL2 => x-y)
      (Fin.sum_univ_eq_sum_range (fun i => stepClass F (τ i) (τ (i+1)) (a i)) n)
      (Fin.sum_univ_eq_sum_range (fun j => stepClass F (σ j) (σ (j+1)) (b j)) m)
  exact (Finset.sum_coe_sort (cells τ σ n m)
    (fun p => stepClass F (left τ σ p) (right τ σ p) (coefficient τ σ a b p))).symm.trans
      (hh.symm.trans hs)

theorem difference_bound (F : JointL2) (τ σ : ℕ → ℝ≥0)
    (hτ : Monotone τ) (hσ : Monotone σ)
    (a : ∀ i, Coefficient (τ i)) (b : ∀ j, Coefficient (σ j)) (n m : ℕ)
    (hstart : τ 0 = σ 0) (hend : τ n = σ m) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ r, ∀ᵐ ω ∂IBMSourceLaws.jointMeasure,
      ‖timeSum τ a n r ω - timeSum σ b m r ω‖ ≤ C) :
    ‖sumClass F τ a n - sumClass F σ b m‖ ^ 2 ≤ C ^ 2 * ‖F‖ ^ 2 := by
  rw [← integral_difference F τ σ hτ hσ a b n m hstart hend]
  apply IBMDisjointProcessControl.actual_process_bound F (cells τ σ n m)
    (left τ σ) (right τ σ) (coefficient τ σ a b)
    (fun _ hp => (cells_positive τ σ n m hp).le)
    (fun _ _ _ _ hpq => cells_separated τ σ hτ hσ hpq) C hC
  intro r
  filter_upwards [ha r] with ω hω
  rwa [← process_difference τ σ hτ hσ a b n m hstart hend r ω] at hω

theorem actual_difference (F : JointL2) (τ σ : ℕ → ℝ≥0)
    (hτ : Monotone τ) (hσ : Monotone σ)
    (a : ∀ i, Coefficient (τ i)) (b : ∀ j, Coefficient (σ j)) (n m : ℕ)
    (hstart : τ 0 = σ 0) (hend : τ n = σ m) :
    (sum F τ a n - sum F σ b m) =ᵐ[IBMSourceLaws.jointMeasure]
      (fun ω => ∑ p ∈ cells τ σ n m,
        step F (left τ σ p) (right τ σ p) (coefficient τ σ a b p) ω) := by
  have hs := (Lp.coeFn_sub (sumClass F τ a n) (sumClass F σ b m)).trans
    ((sumClass_ae F τ a n).sub (sumClass_ae F σ b m))
  have hc := integral_ae F τ σ a b n m
  rw [integral_difference F τ σ hτ hσ a b n m hstart hend] at hc
  exact hs.symm.trans hc

end OperatorDerivativeRewrite.Foundation.IBMGridDifferenceControl
