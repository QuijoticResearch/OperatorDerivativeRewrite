import Foundation.IBMDisjointProcessControl

/-! Actual positive intersection cells for two predictable time grids. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMGridIntersection
open IBMTimeAveragedObservable IBMNaturalFiltrationObstruction
open IBMIntrinsicMartingaleStep (Coefficient)
open IBMIntrinsicMartingaleRefinement (constant later constantAlong)
open IBMIntrinsicPredictableProcess (timeStep timeSum)
set_option backward.isDefEq.respectTransparency false

def left (τ σ : ℕ → ℝ≥0) (p : ℕ × ℕ) : ℝ≥0 := max (τ p.1) (σ p.2)
def right (τ σ : ℕ → ℝ≥0) (p : ℕ × ℕ) : ℝ≥0 := min (τ (p.1+1)) (σ (p.2+1))
def cells (τ σ : ℕ → ℝ≥0) (n m : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range n) ×ˢ (Finset.range m)).filter (fun p => left τ σ p < right τ σ p)

def coefficient (τ σ : ℕ → ℝ≥0) (a : ∀ i, Coefficient (τ i))
    (b : ∀ j, Coefficient (σ j)) (p : ℕ × ℕ) : Coefficient (left τ σ p) where
  function := (a p.1).function - (b p.2).function
  adapted := (later (le_max_left _ _) (a p.1)).adapted.sub
    (later (le_max_right _ _) (b p.2)).adapted
  bound := (a p.1).bound + (b p.2).bound
  bounded := by
    filter_upwards [(a p.1).bounded, (b p.2).bounded] with ω ha hb
    exact (norm_sub_le _ _).trans (add_le_add ha hb)

theorem cells_positive (τ σ : ℕ → ℝ≥0) (n m : ℕ) {p : ℕ × ℕ}
    (hp : p ∈ cells τ σ n m) : left τ σ p < right τ σ p :=
  (Finset.mem_filter.mp hp).2

theorem cells_separated (τ σ : ℕ → ℝ≥0) (hτ : Monotone τ) (hσ : Monotone σ)
    {p q : ℕ × ℕ} (hpq : p ≠ q) :
    right τ σ p ≤ left τ σ q ∨ right τ σ q ≤ left τ σ p := by
  by_cases hi : p.1 = q.1
  · have hj : p.2 ≠ q.2 := fun h => hpq (Prod.ext hi h)
    rcases lt_or_gt_of_ne hj with h | h
    · exact Or.inl ((min_le_right _ _).trans
        ((hσ (Nat.succ_le_of_lt h)).trans (le_max_right _ _)))
    · exact Or.inr ((min_le_right _ _).trans
        ((hσ (Nat.succ_le_of_lt h)).trans (le_max_right _ _)))
  · rcases lt_or_gt_of_ne hi with h | h
    · exact Or.inl ((min_le_left _ _).trans
        ((hτ (Nat.succ_le_of_lt h)).trans (le_max_left _ _)))
    · exact Or.inr ((min_le_left _ _).trans
        ((hτ (Nat.succ_le_of_lt h)).trans (le_max_left _ _)))

def process (τ σ : ℕ → ℝ≥0) (a : ∀ i, Coefficient (τ i))
    (b : ∀ j, Coefficient (σ j)) (n m : ℕ) (r : ℝ≥0) (ω : IBMSourceLaws.JointSample) : ℝ :=
  ∑ p ∈ cells τ σ n m, timeStep (left τ σ p) (right τ σ p) (coefficient τ σ a b p) r ω

theorem cell_formula (τ σ : ℕ → ℝ≥0) (a : ∀ i, Coefficient (τ i))
    (b : ∀ j, Coefficient (σ j)) (p : ℕ × ℕ) (r : ℝ≥0) (ω : IBMSourceLaws.JointSample) :
    timeStep (left τ σ p) (right τ σ p) (coefficient τ σ a b p) r ω =
      timeStep (τ p.1) (τ (p.1+1)) (a p.1) r ω *
        timeStep (σ p.2) (σ (p.2+1)) (constant (σ p.2) 1) r ω -
      timeStep (τ p.1) (τ (p.1+1)) (constant (τ p.1) 1) r ω *
        timeStep (σ p.2) (σ (p.2+1)) (b p.2) r ω := by
  change (Ioc (max (τ p.1) (σ p.2)) (min (τ (p.1+1)) (σ (p.2+1)))).indicator
    (fun _ => (a p.1).function ω - (b p.2).function ω) r = _
  rw [← Set.Ioc_inter_Ioc]
  by_cases h1 : r ∈ Ioc (τ p.1) (τ (p.1+1)) <;>
    by_cases h2 : r ∈ Ioc (σ p.2) (σ (p.2+1)) <;>
    simp [timeStep, constant, Set.indicator, h1, h2]

theorem process_product (τ σ : ℕ → ℝ≥0) (a : ∀ i, Coefficient (τ i))
    (b : ∀ j, Coefficient (σ j)) (n m : ℕ) (r : ℝ≥0) (ω : IBMSourceLaws.JointSample) :
    process τ σ a b n m r ω =
      timeSum τ a n r ω * timeSum σ (fun j => constant (σ j) 1) m r ω -
      timeSum τ (fun i => constant (τ i) 1) n r ω * timeSum σ b m r ω := by
  classical
  have he : process τ σ a b n m r ω =
      ∑ p ∈ (Finset.range n) ×ˢ (Finset.range m),
        timeStep (left τ σ p) (right τ σ p) (coefficient τ σ a b p) r ω := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hn
    have hnot : ¬left τ σ p < right τ σ p := by
      intro h; exact hn (Finset.mem_filter.mpr ⟨hp, h⟩)
    have hempty : Ioc (left τ σ p) (right τ σ p) = ∅ :=
      Ioc_eq_empty_of_le (le_of_not_gt hnot)
    simp only [timeStep, hempty, indicator_empty]
  rw [he]
  have hp := Finset.sum_product (Finset.range n) (Finset.range m)
    (fun p => timeStep (left τ σ p) (right τ σ p) (coefficient τ σ a b p) r ω)
  rw [hp]
  simp_rw [cell_formula, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  rfl

theorem unit_cover (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (n : ℕ)
    (r : ℝ≥0) (ω : IBMSourceLaws.JointSample) :
    timeSum τ (fun i => constant (τ i) 1) n r ω =
      (Ioc (τ 0) (τ n)).indicator (fun _ => (1 : ℝ)) r := by
  have he : (fun i => constant (τ i) 1) = constantAlong τ hτ (constant (τ 0) 1) := rfl
  rw [he]
  exact congrFun (congrFun (IBMIntrinsicPredictableProcess.refined_timeSum τ hτ
    (constant (τ 0) 1) n) r) ω

theorem process_support (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (a : ∀ i, Coefficient (τ i))
    (n : ℕ) (r : ℝ≥0) (ω : IBMSourceLaws.JointSample) (hr : r ∉ Ioc (τ 0) (τ n)) :
    timeSum τ a n r ω = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  apply indicator_of_notMem
  intro hm
  exact hr ⟨(hτ (Nat.zero_le i)).trans_lt hm.1,
    hm.2.trans (hτ (Nat.succ_le_of_lt (Finset.mem_range.mp hi)))⟩

theorem process_difference (τ σ : ℕ → ℝ≥0) (hτ : Monotone τ) (hσ : Monotone σ)
    (a : ∀ i, Coefficient (τ i)) (b : ∀ j, Coefficient (σ j)) (n m : ℕ)
    (hstart : τ 0 = σ 0) (hend : τ n = σ m) (r : ℝ≥0) (ω : IBMSourceLaws.JointSample) :
    process τ σ a b n m r ω = timeSum τ a n r ω - timeSum σ b m r ω := by
  rw [process_product, unit_cover τ hτ, unit_cover σ hσ, ← hstart, ← hend]
  by_cases hr : r ∈ Ioc (τ 0) (τ n)
  · simp only [indicator_of_mem hr, mul_one, one_mul]
  · have hrσ : r ∉ Ioc (σ 0) (σ m) := by simpa only [← hstart, ← hend] using hr
    rw [process_support τ hτ a n r ω hr, process_support σ hσ b m r ω hrσ]
    simp only [zero_mul, mul_zero, sub_self]

theorem process_predictable (τ σ : ℕ → ℝ≥0) (a : ∀ i, Coefficient (τ i))
    (b : ∀ j, Coefficient (σ j)) (n m : ℕ) :
    IsStronglyPredictable naturalFiltration (process τ σ a b n m) := by
  change StronglyMeasurable[naturalFiltration.predictable]
    (fun z : ℝ≥0 × IBMSourceLaws.JointSample => ∑ p ∈ cells τ σ n m,
      timeStep (left τ σ p) (right τ σ p) (coefficient τ σ a b p) z.1 z.2)
  exact Finset.stronglyMeasurable_fun_sum _ (fun p _ =>
    IBMIntrinsicPredictableProcess.timeStep_predictable _ _ _)

end OperatorDerivativeRewrite.Foundation.IBMGridIntersection
