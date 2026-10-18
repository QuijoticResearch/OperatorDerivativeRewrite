import Foundation.HigherHeatPolynomialPathDomain

/-! Concrete retained-cell families and signed polynomial projections on dyadic tails. -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.HigherHeatDyadicConditioning
open HigherHeatPolynomialCylinders HigherHeatConditionalRefinement HigherHeatPolynomialRefinement
  PureOrderPolynomialConditioning HigherHeatGridDoubling HigherHeatBlockCoarsening

def cells (b : ℕ) (S : Finset (Fin (size b))) (n : ℕ) (h : b ≤ n) : Finset (Fin (size n)) :=
  Nat.leRecOn h (@fun k A => pastCells (@pairBlock (size k)) A) S

theorem cells_self (b : ℕ) (S : Finset (Fin (size b))) : cells b S b le_rfl = S := by
  unfold cells
  exact Nat.leRecOn_self (C := fun k => Finset (Fin (size k)))
    (next := @fun k A => pastCells (@pairBlock (size k)) A) S

theorem cells_succ (b : ℕ) (S : Finset (Fin (size b))) (n : ℕ) (h : b ≤ n) :
    cells b S (n+1) (h.trans (Nat.le_succ n)) = pastCells (@pairBlock (size n)) (cells b S n h) :=
  by
    unfold cells
    exact Nat.leRecOn_succ (C := fun k => Finset (Fin (size k))) h
      (next := @fun k A => pastCells (@pairBlock (size k)) A) S

open Classical in
theorem cells_inter (b : ℕ) (S U : Finset (Fin (size b))) (n : ℕ) (h : b ≤ n) :
    cells b (S ∩ U) n h = cells b S n h ∩ cells b U n h := by
  classical
  induction n, h using Nat.le_induction with
  | base => rw [cells_self, cells_self, cells_self]
  | succ n hn ih =>
    rw [cells_succ b (S ∩ U) n hn, cells_succ b S n hn, cells_succ b U n hn, ih]
    change pastCells (@pairBlock (size n)) (cells b S n hn ∩ cells b U n hn) =
      (pastCells (@pairBlock (size n)) (cells b S n hn) ∩
        pastCells (@pairBlock (size n)) (cells b U n hn) : Finset (Fin (2*size n)))
    ext j
    simp [pastCells]

def localProjection (m : ℕ) (T : ℝ≥0) (n : ℕ) (A : Finset (Fin (size n))) :
    Test n →ₗ[ℝ] Test n :=
  conditioning (2*m) (parameters m (fun _ => HigherHeatDyadicLaws.duration T n)) A

theorem localProjection_step (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (A : Finset (Fin (size n))) (P : Test n) :
    localProjection m T (n+1) (pastCells (@pairBlock (size n)) A) (step n P) =
      step n (localProjection m T n A P) := by
  have he := conditional_refinement m hm
    (fun _ : Fin (2*size n) => HigherHeatDyadicLaws.duration T (n+1))
    (fun _ => HigherHeatDyadicLaws.duration_pos T hT (n+1))
    pairBlock (pairBlock_surjective (size n)) A P
  have hs : blockTimes pairBlock
      (fun _ : Fin (2*size n) => HigherHeatDyadicLaws.duration T (n+1)) =
      (fun _ : Fin (size n) => HigherHeatDyadicLaws.duration T n) := by
    funext i
    rw [pair_times, HigherHeatDyadicLaws.duration_halves]
  change conditioning (2*m)
      (parameters m (fun _ : Fin (2*size n) => HigherHeatDyadicLaws.duration T (n+1)))
      (pastCells pairBlock A) (pullback pairBlock P) =
    pullback pairBlock (conditioning (2*m)
      (parameters m (fun _ : Fin (size n) => HigherHeatDyadicLaws.duration T n)) A P)
  simpa only [hs] using he

theorem localProjection_transfer (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (S : Finset (Fin (size b))) (i j : ℕ) (hi : b ≤ i) (hij : i ≤ j) (P : Test i) :
    localProjection m T j (cells b S j (hi.trans hij)) (transfer i j hij P) =
      transfer i j hij (localProjection m T i (cells b S i hi) P) := by
  induction j, hij using Nat.le_induction with
  | base => simp only [transfer_self]
  | succ j hj ih =>
    calc
      _ = localProjection m T (j+1) (pastCells (@pairBlock (size j)) (cells b S j (hi.trans hj)))
          (step j (transfer i j hj P)) := by
        exact congrArg₂
          (fun (A : Finset (Fin (size (j+1)))) (Q : Test (j+1)) => localProjection m T (j+1) A Q)
          (cells_succ b S j (hi.trans hj)) (transfer_succ i j hj P)
      _ = step j (localProjection m T j (cells b S j (hi.trans hj)) (transfer i j hj P)) :=
        localProjection_step m hm T hT j _ _
      _ = step j (transfer i j hj (localProjection m T i (cells b S i hi) P)) :=
        congrArg (fun Q => step j Q) ih
      _ = _ := (transfer_succ i j hj (localProjection m T i (cells b S i hi) P)).symm


theorem localProjection_idempotent (m : ℕ) (T : ℝ≥0) (n : ℕ)
    (A : Finset (Fin (size n))) (P : Test n) :
    localProjection m T n A (localProjection m T n A P) = localProjection m T n A P :=
  conditioning_idempotent _ _ _ P

theorem conditioning_tower_set {ι : Type*} [Fintype ι] (p : ℕ) (a : ι → ℝ)
    (A B C : Finset ι) (hC : ∀ i, i ∈ C ↔ i ∈ A ∧ i ∈ B) (P : MvPolynomial ι ℝ) :
    conditioning p a A (conditioning p a B P) = conditioning p a C P := by
  classical
  have hc : C = A ∩ B := by
    ext i
    simpa only [Finset.mem_inter] using hC i
  rw [hc]
  exact conditioning_tower p a A B P

open Classical in
theorem localProjection_tower (m : ℕ) (T : ℝ≥0) (n : ℕ)
    (A B : Finset (Fin (size n))) (P : Test n) :
    localProjection m T n A (localProjection m T n B P) = localProjection m T n (A ∩ B) P :=
  conditioning_tower_set (2*m)
    (parameters m (fun _ : Fin (size n) => HigherHeatDyadicLaws.duration T n))
    A B (A ∩ B) (by intro i; simp only [Finset.mem_inter]) P

theorem localProjection_expectation (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (A : Finset (Fin (size n))) (P : Test n) :
    expectation m hm T hT n (localProjection m T n A P) = expectation m hm T hT n P :=
  actual_mean_conditioning m hm _ _ A P


theorem localProjection_C (m : ℕ) (T : ℝ≥0) (n : ℕ)
    (A : Finset (Fin (size n))) (c : ℝ) :
    localProjection m T n A (MvPolynomial.C c) = MvPolynomial.C c := by
  have he := conditioning_supported_monomial (2*m)
    (parameters m (fun _ : Fin (size n) => HigherHeatDyadicLaws.duration T n)) A
    (0 : Fin (size n) →₀ ℕ) c (by intro i _; rfl)
  simpa only [localProjection, MvPolynomial.monomial_zero'] using he

def initialPast (n q : ℕ) : Finset (Fin (size n)) := Finset.univ.filter (fun i => i.val < q)

theorem pastCells_initialPast (n q : ℕ) :
    pastCells (@pairBlock (size n)) (initialPast n q) = initialPast (n+1) (2*q) := by
  classical
  ext j
  have hl : j ∈ pastCells (@pairBlock (size n)) (initialPast n q) ↔ j.val/2 < q := by
    simp [pastCells, initialPast, pairBlock]
  have hr : j ∈ initialPast (n+1) (2*q) ↔ j.val < 2*q := by
    change j ∈ (Finset.univ.filter (fun i : Fin (2*size n) => i.val < 2*q)) ↔ j.val < 2*q
    constructor
    · intro hj
      exact (Finset.mem_filter.mp hj).2
    · intro hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
  have hquot : j.val/2 < q ↔ j.val < 2*q := by omega
  exact hl.trans (hquot.trans hr.symm)


theorem cells_initialPast (b q n : ℕ) (h : b ≤ n) :
    cells b (initialPast b q) n h = initialPast n (q * 2^(n-b)) := by
  induction n, h using Nat.le_induction with
  | base => simp only [cells_self, Nat.sub_self, pow_zero, mul_one]
  | succ n hn ih =>
    rw [cells_succ b (initialPast b q) n hn, ih, pastCells_initialPast]
    have he : n+1-b = (n-b)+1 := by omega
    rw [he, pow_succ]
    congr 1
    ring



theorem cells_refine_base (b : ℕ) (S : Finset (Fin (size b))) (n : ℕ) (hn : b+1 ≤ n) :
    cells b S n ((Nat.le_succ b).trans hn) =
      cells (b+1) (pastCells (@pairBlock (size b)) S) n hn := by
  unfold cells
  have he := Nat.leRecOn_trans (C := fun k => Finset (Fin (size k)))
    (next := @fun k A => pastCells (@pairBlock (size k)) A) (Nat.le_succ b) hn S
  simpa only [Nat.leRecOn_succ'] using he


end OperatorDerivativeRewrite.Foundation.HigherHeatDyadicConditioning
