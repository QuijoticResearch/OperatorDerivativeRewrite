import Foundation.IBMIntrinsicMartingaleStep

/-! Genuine finite-grid stochastic sums and their L2 energy identity for the
constructed IBM-natural martingale. The energy is not elapsed Brownian time. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMIntrinsicMartingaleGrid
open IBMNaturalFiltrationObstruction IBMTimeAveragedObservable
open IBMIntrinsicQuadraticMartingale IBMIntrinsicMartingaleStep
set_option backward.isDefEq.respectTransparency false

def sum (τ : ℕ → ℝ≥0) (a : ∀ i, Coefficient (τ i)) (n : ℕ) :
    IBMSourceLaws.JointSample → ℝ :=
  ∑ i ∈ Finset.range n, step (τ i) (τ (i + 1)) (a i)

def sumClass (τ : ℕ → ℝ≥0) (a : ∀ i, Coefficient (τ i)) (n : ℕ) : JointL2 :=
  ∑ i ∈ Finset.range n, stepClass (τ i) (τ (i + 1)) (a i)

theorem sumClass_ae (τ : ℕ → ℝ≥0) (a : ∀ i, Coefficient (τ i)) (n : ℕ) :
    sumClass τ a n =ᵐ[IBMSourceLaws.jointMeasure] sum τ a n := by
  classical
  induction n with
  | zero => simpa [sumClass, sum] using (Lp.coeFn_zero ℝ 2 IBMSourceLaws.jointMeasure)
  | succ n ih =>
    unfold sumClass sum at *
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    exact (Lp.coeFn_add _ _).trans (ih.add (stepClass_ae (τ n) (τ (n + 1)) (a n)))

theorem sum_memLp (τ : ℕ → ℝ≥0) (a : ∀ i, Coefficient (τ i)) (n : ℕ) :
    MemLp (sum τ a n) 2 IBMSourceLaws.jointMeasure :=
  (Lp.memLp (sumClass τ a n)).ae_eq (sumClass_ae τ a n)

theorem sumClass_mem_past (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i)) (n : ℕ) : sumClass τ a n ∈ past (τ n) := by
  apply Submodule.sum_mem
  intro i hi
  exact (stepClass_mem_past (hτ (Nat.le_succ i)) (a i)).mono
    (naturalFiltration.mono (hτ (Nat.succ_le_of_lt (Finset.mem_range.mp hi))))

def gridFiltration (τ : ℕ → ℝ≥0) (hτ : Monotone τ) :
    Filtration ℕ (inferInstance : MeasurableSpace IBMSourceLaws.JointSample) where
  seq n := naturalFiltration (τ n)
  mono' _ _ h := naturalFiltration.mono (hτ h)
  le' n := naturalFiltration.le (τ n)

/-- The actual accumulated stochastic sums are themselves a genuine martingale
in the sampled full IBM past, not merely centered terminal variables. -/
theorem sum_martingale (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i)) :
    Martingale (sum τ a) (gridFiltration τ hτ) IBMSourceLaws.jointMeasure := by
  apply martingale_of_condExp_sub_eq_zero_nat
  · intro n
    unfold sum
    apply Finset.stronglyMeasurable_sum
    intro i hi
    have hin : i ≤ n := (Finset.mem_range.mp hi).le
    have hsn : i + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    exact ((a i).adapted.mono (naturalFiltration.mono (hτ hin))).mul
      (((actual_martingale.stronglyAdapted (τ (i + 1))).mono
        (naturalFiltration.mono (hτ hsn))).sub
        ((actual_martingale.stronglyAdapted (τ i)).mono (naturalFiltration.mono (hτ hin))))
  · intro n
    exact (sum_memLp τ a n).integrable (by norm_num)
  · intro n
    have hs : sum τ a (n + 1) - sum τ a n = step (τ n) (τ (n + 1)) (a n) := by
      funext ω
      simp [sum, Finset.sum_range_succ]
    rw [hs]
    exact step_condExp (hτ (Nat.le_succ n)) (a n)

theorem energy_identity (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i)) (n : ℕ) :
    ‖sumClass τ a n‖ ^ 2 =
      ∑ i ∈ Finset.range n, ‖stepClass (τ i) (τ (i + 1)) (a i)‖ ^ 2 := by
  induction n with
  | zero => simp [sumClass]
  | succ n ih =>
    have ho : inner ℝ (sumClass τ a n) (stepClass (τ n) (τ (n + 1)) (a n)) = 0 := by
      exact past_inner_step_zero (hτ (Nat.le_succ n)) (a n) _ (sumClass_mem_past τ hτ a n)
    have hs : sumClass τ a (n + 1) =
        sumClass τ a n + stepClass (τ n) (τ (n + 1)) (a n) :=
      Finset.sum_range_succ _ _
    rw [hs, norm_add_sq_real, ho, ih, Finset.sum_range_succ]
    ring

theorem step_energy (s t : ℝ≥0) (a : Coefficient s) :
    ‖stepClass s t a‖ ^ 2 =
      ∫ ω, (a.function ω) ^ 2 * (increment s t ω) ^ 2 ∂IBMSourceLaws.jointMeasure := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [stepClass_ae s t a] with ω hω
  rw [hω, Real.inner_apply]
  change (a.function ω * increment s t ω) * (a.function ω * increment s t ω) = _
  ring

/-- The actual stochastic-sum isometry retains its random increment energies.
No Brownian variance or independence normalization is inserted. -/
theorem actual_energy_identity (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i)) (n : ℕ) :
    (∫ ω, (sum τ a n ω) ^ 2 ∂IBMSourceLaws.jointMeasure) =
      ∑ i ∈ Finset.range n,
        ∫ ω, (a i).function ω ^ 2 * increment (τ i) (τ (i + 1)) ω ^ 2
          ∂IBMSourceLaws.jointMeasure := by
  calc
    _ = ‖sumClass τ a n‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [sumClass_ae τ a n] with ω hω
      rw [hω, Real.inner_apply, pow_two]
    _ = _ := by rw [energy_identity τ hτ a n]; simp_rw [step_energy]

end OperatorDerivativeRewrite.Foundation.IBMIntrinsicMartingaleGrid
