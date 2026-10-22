import Foundation.IBMTerminalPredictableStep

/-! Actual finite-grid random predictable stochastic sums for every terminal
IBM martingale, with exact weighted energy and existing predictable processes. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMTerminalPredictableGrid
open IBMTimeAveragedObservable IBMNaturalFiltrationObstruction IBMRawObservedMartingale
open IBMIntrinsicMartingaleStep (Coefficient)
open IBMTerminalPredictableStep
set_option backward.isDefEq.respectTransparency false

def sum (F : JointL2) (τ : ℕ → ℝ≥0) (a : ∀ i, Coefficient (τ i)) (n : ℕ) :
    IBMSourceLaws.JointSample → ℝ :=
  ∑ i ∈ Finset.range n, step F (τ i) (τ (i + 1)) (a i)

def sumClass (F : JointL2) (τ : ℕ → ℝ≥0) (a : ∀ i, Coefficient (τ i)) (n : ℕ) : JointL2 :=
  ∑ i ∈ Finset.range n, stepClass F (τ i) (τ (i + 1)) (a i)

theorem sumClass_ae (F : JointL2) (τ : ℕ → ℝ≥0) (a : ∀ i, Coefficient (τ i)) (n : ℕ) :
    sumClass F τ a n =ᵐ[IBMSourceLaws.jointMeasure] sum F τ a n := by
  induction n with
  | zero => simpa [sumClass, sum] using (Lp.coeFn_zero ℝ 2 IBMSourceLaws.jointMeasure)
  | succ n ih =>
    unfold sumClass sum at *
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    exact (Lp.coeFn_add _ _).trans (ih.add (stepClass_ae F (τ n) (τ (n + 1)) (a n)))

theorem sumClass_mem_past (F : JointL2) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i)) (n : ℕ) : sumClass F τ a n ∈ past (τ n) := by
  apply Submodule.sum_mem
  intro i hi
  exact (stepClass_mem_past F (hτ (Nat.le_succ i)) (a i)).mono
    (naturalFiltration.mono (hτ (Nat.succ_le_of_lt (Finset.mem_range.mp hi))))

theorem sum_martingale (F : JointL2) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i)) :
    Martingale (sum F τ a) (IBMIntrinsicMartingaleGrid.gridFiltration τ hτ)
      IBMSourceLaws.jointMeasure := by
  apply martingale_of_condExp_sub_eq_zero_nat
  · intro n
    unfold sum
    apply Finset.stronglyMeasurable_sum
    intro i hi
    have hin : i ≤ n := (Finset.mem_range.mp hi).le
    have hsn : i + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    exact ((a i).adapted.mono (naturalFiltration.mono (hτ hin))).mul
      ((((raw_martingale F).stronglyAdapted (τ (i + 1))).mono
        (naturalFiltration.mono (hτ hsn))).sub
        (((raw_martingale F).stronglyAdapted (τ i)).mono (naturalFiltration.mono (hτ hin))))
  · intro n
    exact ((Lp.memLp (sumClass F τ a n)).ae_eq (sumClass_ae F τ a n)).integrable (by norm_num)
  · intro n
    have hs : sum F τ a (n + 1) - sum F τ a n = step F (τ n) (τ (n + 1)) (a n) := by
      funext ω
      simp [sum, Finset.sum_range_succ]
    rw [hs]
    exact step_condExp F (hτ (Nat.le_succ n)) (a n)

theorem energy_identity (F : JointL2) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i)) (n : ℕ) :
    ‖sumClass F τ a n‖ ^ 2 =
      ∑ i ∈ Finset.range n, ‖stepClass F (τ i) (τ (i + 1)) (a i)‖ ^ 2 := by
  induction n with
  | zero => simp [sumClass]
  | succ n ih =>
    have ho := past_inner_step_zero F (hτ (Nat.le_succ n)) (a n)
      (sumClass F τ a n) (sumClass_mem_past F τ hτ a n)
    have hs : sumClass F τ a (n + 1) = sumClass F τ a n +
        stepClass F (τ n) (τ (n + 1)) (a n) := Finset.sum_range_succ _ _
    rw [hs, norm_add_sq_real, ho, ih, Finset.sum_range_succ]
    ring

theorem actual_energy_identity (F : JointL2) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i)) (n : ℕ) :
    (∫ ω, (sum F τ a n ω) ^ 2 ∂IBMSourceLaws.jointMeasure) =
      ∑ i ∈ Finset.range n, ∫ ω, (a i).function ω ^ 2 *
        increment F (τ i) (τ (i + 1)) ω ^ 2 ∂IBMSourceLaws.jointMeasure := by
  calc
    _ = ‖sumClass F τ a n‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [sumClass_ae F τ a n] with ω hω
      rw [hω, Real.inner_apply, pow_two]
    _ = _ := by rw [energy_identity F τ hτ]; simp_rw [step_energy]

theorem integrand_predictable (τ : ℕ → ℝ≥0) (a : ∀ i, Coefficient (τ i)) (n : ℕ) :
    IsStronglyPredictable naturalFiltration (IBMIntrinsicPredictableProcess.timeSum τ a n) :=
  IBMIntrinsicPredictableProcess.timeSum_predictable τ a n

theorem unit_sum (F : JointL2) (τ : ℕ → ℝ≥0) (n : ℕ) :
    sum F τ (fun i => IBMIntrinsicMartingaleRefinement.constant (τ i) 1) n =
      rawValue F (τ n) - rawValue F (τ 0) := by
  funext ω
  induction n with
  | zero => simp [sum]
  | succ n ih =>
    simp only [sum, Finset.sum_range_succ, Pi.add_apply] at *
    rw [ih]
    simp only [step, increment, IBMIntrinsicMartingaleRefinement.constant,
      Pi.mul_apply, Pi.sub_apply, one_mul]
    ring

theorem observed_unit_recovery (τ : ℕ → ℝ≥0) (n : ℕ) (h₀ : τ 0 = 0) (h₁ : τ n = 1) :
    sum (IBMDeterministicRangeObstruction.observed 1) τ
      (fun i => IBMIntrinsicMartingaleRefinement.constant (τ i) 1) n
        =ᵐ[IBMSourceLaws.jointMeasure] IBMConstructedSources.ibmValue 1 := by
  rw [unit_sum, h₀, h₁]
  filter_upwards [observed_raw_terminal le_rfl, observed_raw_origin] with ω ht hzero
  simp only [Pi.sub_apply, ht, hzero, sub_zero]

theorem quadratic_sum_agreement (τ : ℕ → ℝ≥0) (a : ∀ i, Coefficient (τ i)) (n : ℕ)
    (H : ℝ≥0) (hH : ∀ i ≤ n, τ i ≤ H) :
    sumClass (IBMIntrinsicQuadraticMartingale.valueClass H : JointL2) τ a n =
      IBMIntrinsicMartingaleGrid.sumClass τ a n := by
  unfold sumClass IBMIntrinsicMartingaleGrid.sumClass
  apply Finset.sum_congr rfl
  intro i hi
  exact quadratic_agreement (hH i (Finset.mem_range.mp hi).le)
    (hH (i + 1) (Nat.succ_le_of_lt (Finset.mem_range.mp hi))) (a i)

end OperatorDerivativeRewrite.Foundation.IBMTerminalPredictableGrid
