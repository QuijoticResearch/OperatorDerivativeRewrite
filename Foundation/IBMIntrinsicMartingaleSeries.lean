import Foundation.IBMIntrinsicMartingaleRefinement
import Mathlib.Analysis.InnerProductSpace.Subspace

/-! Countable actual predictable stochastic sums in their martingale energy.
Convergence is strong scalar L2 on a fixed deterministic ordered time grid. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMIntrinsicMartingaleSeries
open IBMNaturalFiltrationObstruction IBMTimeAveragedObservable
open IBMIntrinsicMartingaleStep IBMIntrinsicMartingaleGrid IBMIntrinsicMartingaleRefinement
set_option backward.isDefEq.respectTransparency false

def incrementSpace (τ : ℕ → ℝ≥0) (i : ℕ) : Submodule ℝ JointL2 :=
  past (τ (i + 1)) ⊓ (past (τ i))ᗮ

theorem incrementSpaces_orthogonal (τ : ℕ → ℝ≥0) (hτ : Monotone τ) :
    OrthogonalFamily ℝ (fun i => incrementSpace τ i)
      (fun i => (incrementSpace τ i).subtypeₗᵢ) := by
  intro i j hij f g
  rcases lt_or_gt_of_ne hij with h | h
  · exact Submodule.inner_right_of_mem_orthogonal
      (f.property.1.mono (naturalFiltration.mono (hτ (Nat.succ_le_of_lt h)))) g.property.2
  · rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal
      (g.property.1.mono (naturalFiltration.mono (hτ (Nat.succ_le_of_lt h)))) f.property.2

def component (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (a : ∀ i, Coefficient (τ i))
    (i : ℕ) : incrementSpace τ i :=
  ⟨stepClass (τ i) (τ (i + 1)) (a i), stepClass_mem_past (hτ (Nat.le_succ i)) (a i),
    fun f hf => past_inner_step_zero (hτ (Nat.le_succ i)) (a i) f hf⟩

theorem steps_summable (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i))
    (ha : Summable (fun i => ‖stepClass (τ i) (τ (i + 1)) (a i)‖ ^ 2)) :
    Summable (fun i => stepClass (τ i) (τ (i + 1)) (a i)) :=
  ((incrementSpaces_orthogonal τ hτ).summable_iff_norm_sq_summable (component τ hτ a)).mpr ha

def integral (τ : ℕ → ℝ≥0) (a : ∀ i, Coefficient (τ i)) : JointL2 :=
  ∑' i, stepClass (τ i) (τ (i + 1)) (a i)

theorem sumClass_tendsto (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i))
    (ha : Summable (fun i => ‖stepClass (τ i) (τ (i + 1)) (a i)‖ ^ 2)) :
    Tendsto (sumClass τ a) atTop (𝓝 (integral τ a)) :=
  (steps_summable τ hτ a ha).hasSum.tendsto_sum_nat

theorem integral_energy (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i))
    (ha : Summable (fun i => ‖stepClass (τ i) (τ (i + 1)) (a i)‖ ^ 2)) :
    ‖integral τ a‖ ^ 2 = ∑' i, ‖stepClass (τ i) (τ (i + 1)) (a i)‖ ^ 2 := by
  have ht := (sumClass_tendsto τ hτ a ha).norm.pow 2
  simp_rw [energy_identity τ hτ a] at ht
  exact tendsto_nhds_unique ht ha.hasSum.tendsto_sum_nat

theorem bounded_energy_summable (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (T : ℝ≥0) (hT : ∀ i, τ i ≤ T) (a : ∀ i, Coefficient (τ i))
    (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ‖(a i).function ω‖ ≤ C) :
    Summable (fun i => ‖stepClass (τ i) (τ (i + 1)) (a i)‖ ^ 2) := by
  apply summable_of_sum_range_le (fun i => sq_nonneg _) (c := C ^ 2 * (2 * (T : ℝ) ^ 2))
  intro n
  rw [← energy_identity τ hτ a n]
  exact (grid_energy_bound τ hτ a C hC ha n).trans
    (mul_le_mul_of_nonneg_left (by nlinarith [show (τ n : ℝ) ≤ T from hT n,
      (τ n).coe_nonneg, T.coe_nonneg]) (sq_nonneg C))

theorem bounded_integral_bound (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (T : ℝ≥0) (hT : ∀ i, τ i ≤ T) (a : ∀ i, Coefficient (τ i))
    (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ‖(a i).function ω‖ ≤ C) :
    ‖integral τ a‖ ^ 2 ≤ C ^ 2 * (2 * (T : ℝ) ^ 2) := by
  rw [integral_energy τ hτ a (bounded_energy_summable τ hτ T hT a C hC ha)]
  apply Real.tsum_le_of_sum_range_le (fun i => sq_nonneg _)
  intro n
  rw [← energy_identity τ hτ a n]
  exact (grid_energy_bound τ hτ a C hC ha n).trans
    (mul_le_mul_of_nonneg_left (by nlinarith [show (τ n : ℝ) ≤ T from hT n,
      (τ n).coe_nonneg, T.coe_nonneg]) (sq_nonneg C))

theorem integral_mem_past (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (T : ℝ≥0) (hT : ∀ i, τ i ≤ T) (a : ∀ i, Coefficient (τ i))
    (ha : Summable (fun i => ‖stepClass (τ i) (τ (i + 1)) (a i)‖ ^ 2)) :
    integral τ a ∈ past T := by
  apply (past_closed T).mem_of_tendsto (sumClass_tendsto τ hτ a ha)
  exact Eventually.of_forall fun n =>
    (sumClass_mem_past τ hτ a n).mono (naturalFiltration.mono (hT n))

theorem sumClass_condExp (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i)) {m n : ℕ} (hmn : m ≤ n) :
    (condExpL2 ℝ ℝ (naturalFiltration.le (τ m)) (sumClass τ a n) : JointL2) = sumClass τ a m := by
  have he : (condExpL2 ℝ ℝ (naturalFiltration.le (τ m)) (sumClass τ a n) : JointL2)
      =ᵐ[IBMSourceLaws.jointMeasure]
        IBMSourceLaws.jointMeasure[sumClass τ a n | naturalFiltration (τ m)] := by
    simpa only [Lp.toLp_coeFn] using (Lp.memLp (sumClass τ a n)).condExpL2_ae_eq_condExp
      (𝕜 := ℝ) (naturalFiltration.le (τ m))
  apply Lp.ext
  exact he.trans ((condExp_congr_ae (sumClass_ae τ a n)).trans
    (((sum_martingale τ hτ a).condExp_ae_eq hmn).trans (sumClass_ae τ a m).symm))

/-- The limiting integral closes the actual grid martingale in strong L2. -/
theorem integral_condExp (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i))
    (ha : Summable (fun i => ‖stepClass (τ i) (τ (i + 1)) (a i)‖ ^ 2)) (m : ℕ) :
    (condExpL2 ℝ ℝ (naturalFiltration.le (τ m)) (integral τ a) : JointL2) = sumClass τ a m := by
  have ht := (((past (τ m)).subtypeL.comp
    (condExpL2 ℝ ℝ (naturalFiltration.le (τ m)))).continuous.tendsto (integral τ a)).comp
      (sumClass_tendsto τ hτ a ha)
  have he : ∀ᶠ n in atTop,
      (condExpL2 ℝ ℝ (naturalFiltration.le (τ m)) (sumClass τ a n) : JointL2) = sumClass τ a m :=
    eventually_atTop.mpr ⟨m, fun n hn => sumClass_condExp τ hτ a hn⟩
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he))

theorem integral_actual_condExp (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i))
    (ha : Summable (fun i => ‖stepClass (τ i) (τ (i + 1)) (a i)‖ ^ 2)) (m : ℕ) :
    IBMSourceLaws.jointMeasure[integral τ a | naturalFiltration (τ m)]
      =ᵐ[IBMSourceLaws.jointMeasure] sum τ a m := by
  have he : (condExpL2 ℝ ℝ (naturalFiltration.le (τ m)) (integral τ a) : JointL2)
      =ᵐ[IBMSourceLaws.jointMeasure]
        IBMSourceLaws.jointMeasure[integral τ a | naturalFiltration (τ m)] := by
    simpa only [Lp.toLp_coeFn] using (Lp.memLp (integral τ a)).condExpL2_ae_eq_condExp
      (𝕜 := ℝ) (naturalFiltration.le (τ m))
  rw [integral_condExp τ hτ a ha m] at he
  exact he.symm.trans (sumClass_ae τ a m)

end OperatorDerivativeRewrite.Foundation.IBMIntrinsicMartingaleSeries
