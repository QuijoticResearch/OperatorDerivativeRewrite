import Foundation.IBMTerminalIntegralEnergy
import Foundation.IBMIntrinsicMartingaleSeries

/-! Strong L2 countable-grid integration for actual IBM terminal martingales.
The integral requires its actual stochastic energy domain as an argument. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMTerminalPredictableSeries
open IBMNaturalFiltrationObstruction IBMTimeAveragedObservable IBMRawObservedMartingale
open IBMIntrinsicMartingaleStep (Coefficient)
open IBMIntrinsicMartingaleRefinement (constant)
open IBMTerminalPredictableStep IBMTerminalPredictableGrid IBMTerminalIntegralEnergy
open IBMIntrinsicMartingaleSeries (incrementSpace incrementSpaces_orthogonal)
set_option backward.isDefEq.respectTransparency false

def component (F : JointL2) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i)) (i : ℕ) : incrementSpace τ i :=
  ⟨stepClass F (τ i) (τ (i + 1)) (a i),
    stepClass_mem_past F (hτ (Nat.le_succ i)) (a i),
    fun f hf => past_inner_step_zero F (hτ (Nat.le_succ i)) (a i) f hf⟩

theorem steps_summable (F : JointL2) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i))
    (ha : Summable (fun i => ‖stepClass F (τ i) (τ (i + 1)) (a i)‖ ^ 2)) :
    Summable (fun i => stepClass F (τ i) (τ (i + 1)) (a i)) :=
  ((incrementSpaces_orthogonal τ hτ).summable_iff_norm_sq_summable
    (component F τ hτ a)).mpr ha

def integral (F : JointL2) (τ : ℕ → ℝ≥0) (_hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i))
    (_ha : Summable (fun i => ‖stepClass F (τ i) (τ (i + 1)) (a i)‖ ^ 2)) : JointL2 :=
  ∑' i, stepClass F (τ i) (τ (i + 1)) (a i)

theorem sumClass_tendsto (F : JointL2) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i))
    (ha : Summable (fun i => ‖stepClass F (τ i) (τ (i + 1)) (a i)‖ ^ 2)) :
    Tendsto (sumClass F τ a) atTop (𝓝 (integral F τ hτ a ha)) :=
  (steps_summable F τ hτ a ha).hasSum.tendsto_sum_nat

theorem integral_energy (F : JointL2) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i))
    (ha : Summable (fun i => ‖stepClass F (τ i) (τ (i + 1)) (a i)‖ ^ 2)) :
    ‖integral F τ hτ a ha‖ ^ 2 =
      ∑' i, ‖stepClass F (τ i) (τ (i + 1)) (a i)‖ ^ 2 := by
  have ht := (sumClass_tendsto F τ hτ a ha).norm.pow 2
  simp_rw [energy_identity F τ hτ a] at ht
  exact tendsto_nhds_unique ht ha.hasSum.tendsto_sum_nat

theorem bounded_integral_bound (F : JointL2) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i)) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ‖(a i).function ω‖ ≤ C) :
    ‖integral F τ hτ a (bounded_energy_summable F τ hτ a C hC ha)‖ ^ 2 ≤ C ^ 2 * ‖F‖ ^ 2 := by
  rw [integral_energy]
  apply Real.tsum_le_of_sum_range_le (fun i => sq_nonneg _)
  intro n
  rw [← energy_identity F τ hτ a n]
  exact grid_energy_bound F τ hτ a C hC ha n

theorem integral_mem_past (F : JointL2) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (T : ℝ≥0) (hT : ∀ i, τ i ≤ T) (a : ∀ i, Coefficient (τ i))
    (ha : Summable (fun i => ‖stepClass F (τ i) (τ (i + 1)) (a i)‖ ^ 2)) :
    integral F τ hτ a ha ∈ past T := by
  apply (past_closed T).mem_of_tendsto (sumClass_tendsto F τ hτ a ha)
  exact Eventually.of_forall fun n =>
    (sumClass_mem_past F τ hτ a n).mono (naturalFiltration.mono (hT n))

theorem sumClass_condExp (F : JointL2) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i)) {m n : ℕ} (hmn : m ≤ n) :
    (condExpL2 ℝ ℝ (naturalFiltration.le (τ m)) (sumClass F τ a n) : JointL2) =
      sumClass F τ a m := by
  have he : (condExpL2 ℝ ℝ (naturalFiltration.le (τ m)) (sumClass F τ a n) : JointL2)
      =ᵐ[IBMSourceLaws.jointMeasure]
        IBMSourceLaws.jointMeasure[sumClass F τ a n | naturalFiltration (τ m)] := by
    simpa only [Lp.toLp_coeFn] using (Lp.memLp (sumClass F τ a n)).condExpL2_ae_eq_condExp
      (𝕜 := ℝ) (naturalFiltration.le (τ m))
  apply Lp.ext
  exact he.trans ((condExp_congr_ae (sumClass_ae F τ a n)).trans
    (((sum_martingale F τ hτ a).condExp_ae_eq hmn).trans (sumClass_ae F τ a m).symm))

theorem integral_condExp (F : JointL2) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i))
    (ha : Summable (fun i => ‖stepClass F (τ i) (τ (i + 1)) (a i)‖ ^ 2)) (m : ℕ) :
    (condExpL2 ℝ ℝ (naturalFiltration.le (τ m)) (integral F τ hτ a ha) : JointL2) =
      sumClass F τ a m := by
  have ht := (((past (τ m)).subtypeL.comp
    (condExpL2 ℝ ℝ (naturalFiltration.le (τ m)))).continuous.tendsto
      (integral F τ hτ a ha)).comp (sumClass_tendsto F τ hτ a ha)
  have he : ∀ᶠ n in atTop,
      (condExpL2 ℝ ℝ (naturalFiltration.le (τ m)) (sumClass F τ a n) : JointL2) =
        sumClass F τ a m :=
    eventually_atTop.mpr ⟨m, fun n hn => sumClass_condExp F τ hτ a hn⟩
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he))

theorem integral_actual_condExp (F : JointL2) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i))
    (ha : Summable (fun i => ‖stepClass F (τ i) (τ (i + 1)) (a i)‖ ^ 2)) (m : ℕ) :
    IBMSourceLaws.jointMeasure[integral F τ hτ a ha | naturalFiltration (τ m)]
      =ᵐ[IBMSourceLaws.jointMeasure] sum F τ a m := by
  have he : (condExpL2 ℝ ℝ (naturalFiltration.le (τ m)) (integral F τ hτ a ha) : JointL2)
      =ᵐ[IBMSourceLaws.jointMeasure]
        IBMSourceLaws.jointMeasure[integral F τ hτ a ha | naturalFiltration (τ m)] := by
    simpa only [Lp.toLp_coeFn] using (Lp.memLp (integral F τ hτ a ha)).condExpL2_ae_eq_condExp
      (𝕜 := ℝ) (naturalFiltration.le (τ m))
  rw [integral_condExp F τ hτ a ha m] at he
  exact he.symm.trans (sumClass_ae F τ a m)

theorem unit_integral (F : JointL2) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (T : ℝ≥0) (hT : ∀ i, τ i ≤ T) (hlim : Tendsto τ atTop (𝓝 T))
    (ha : Summable (fun i =>
      ‖stepClass F (τ i) (τ (i + 1)) (constant (τ i) 1)‖ ^ 2)) :
    integral F τ hτ (fun i => constant (τ i) 1) ha = rawClass F T - rawClass F (τ 0) := by
  have ht := (IBMCofinalPast.projection_tendsto τ hτ T hT hlim F).sub_const
    (rawClass F (τ 0))
  change Tendsto (fun n => rawClass F (τ n) - rawClass F (τ 0)) atTop
    (𝓝 (rawClass F T - rawClass F (τ 0))) at ht
  simp_rw [← unit_sumClass F τ] at ht
  exact tendsto_nhds_unique (sumClass_tendsto F τ hτ _ ha) ht

theorem unit_energy_summable (F : JointL2) (τ : ℕ → ℝ≥0) (hτ : Monotone τ) :
    Summable (fun i =>
      ‖stepClass F (τ i) (τ (i + 1)) (constant (τ i) 1)‖ ^ 2) := by
  apply bounded_energy_summable F τ hτ _ 1 zero_le_one
  intro i
  filter_upwards [] with ω
  simp only [constant, norm_one, le_refl]

theorem centered_unit_reconstruction (F : JointL2) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (T : ℝ≥0) (hT : ∀ i, τ i ≤ T) (hlim : Tendsto τ atTop (𝓝 T))
    (hzero : τ 0 = 0) (hF : F ∈ past T)
    (hmean : (∫ ω, F ω ∂IBMSourceLaws.jointMeasure) = 0) :
    integral F τ hτ (fun i => constant (τ i) 1) (unit_energy_summable F τ hτ) = F := by
  rw [unit_integral F τ hτ T hT hlim, hzero, raw_origin_class F hmean,
    raw_terminal_class F hF le_rfl, sub_zero]

theorem observed_unit_reconstruction (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hT : ∀ i, τ i ≤ 1) (hlim : Tendsto τ atTop (𝓝 1)) (hzero : τ 0 = 0) :
    integral (IBMDeterministicRangeObstruction.observed 1) τ hτ
      (fun i => constant (τ i) 1)
      (unit_energy_summable (IBMDeterministicRangeObstruction.observed 1) τ hτ)
      =ᵐ[IBMSourceLaws.jointMeasure] IBMConstructedSources.ibmValue 1 := by
  rw [centered_unit_reconstruction _ τ hτ 1 hT hlim hzero
    (IBMDeterministicRangeObstruction.observed_mem_past 1)
    (IBMDeterministicRangeObstruction.observed_centered 1)]
  exact IBMDeterministicRangeObstruction.observed_ae 1

end OperatorDerivativeRewrite.Foundation.IBMTerminalPredictableSeries
