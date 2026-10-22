import Foundation.IBMFiniteIntervalIdentification

/-! Actual time-process control on finite disjoint martingale intervals.
The terminal-norm estimate uses no deterministic variance factorization. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMDisjointProcessControl
open IBMTimeAveragedObservable IBMNaturalFiltrationObstruction IBMRawObservedMartingale
open IBMTerminalPredictableStep IBMTerminalIntegralEnergy
open IBMIntrinsicMartingaleStep (Coefficient)
open IBMIntrinsicMartingaleRefinement (constant)
set_option backward.isDefEq.respectTransparency false

theorem finite_energy {ι : Type*} (F : JointL2) (I : Finset ι)
    (s t : ι → ℝ≥0) (a : ∀ i, Coefficient (s i)) (hst : ∀ i ∈ I, s i ≤ t i)
    (hd : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → t i ≤ s j ∨ t j ≤ s i) :
    ‖∑ i ∈ I, stepClass F (s i) (t i) (a i)‖ ^ 2 =
      ∑ i ∈ I, ‖stepClass F (s i) (t i) (a i)‖ ^ 2 := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    have ho : inner ℝ (stepClass F (s i) (t i) (a i))
        (∑ j ∈ I, stepClass F (s j) (t j) (a j)) = 0 := by
      rw [inner_sum]
      apply Finset.sum_eq_zero
      intro j hj
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      rcases hd i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) hij with h | h
      · exact disjoint_steps_orthogonal F (hst i (Finset.mem_insert_self _ _)) h
          (hst j (Finset.mem_insert_of_mem hj)) (a i) (a j)
      · rw [real_inner_comm]
        exact disjoint_steps_orthogonal F (hst j (Finset.mem_insert_of_mem hj)) h
          (hst i (Finset.mem_insert_self _ _)) (a j) (a i)
    rw [Finset.sum_insert hi, norm_add_sq_real, ho,
      ih (fun j hj => hst j (Finset.mem_insert_of_mem hj))
        (fun j hj k hk => hd j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)),
      Finset.sum_insert hi]
    ring

theorem terminal_pairing (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t) :
    inner ℝ F (stepClass F s t (constant s 1)) =
      ‖stepClass F s t (constant s 1)‖ ^ 2 := by
  have hp := (past t).starProjection_inner_eq_zero F _
    (stepClass_mem_past F hst (constant s 1))
  have ho := past_inner_step_zero F hst (constant s 1) (rawClass F s)
    (Submodule.starProjection_apply_mem _ _)
  have he : rawClass F t = rawClass F s + stepClass F s t (constant s 1) := by
    rw [unit_stepClass]; abel
  change inner ℝ (F - rawClass F t) (stepClass F s t (constant s 1)) = 0 at hp
  rw [inner_sub_left, he, inner_add_left, ho, zero_add, real_inner_self_eq_norm_sq] at hp
  linarith

theorem unit_energy_bound {ι : Type*} (F : JointL2) (I : Finset ι)
    (s t : ι → ℝ≥0) (hst : ∀ i ∈ I, s i ≤ t i)
    (hd : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → t i ≤ s j ∨ t j ≤ s i) :
    (∑ i ∈ I, ‖stepClass F (s i) (t i) (constant (s i) 1)‖ ^ 2) ≤ ‖F‖ ^ 2 := by
  have he := finite_energy F I s t (fun i => constant (s i) 1) hst hd
  have hh : inner ℝ F (∑ i ∈ I, stepClass F (s i) (t i) (constant (s i) 1)) =
      ∑ i ∈ I, ‖stepClass F (s i) (t i) (constant (s i) 1)‖ ^ 2 := by
    rw [inner_sum]
    exact Finset.sum_congr rfl fun i hi => terminal_pairing F (hst i hi)
  have hn := sq_nonneg ‖F - ∑ i ∈ I, stepClass F (s i) (t i) (constant (s i) 1)‖
  rw [norm_sub_sq_real, hh, he] at hn
  linarith

theorem coefficient_energy_bound {ι : Type*} (F : JointL2) (I : Finset ι)
    (s t : ι → ℝ≥0) (a : ∀ i, Coefficient (s i)) (hst : ∀ i ∈ I, s i ≤ t i)
    (hd : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → t i ≤ s j ∨ t j ≤ s i)
    (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i ∈ I, ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ‖(a i).function ω‖ ≤ C) :
    ‖∑ i ∈ I, stepClass F (s i) (t i) (a i)‖ ^ 2 ≤ C ^ 2 * ‖F‖ ^ 2 := by
  rw [finite_energy F I s t a hst hd]
  calc
    _ ≤ ∑ i ∈ I, C ^ 2 * ‖stepClass F (s i) (t i) (constant (s i) 1)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hb := step_norm_bound F (s i) (t i) (a i) C (ha i hi)
      simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg hC (norm_nonneg _))).mpr hb
    _ = C ^ 2 * ∑ i ∈ I, ‖stepClass F (s i) (t i) (constant (s i) 1)‖ ^ 2 :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (unit_energy_bound F I s t hst hd) (sq_nonneg C)

theorem process_endpoint {ι : Type*} (I : Finset ι) (s t : ι → ℝ≥0)
    (a : ∀ i, Coefficient (s i))
    (hd : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → t i ≤ s j ∨ t j ≤ s i)
    {i : ι} (hi : i ∈ I) (hpos : s i < t i) (ω : IBMSourceLaws.JointSample) :
    (∑ j ∈ I, IBMIntrinsicPredictableProcess.timeStep (s j) (t j) (a j) (t i) ω) =
      (a i).function ω := by
  classical
  rw [Finset.sum_eq_single i]
  · exact indicator_of_mem (show t i ∈ Ioc (s i) (t i) from ⟨hpos, le_rfl⟩) _
  · intro j hj hji
    apply indicator_of_notMem
    intro hm
    rcases hd i hi j hj hji.symm with h | h
    · exact (not_lt_of_ge h) hm.1
    · exact (not_le_of_gt hpos) (hm.2.trans h)
  · exact fun hn => (hn hi).elim

theorem stepClass_self (F : JointL2) (s : ℝ≥0) (a : Coefficient s) :
    stepClass F s s a = 0 := by
  apply Lp.ext
  filter_upwards [stepClass_ae F s s a, Lp.coeFn_zero ℝ 2 IBMSourceLaws.jointMeasure] with ω hs hz
  rw [hs, hz]
  simp only [step, increment, sub_self, Pi.mul_apply, Pi.zero_apply, mul_zero]

theorem actual_process_bound {ι : Type*} (F : JointL2) (I : Finset ι)
    (s t : ι → ℝ≥0) (a : ∀ i, Coefficient (s i)) (hst : ∀ i ∈ I, s i ≤ t i)
    (hd : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → t i ≤ s j ∨ t j ≤ s i)
    (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ r, ∀ᵐ ω ∂IBMSourceLaws.jointMeasure,
      ‖∑ i ∈ I, IBMIntrinsicPredictableProcess.timeStep (s i) (t i) (a i) r ω‖ ≤ C) :
    ‖∑ i ∈ I, stepClass F (s i) (t i) (a i)‖ ^ 2 ≤ C ^ 2 * ‖F‖ ^ 2 := by
  rw [finite_energy F I s t a hst hd]
  calc
    _ ≤ ∑ i ∈ I, C ^ 2 * ‖stepClass F (s i) (t i) (constant (s i) 1)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      rcases (hst i hi).eq_or_lt with he | hpos
      · rw [← he, stepClass_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]
        positivity
      · have hb : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ‖(a i).function ω‖ ≤ C := by
          filter_upwards [ha (t i)] with ω hω
          rwa [process_endpoint I s t a hd hi hpos ω] at hω
        have hn := step_norm_bound F (s i) (t i) (a i) C hb
        simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _)
          (mul_nonneg hC (norm_nonneg _))).mpr hn
    _ = C ^ 2 * ∑ i ∈ I, ‖stepClass F (s i) (t i) (constant (s i) 1)‖ ^ 2 :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (unit_energy_bound F I s t hst hd) (sq_nonneg C)

theorem bound_of_disjoint_presentation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : JointL2) (s t : ι → ℝ≥0) (a : ∀ i, Coefficient (s i))
    (u v : κ → ℝ≥0) (b : ∀ j, Coefficient (u j))
    (hst : ∀ i, s i ≤ t i) (huv : ∀ j, u j ≤ v j)
    (hd : ∀ j k, j ≠ k → v j ≤ u k ∨ v k ≤ u j)
    (C : ℝ) (hC : 0 ≤ C)
    (he : ∀ r, (fun ω => ∑ i, IBMIntrinsicPredictableProcess.timeStep (s i) (t i) (a i) r ω)
      =ᵐ[IBMSourceLaws.jointMeasure]
        (fun ω => ∑ j, IBMIntrinsicPredictableProcess.timeStep (u j) (v j) (b j) r ω))
    (ha : ∀ r, ∀ᵐ ω ∂IBMSourceLaws.jointMeasure,
      ‖∑ i, IBMIntrinsicPredictableProcess.timeStep (s i) (t i) (a i) r ω‖ ≤ C) :
    ‖∑ i, stepClass F (s i) (t i) (a i)‖ ^ 2 ≤ C ^ 2 * ‖F‖ ^ 2 := by
  classical
  rw [IBMFiniteIntervalIdentification.stochastic_integral_identification F s t a u v b hst huv he]
  apply actual_process_bound F Finset.univ u v b (fun j _ => huv j)
    (fun j _ k _ => hd j k) C hC
  intro r
  filter_upwards [ha r, he r] with ω hb hh
  rwa [hh] at hb

end OperatorDerivativeRewrite.Foundation.IBMDisjointProcessControl
