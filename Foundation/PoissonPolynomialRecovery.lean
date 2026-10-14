import Foundation.PoissonCharlierLadder
import Foundation.DivergenceKernelContrast

/-! Genuine unique Poisson divergence recovery for finite positive Charlier
expansions. No unproved polynomial completeness is used. -/
noncomputable section
open MeasureTheory
open scoped NNReal
set_option backward.isDefEq.respectTransparency false

namespace OperatorDerivativeRewrite.Foundation.PoissonPolynomialRecovery
open PoissonDifferenceCore PoissonDifferenceOperators PoissonMaximalOperators PoissonCharlierLadder

def target (rate : ℝ≥0) (hr : 0 < rate) {N : ℕ} (c : Fin N → ℝ) : ScalarL2 rate :=
  ∑ i, c i • scalar rate hr (i.val+1)

def recovery (rate : ℝ≥0) (hr : 0 < rate) {N : ℕ} (c : Fin N → ℝ) : FieldL2 rate :=
  ∑ i, c i • field rate hr i.val

theorem recovery_graph (rate : ℝ≥0) (hr : 0 < rate) {N : ℕ} (c : Fin N → ℝ) :
    (recovery rate hr c,target rate hr c) ∈ (maximalDivergence rate hr).graph := by
  rw [recovery,target,prod_mk_sum]
  exact (maximalDivergence rate hr).graph.sum_mem
    (fun i _ => (maximalDivergence rate hr).graph.smul_mem (c i) (raising_graph rate hr i.val))

theorem recovery_unique (rate : ℝ≥0) (hr : 0 < rate) {N : ℕ} (c : Fin N → ℝ)
    (u : FieldL2 rate) (hu : (u,target rate hr c) ∈ (maximalDivergence rate hr).graph) :
    u=recovery rate hr c := by
  have hz : (u-recovery rate hr c,0) ∈ (maximalDivergence rate hr).graph := by
    simpa only [Prod.mk_sub_mk,sub_self] using
      (maximalDivergence rate hr).graph.sub_mem hu (recovery_graph rate hr c)
  exact sub_eq_zero.mp ((DivergenceKernelContrast.poisson_divergence_zero_iff rate hr _).mp hz)

theorem target_centered (rate : ℝ≥0) (hr : 0 < rate) {N : ℕ} (c : Fin N → ℝ) :
    (∫ k, target rate hr c k ∂poissonLaw rate)=0 := by
  have hi : inner ℝ (scalar rate hr 0) (target rate hr c)=0 := by
    simp [target,inner_sum,inner_smul_right,scalar_inner]
  calc
    _ = ∫ k, inner ℝ (scalar rate hr 0 k) (target rate hr c k) ∂poissonLaw rate := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun k => by
        change target rate hr c k = inner ℝ (scalar rate hr 0 k) (target rate hr c k)
        rw [scalar_apply,value_zero]
        simp
    _ = inner ℝ (scalar rate hr 0) (target rate hr c) := (L2_inner_eq_integral _ _).symm
    _ = 0 := hi

theorem recovery_norm_sq (rate : ℝ≥0) (hr : 0 < rate) {N : ℕ} (c : Fin N → ℝ) :
    ‖recovery rate hr c‖^2 =
      ∑ i, (c i)^2*(i.val.factorial : ℝ)*(rate : ℝ)^(i.val+1) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [recovery,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,
    field_inner,scalar_inner]
  simp [Fin.val_inj,mul_ite,ite_mul,mul_assoc,mul_left_comm,mul_comm,pow_succ,pow_two]

theorem target_norm_sq (rate : ℝ≥0) (hr : 0 < rate) {N : ℕ} (c : Fin N → ℝ) :
    ‖target rate hr c‖^2 =
      ∑ i, (i.val+1 : ℝ)*(c i)^2*(i.val.factorial : ℝ)*(rate : ℝ)^(i.val+1) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [target,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,scalar_inner]
  simp [Fin.val_inj,mul_ite,ite_mul,mul_assoc,mul_left_comm,pow_two,Nat.factorial_succ]

/-- Uniform norm-one recovery on every finite centered polynomial sector.
Extension to all Poisson L2 still needs an actual density theorem. -/
theorem recovery_norm_le (rate : ℝ≥0) (hr : 0 < rate) {N : ℕ} (c : Fin N → ℝ) :
    ‖recovery rate hr c‖ ≤ ‖target rate hr c‖ := by
  have hs : ‖recovery rate hr c‖^2 ≤ ‖target rate hr c‖^2 := by
    rw [recovery_norm_sq,target_norm_sq]
    apply Finset.sum_le_sum
    intro i _
    have hn : (1 : ℝ) ≤ i.val+1 := by
      have hi : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
      linarith
    have hp : 0 ≤ (c i)^2*(i.val.factorial : ℝ)*(rate : ℝ)^(i.val+1) := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) hp]
  nlinarith [norm_nonneg (recovery rate hr c),norm_nonneg (target rate hr c)]

end OperatorDerivativeRewrite.Foundation.PoissonPolynomialRecovery
