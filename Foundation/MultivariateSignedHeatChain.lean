import Foundation.MultivariateDirectionalKernel

/-! Actual complete directional heat operators and their finite signed-kernel realization. -/
noncomputable section

open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.MultivariateSignedHeatChain
open MultivariateFactorialDomain MultivariateFactorialHeat MultivariateDirectionalKernel
open MeasureTheory
variable {ι : Type*} [DecidableEq ι]

structure Step (ι : Type*) where
  time : ℝ≥0
  positive : 0 < time
  direction : ι → ℝ
  bounded : ∀ i, |direction i| ≤ 1

def stepOperator (m : ℕ) (s : Step ι) : H ι →L[ℝ] H ι :=
  evolution (2*m) ((-1:ℝ)^(m+1)*(s.time:ℝ)) s.direction s.bounded

def stepTransport (m : ℕ) (hm : 0 < m) (s : Step ι) :
    MvPolynomial ι ℝ →ₗ[ℝ] MvPolynomial ι ℝ :=
  transport (2*m) (by omega) ((-1:ℝ)^(m+1)*(s.time:ℝ)) s.direction

def operator (m : ℕ) : List (Step ι) → H ι →L[ℝ] H ι
  | [] => ContinuousLinearMap.id ℝ _
  | s::ss => (stepOperator m s).comp (operator m ss)

def polynomialTransport (m : ℕ) (hm : 0 < m) :
    List (Step ι) → MvPolynomial ι ℝ →ₗ[ℝ] MvPolynomial ι ℝ
  | [] => LinearMap.id
  | s::ss => (stepTransport m hm s).comp (polynomialTransport m hm ss)

def totalTime (ss : List (Step ι)) : ℝ := (ss.map (fun s => (s.time:ℝ))).sum

theorem stepOperator_core (m : ℕ) (hm : 0 < m) (s : Step ι) (P : MvPolynomial ι ℝ) :
    stepOperator m s (polynomial P) = polynomial (stepTransport m hm s P) :=
  completed_transport (2*m) (by omega) _ _ _ _

theorem operator_core (m : ℕ) (hm : 0 < m) (ss : List (Step ι)) (P : MvPolynomial ι ℝ) :
    operator m ss (polynomial P) = polynomial (polynomialTransport m hm ss P) := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    change stepOperator m s (operator m ss (polynomial P)) = _
    rw [ih, stepOperator_core m hm s]
    rfl

theorem stepOperator_bound (m : ℕ) (s : Step ι) :
    ‖stepOperator m s‖ ≤ Real.exp (s.time:ℝ) := by
  have h := evolution_bound (2*m) ((-1:ℝ)^(m+1)*(s.time:ℝ)) s.direction s.bounded
  simpa only [stepOperator, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg s.time.coe_nonneg] using h

theorem operator_bound (m : ℕ) (ss : List (Step ι)) :
    ‖operator m ss‖ ≤ Real.exp (totalTime ss) := by
  induction ss with
  | nil => simpa only [operator, totalTime, List.map_nil, List.sum_nil, Real.exp_zero] using
      ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := H ι)
  | cons s ss ih =>
    calc
      ‖operator m (s::ss)‖ ≤ ‖stepOperator m s‖ * ‖operator m ss‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ Real.exp (s.time:ℝ) * Real.exp (totalTime ss) :=
        mul_le_mul (stepOperator_bound m s) ih (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (totalTime (s::ss)) := by
        simp only [totalTime, List.map_cons, List.sum_cons, Real.exp_add]

def nestedIntegral (m : ℕ) (hm : 0 < m) (P : MvPolynomial ι ℝ) :
    List (Step ι) → (ι → ℝ) → ℝ
  | [], x => MvPolynomial.eval x P
  | s::ss, x => ∫ z : ℝ, nestedIntegral m hm P ss (fun i => x i + z*s.direction i) *
      HigherHeatSignedLaws.realKernel m hm s.time s.positive z

omit [DecidableEq ι] in
theorem nestedIntegral_eq (m : ℕ) (hm : 0 < m) (P : MvPolynomial ι ℝ)
    (ss : List (Step ι)) (x : ι → ℝ) :
    nestedIntegral m hm P ss x = MvPolynomial.eval x (polynomialTransport m hm ss P) := by
  induction ss generalizing x with
  | nil => rfl
  | cons s ss ih =>
    simp only [nestedIntegral, ih]
    exact actual_kernel_transport m hm s.time s.positive s.direction x _

omit [DecidableEq ι] in
theorem nested_step_integrable (m : ℕ) (hm : 0 < m) (P : MvPolynomial ι ℝ)
    (ss : List (Step ι)) (s : Step ι) (x : ι → ℝ) :
    Integrable (fun z : ℝ => nestedIntegral m hm P ss (fun i => x i + z*s.direction i) *
      HigherHeatSignedLaws.realKernel m hm s.time s.positive z) := by
  simp only [nestedIntegral_eq]
  exact actual_kernel_integrable m hm s.time s.positive s.direction x _

omit [DecidableEq ι] in
theorem polynomialTransport_bound (m : ℕ) (hm : 0 < m) (ss : List (Step ι))
    (P : MvPolynomial ι ℝ) :
    ‖polynomial (polynomialTransport m hm ss P)‖ ≤ Real.exp (totalTime ss) * ‖polynomial P‖ := by
  classical
  rw [← operator_core]
  exact (operator m ss).le_of_opNorm_le (operator_bound m ss) _

end OperatorDerivativeRewrite.Foundation.MultivariateSignedHeatChain
