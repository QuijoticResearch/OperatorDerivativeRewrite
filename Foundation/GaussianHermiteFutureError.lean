import Foundation.GaussianShiftedRepresentation
import Foundation.GaussianPastFutureProducts

/-! The whole Hermite stochastic-sum error is a measurable function of the
future-increment process. Its L2 error remains controlled after multiplication
by an arbitrary square-integrable measurable past coefficient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianHermiteFutureError
open InfiniteGaussian GaussianTimeSpaceHermite GaussianShiftedHermite GaussianShiftedRepresentation
open GaussianTimeProcess GaussianPredictableFull GaussianBrownianQuadraticVariation
open GaussianPastFutureProducts

def sumFunctional (n : ℕ) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) (z : ℝ≥0 → ℝ) : ℝ :=
  ∑ i : Fin m, value n (z (τ i.castSucc)) (τ i.castSucc) * (z (τ i.succ) - z (τ i.castSucc))

def errorFunctional (n : ℕ) (T : ℝ≥0) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) (z : ℝ≥0 → ℝ) : ℝ :=
  value (n + 1) (z T) T - (n + 1 : ℝ) * sumFunctional n τ z

theorem value_functional_measurable (n : ℕ) (r : ℝ≥0) :
    Measurable (fun z : ℝ≥0 → ℝ => value n (z r) r) :=
  (polynomial r n).continuous_eval.measurable.comp
    (Measurable.of_eval (fun _ : Unit => measurable_pi_apply r))

theorem sumFunctional_measurable (n : ℕ) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) :
    Measurable (sumFunctional n τ) :=
  Finset.measurable_sum _ (fun i _ => (value_functional_measurable n (τ i.castSucc)).mul
    ((measurable_pi_apply (τ i.succ)).sub (measurable_pi_apply (τ i.castSucc))))

theorem errorFunctional_measurable (n : ℕ) (T : ℝ≥0) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) :
    Measurable (errorFunctional n T τ) :=
  (value_functional_measurable (n + 1) T).sub ((sumFunctional_measurable n τ).const_mul _)

theorem integral_stepSum_coeFn (s : ℝ≥0) (n : ℕ) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0)
    (hτ : Monotone τ) :
    itoIntegral (stepSum s n τ) =ᵐ[gaussianProduct] futureValue s (sumFunctional n τ) := by
  rw [stepSum, map_sum]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin m =>
    itoIntegral (step s n (τ i.castSucc) (τ i.succ))), ae_all_iff.mpr (fun i : Fin m =>
      itoIntegral_past_step (s + τ i.castSucc) (s + τ i.succ)
        (add_le_add le_rfl (hτ (Fin.castSucc_le_succ i)))
        (incrementCore s (τ i.castSucc) n) (incrementCore_past s (τ i.castSucc) n)),
    ae_all_iff.mpr (fun i : Fin m => incrementCore_coeFn s (τ i.castSucc) n)] with ω hs hi hc
  rw [hs]
  simp only [Finset.sum_apply, futureValue, sumFunctional, futureProcess]
  apply Finset.sum_congr rfl
  intro i _
  change itoIntegral (step s n (τ i.castSucc) (τ i.succ)) ω = _
  have h := hi i
  change itoIntegral (step s n (τ i.castSucc) (τ i.succ)) ω = _ at h
  rw [h, hc i]
  ring

theorem error_coeFn (s : ℝ≥0) (n : ℕ) (T : ℝ≥0) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0)
    (hτ : Monotone τ) :
    ((incrementCore s T (n + 1) : GaussianL2) - (n + 1 : ℝ) • itoIntegral (stepSum s n τ))
      =ᵐ[gaussianProduct] futureValue s (errorFunctional n T τ) := by
  filter_upwards [Lp.coeFn_sub (incrementCore s T (n + 1) : GaussianL2)
    ((n + 1 : ℝ) • itoIntegral (stepSum s n τ)),
    Lp.coeFn_smul (n + 1 : ℝ) (itoIntegral (stepSum s n τ)),
    incrementCore_coeFn s T (n + 1), integral_stepSum_coeFn s n τ hτ] with ω hs hm hc hi
  simp only [hs, Pi.sub_apply, hm, Pi.smul_apply, smul_eq_mul, hc, hi,
    futureValue, errorFunctional, futureProcess]

theorem error_memLp (s : ℝ≥0) (n : ℕ) (T : ℝ≥0) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0)
    (hτ : Monotone τ) : MemLp (futureValue s (errorFunctional n T τ)) 2 gaussianProduct :=
  (Lp.memLp _).ae_eq (error_coeFn s n T τ hτ)

theorem error_sq_integral (s : ℝ≥0) (n : ℕ) (T : ℝ≥0) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0)
    (hτ : Monotone τ) :
    (∫ ω, futureValue s (errorFunctional n T τ) ω ^ 2 ∂gaussianProduct) =
      ‖(incrementCore s T (n + 1) : GaussianL2) - (n + 1 : ℝ) • itoIntegral (stepSum s n τ)‖ ^ 2 := by
  let E : GaussianL2 := (incrementCore s T (n + 1) : GaussianL2) -
    (n + 1 : ℝ) • itoIntegral (stepSum s n τ)
  change _ = ‖E‖ ^ 2
  have hn : ‖E‖ ^ 2 = ∫ ω, E ω ^ 2 ∂gaussianProduct := by
    rw [← real_inner_self_eq_norm_sq, L2_inner_eq_integral]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => by simp [Real.inner_apply, pow_two]
  rw [hn]
  apply integral_congr_ae
  filter_upwards [error_coeFn s n T τ hτ] with ω he
  exact (congrArg (fun x : ℝ => x ^ 2) he).symm

theorem weighted_error_sq_integrable (s : ℝ≥0) (n : ℕ) (T : ℝ≥0) (N : ℕ)
    {a : (Iic s → ℝ) → ℝ} (ha : Measurable a)
    (hA : MemLp (GaussianPredictableStep.pastCoefficient process s a) 2 gaussianProduct) :
    Integrable (fun ω => (GaussianPredictableStep.pastCoefficient process s a ω *
      futureValue s (errorFunctional n T (uniformTime T N)) ω) ^ 2) gaussianProduct :=
  past_future_sq_integrable s ha (errorFunctional_measurable n T _) hA
    (error_memLp s n T _ (uniformTime_monotone T N))

theorem weighted_error_sq_tendsto (s : ℝ≥0) (n : ℕ) (T : ℝ≥0)
    {a : (Iic s → ℝ) → ℝ} (ha : Measurable a)
    (hA : MemLp (GaussianPredictableStep.pastCoefficient process s a) 2 gaussianProduct) :
    Tendsto (fun N => ∫ ω, (GaussianPredictableStep.pastCoefficient process s a ω *
      futureValue s (errorFunctional n T (uniformTime T N)) ω) ^ 2 ∂gaussianProduct) atTop (𝓝 0) := by
  apply weighted_future_error_tendsto s ha (fun N => errorFunctional_measurable n T _) hA
    (fun N => error_memLp s n T _ (uniformTime_monotone T N))
  simp_rw [error_sq_integral s n T _ (uniformTime_monotone T _)]
  have ht : Tendsto (fun N : ℕ => ((n + 1).factorial : ℝ) * (n + 1 : ℝ) *
      (T : ℝ) ^ (n + 1) / (N + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  exact squeeze_zero (fun N => sq_nonneg _) (fun N => uniform_stochasticSum_error_bound s n N T) ht

end OperatorDerivativeRewrite.Foundation.GaussianHermiteFutureError
