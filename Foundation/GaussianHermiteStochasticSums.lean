import Foundation.GaussianTimeSpaceHermite
import Foundation.GaussianSensitivityCore

/-! Actual predictable Hermite step fields and exact stochastic-sum errors.
No stochastic limit or predictable representation is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianHermiteStochasticSums
open InfiniteGaussian GaussianTimeSpaceHermite GaussianTimeProcess GaussianTimeHilbert
open GaussianTimeDivergence GaussianTimeProductL2 GaussianPredictableFull GaussianTimeFieldNorm
open SeparableHilbertEmbedding
attribute [local instance] timeHilbert_secondCountable

theorem brownianCore_past (T : ℝ≥0) (n : ℕ) :
    AEStronglyMeasurable[naturalFiltration T] (brownianCore T n : GaussianL2) gaussianProduct := by
  have hm : Measurable[naturalFiltration T] (fun ω => value n (process T ω) T) := by
    letI : MeasurableSpace SampleSpace := naturalFiltration T
    exact (polynomial T n).continuous_eval.measurable.comp
      (Measurable.of_eval (fun _ : Unit => (process_stronglyAdapted T).measurable))
  exact hm.stronglyMeasurable.aestronglyMeasurable.congr (brownianCore_coeFn T n).symm

theorem brownianCore_eq_pastCoefficient (T : ℝ≥0) (n : ℕ) :
    brownianCore T n = pastCoefficient (fun _ : Unit => T) (polynomial T n) := by
  apply Subtype.ext
  apply Lp.ext
  exact (brownianCore_coeFn T n).trans (pastCoefficient_coeFn (fun _ : Unit => T) (polynomial T n)).symm

def step (n : ℕ) (s t : ℝ≥0) : fullPredictable :=
  ⟨productTensor (intervalVector s t) (brownianCore s n),
    past_step_mem_fullPredictable s t _ (brownianCore_past s n)⟩

theorem integral_step (n : ℕ) (s t : ℝ≥0) (hst : s ≤ t) :
    itoIntegral (step n s t) = rankDivergence (brownianCore s n) (incrementDirection s t) := by
  rw [brownianCore_eq_pastCoefficient, rankDivergence_pastCoefficient _ _ s t (fun _ => le_rfl) hst]
  apply Lp.ext
  filter_upwards [itoIntegral_past_step s t hst (brownianCore s n) (brownianCore_past s n),
    brownianCore_coeFn s n,
    incrementProductL2_coeFn (fun _ : Unit => s) (polynomial s n) s t] with ω hi hc hp
  change itoIntegral (step n s t) ω = _ at hi
  rw [hi, hc, hp]
  rfl

theorem terminal_step_inner (n : ℕ) (s t T : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) :
    inner ℝ (brownianCore T (n + 1) : GaussianL2) (itoIntegral (step n s t)) =
      (n + 1 : ℝ) * (n.factorial : ℝ) * (s : ℝ) ^ n * ((t : ℝ) - s) := by
  rw [integral_step n s t hst]
  have hi := polynomialDerivative_rank_pairing (brownianCore T (n + 1)) (brownianCore s n)
    (incrementDirection s t)
  change inner ℝ (polynomialDerivative (core _ _ (n + 1))) _ = _ at hi
  rw [core_derivative, real_inner_smul_left, scalarTensor_pair_inner] at hi
  change (n + 1 : ℝ) * (inner ℝ (brownianCore T n : GaussianL2) (brownianCore s n : GaussianL2) *
    inner ℝ (hilbertEmbedding TimeHilbert (timeVector T)) (incrementDirection s t)) = _ at hi
  rw [brownianCore_inner, if_pos rfl, min_eq_right (show (s : ℝ) ≤ T from hst.trans htT)] at hi
  have hh : inner ℝ (hilbertEmbedding TimeHilbert (timeVector T)) (incrementDirection s t) =
      (t : ℝ) - s := by
    rw [incrementDirection, (hilbertEmbedding TimeHilbert).inner_map_map,
      ← timeVector_sub s t hst, inner_sub_right, timeVector_inner, timeVector_inner,
      min_eq_right (show (t : ℝ) ≤ T from htT),
      min_eq_right (show (s : ℝ) ≤ T from hst.trans htT)]
  rw [hh] at hi
  exact hi.symm.trans (by ring)

def stepSum (n : ℕ) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) : fullPredictable :=
  ∑ i : Fin m, step n (τ i.castSucc) (τ i.succ)

theorem stepSum_coe (n : ℕ) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) :
    (stepSum n τ : TimeProbabilityL2) =
      partitionL2 τ (fun i => (brownianCore (τ i.castSucc) n : GaussianL2)) := by
  simp only [stepSum, Submodule.coe_sum, step, partitionL2]

theorem stepSum_norm_sq (n : ℕ) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) (hτ : Monotone τ) :
    ‖stepSum n τ‖ ^ 2 = (n.factorial : ℝ) *
      ∑ i : Fin m, ((τ i.succ : ℝ) - τ i.castSucc) * (τ i.castSucc : ℝ) ^ n := by
  change ‖(stepSum n τ : TimeProbabilityL2)‖ ^ 2 = _
  rw [stepSum_coe, partitionL2_norm_sq τ hτ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [brownianCore_norm_sq]
  ring

theorem terminal_sum_inner (n : ℕ) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) (hτ : Monotone τ) :
    inner ℝ (brownianCore (τ (Fin.last m)) (n + 1) : GaussianL2) (itoIntegral (stepSum n τ)) =
      (n + 1 : ℝ) * (n.factorial : ℝ) *
        ∑ i : Fin m, ((τ i.succ : ℝ) - τ i.castSucc) * (τ i.castSucc : ℝ) ^ n := by
  rw [stepSum, map_sum, inner_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [terminal_step_inner n _ _ _ (hτ (Fin.castSucc_le_succ i)) (hτ (Fin.le_last _))]
  ring

/-- Exact error for every finite monotone partition. The deterministic power
sum must still be proved to converge before a stochastic limit is asserted. -/
theorem stochasticSum_error (n : ℕ) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) (hτ : Monotone τ) :
    ‖(brownianCore (τ (Fin.last m)) (n + 1) : GaussianL2) -
        (n + 1 : ℝ) • itoIntegral (stepSum n τ)‖ ^ 2 =
      ((n + 1).factorial : ℝ) * ((τ (Fin.last m) : ℝ) ^ (n + 1) -
        (n + 1 : ℝ) * ∑ i : Fin m, ((τ i.succ : ℝ) - τ i.castSucc) * (τ i.castSucc : ℝ) ^ n) := by
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, itoIntegral.norm_map,
    stepSum_norm_sq n τ hτ, brownianCore_norm_sq, real_inner_smul_right, terminal_sum_inner n τ hτ,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring

end OperatorDerivativeRewrite.Foundation.GaussianHermiteStochasticSums
