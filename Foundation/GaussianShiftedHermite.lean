import Foundation.GaussianHermiteIntegrand

/-! Time-shifted genuine Hermite cylinders and predictable stochastic sums. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianShiftedHermite
open InfiniteGaussian GaussianTimeSpaceHermite GaussianTimeProcess GaussianTimeHilbert
open GaussianTimeDivergence GaussianTimeProductL2 GaussianPredictableFull GaussianTimeFieldNorm
open SeparableHilbertEmbedding
attribute [local instance] timeHilbert_secondCountable

theorem incrementDirection_sub (s t : ℝ≥0) (hst : s ≤ t) :
    incrementDirection s t = hilbertEmbedding TimeHilbert (timeVector t) -
      hilbertEmbedding TimeHilbert (timeVector s) := by
  rw [← map_sub, timeVector_sub s t hst]
  rfl

theorem shifted_direction_norm (s r : ℝ≥0) :
    ‖incrementDirection s (s + r)‖ ^ 2 = (r : ℝ) := by
  rw [incrementDirection_norm_sq _ _ (by exact le_add_of_nonneg_right (by positivity)), NNReal.coe_add]
  ring

theorem shifted_direction_inner (s r q : ℝ≥0) :
    inner ℝ (incrementDirection s (s + r)) (incrementDirection s (s + q)) =
      min (r : ℝ) q := by
  rw [incrementDirection_sub _ _ (by exact le_add_of_nonneg_right (by positivity)), incrementDirection_sub _ _ (by exact le_add_of_nonneg_right (by positivity))]
  simp only [inner_sub_left, inner_sub_right, (hilbertEmbedding TimeHilbert).inner_map_map,
    timeVector_inner, NNReal.coe_add, min_add_add_left, min_self]
  rw [min_eq_left (show (s : ℝ) ≤ (s : ℝ) + (q : ℝ) from
      _root_.le_add_of_nonneg_right (NNReal.coe_nonneg q)),
    min_eq_right (show (s : ℝ) ≤ (s : ℝ) + (r : ℝ) from
      _root_.le_add_of_nonneg_right (NNReal.coe_nonneg r))]
  ring

theorem shifted_direction_future_inner (s r u v : ℝ≥0) (hru : r ≤ u) (huv : u ≤ v) :
    inner ℝ (incrementDirection s (s + r)) (incrementDirection (s + u) (s + v)) = 0 := by
  rw [incrementDirection_sub _ _ (by exact le_add_of_nonneg_right (by positivity)), inner_sub_left,
    pastDirection_inner_increment _ _ _ (add_le_add le_rfl hru) (add_le_add le_rfl huv),
    pastDirection_inner_increment _ _ _ (by exact le_add_of_nonneg_right (by positivity)) (add_le_add le_rfl huv), sub_self]

theorem shifted_direction_terminal_inner (s r u T : ℝ≥0) (hru : r ≤ u) (huT : u ≤ T) :
    inner ℝ (incrementDirection s (s + T)) (incrementDirection (s + r) (s + u)) =
      (u : ℝ) - r := by
  have he : incrementDirection (s + r) (s + u) =
      incrementDirection s (s + u) - incrementDirection s (s + r) := by
    rw [incrementDirection_sub _ _ (add_le_add le_rfl hru),
      incrementDirection_sub _ _ (by exact le_add_of_nonneg_right (by positivity)), incrementDirection_sub _ _ (by exact le_add_of_nonneg_right (by positivity))]
    module
  rw [he, inner_sub_right, shifted_direction_inner, shifted_direction_inner,
    min_eq_right (show (u : ℝ) ≤ T from huT), min_eq_right (show (r : ℝ) ≤ T from hru.trans huT)]

def incrementCore (s r : ℝ≥0) (n : ℕ) : polynomialCylindricalDomain :=
  core (incrementDirection s (s + r)) r n

theorem incrementCore_eq_wick (s r : ℝ≥0) (n : ℕ) :
    incrementCore s r n = wick (incrementDirection s (s + r)) n := by
  simp only [incrementCore, wick, shifted_direction_norm]

theorem incrementCore_coeFn (s r : ℝ≥0) (n : ℕ) :
    (incrementCore s r n : GaussianL2) =ᵐ[gaussianProduct]
      fun ω => value n (process (s + r) ω - process s ω) r := by
  filter_upwards [core_coeFn (incrementDirection s (s + r)) r n,
    process_increment_ae s (s + r) (by exact le_add_of_nonneg_right (by positivity))] with ω hc hi
  exact hc.trans (congrArg (fun z => value n z r) hi)

theorem incrementCore_memLp (s r : ℝ≥0) (n : ℕ) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun ω => value n (process (s + r) ω - process s ω) r) p gaussianProduct :=
  (polynomialDomain_memLp (incrementCore s r n) p hp).ae_eq (incrementCore_coeFn s r n)

theorem incrementCore_inner (s r q : ℝ≥0) (n m : ℕ) :
    inner ℝ (incrementCore s r n : GaussianL2) (incrementCore s q m : GaussianL2) =
      if n = m then (n.factorial : ℝ) * (min (r : ℝ) q) ^ n else 0 := by
  rw [incrementCore_eq_wick, incrementCore_eq_wick, wick_inner, shifted_direction_inner]

theorem incrementCore_norm_sq (s r : ℝ≥0) (n : ℕ) :
    ‖(incrementCore s r n : GaussianL2)‖ ^ 2 = (n.factorial : ℝ) * (r : ℝ) ^ n := by
  rw [incrementCore_eq_wick, wick_norm_sq, shifted_direction_norm]

theorem incrementCore_past (s r : ℝ≥0) (n : ℕ) :
    AEStronglyMeasurable[naturalFiltration (s + r)] (incrementCore s r n : GaussianL2)
      gaussianProduct := by
  have hm : Measurable[naturalFiltration (s + r)]
      (fun ω => value n (process (s + r) ω - process s ω) r) := by
    letI : MeasurableSpace SampleSpace := naturalFiltration (s + r)
    exact (polynomial r n).continuous_eval.measurable.comp (Measurable.of_eval (fun _ : Unit =>
      (process_stronglyAdapted (s + r)).measurable.sub
        ((process_stronglyAdapted s).measurable.mono (naturalFiltration.mono (by exact le_add_of_nonneg_right (by positivity))) le_rfl)))
  exact hm.stronglyMeasurable.aestronglyMeasurable.congr (incrementCore_coeFn s r n).symm

theorem incrementCore_gradient_future (s r u : ℝ≥0) (hru : r ≤ u) (n : ℕ) :
    (fun ω => inner ℝ (polynomialDerivative (incrementCore s r n) ω)
      (incrementDirection (s + r) (s + u))) =ᵐ[gaussianProduct] fun _ => (0 : ℝ) := by
  cases n with
  | zero =>
    rw [incrementCore, core_zero_derivative]
    filter_upwards [Lp.coeFn_zero CoefficientSpace 2 gaussianProduct] with ω hz
    simp [hz]
  | succ n =>
    rw [incrementCore, core_derivative]
    filter_upwards [Lp.coeFn_smul (n + 1 : ℝ)
      (scalarTensor (incrementDirection s (s + r)) (core (incrementDirection s (s + r)) r n)),
      scalarTensor_coeFn (incrementDirection s (s + r))
        (core (incrementDirection s (s + r)) r n)] with ω hs ht
    simp only [hs, Pi.smul_apply, ht, real_inner_smul_left,
      shifted_direction_future_inner s r r u le_rfl hru, mul_zero]

def step (s : ℝ≥0) (n : ℕ) (r u : ℝ≥0) : fullPredictable :=
  ⟨productTensor (intervalVector (s + r) (s + u)) (incrementCore s r n : GaussianL2),
    past_step_mem_fullPredictable (s + r) (s + u) (incrementCore s r n : GaussianL2)
      (incrementCore_past s r n)⟩

theorem integral_step (s : ℝ≥0) (n : ℕ) (r u : ℝ≥0) (hru : r ≤ u) :
    itoIntegral (step s n r u) =
      rankDivergence (incrementCore s r n) (incrementDirection (s + r) (s + u)) := by
  apply Lp.ext
  filter_upwards [itoIntegral_past_step _ _ (add_le_add le_rfl hru)
    (incrementCore s r n) (incrementCore_past s r n),
    rankDivergence_coeFn (incrementCore s r n) (incrementDirection (s + r) (s + u)),
    incrementCore_gradient_future s r u hru n,
    process_increment_ae (s + r) (s + u) (add_le_add le_rfl hru)] with ω hj hd hz hi
  change itoIntegral (step s n r u) ω = _ at hj
  change firstChaosEmbedding (incrementDirection (s + r) (s + u)) ω = _ at hi
  rw [hj, hd, hz, hi, sub_zero]

theorem terminal_step_inner (s : ℝ≥0) (n : ℕ) (r u T : ℝ≥0) (hru : r ≤ u) (huT : u ≤ T) :
    inner ℝ (incrementCore s T (n + 1) : GaussianL2) (itoIntegral (step s n r u)) =
      (n + 1 : ℝ) * (n.factorial : ℝ) * (r : ℝ) ^ n * ((u : ℝ) - r) := by
  rw [integral_step s n r u hru]
  have hi := polynomialDerivative_rank_pairing (incrementCore s T (n + 1))
    (incrementCore s r n) (incrementDirection (s + r) (s + u))
  change inner ℝ (polynomialDerivative (core _ _ (n + 1))) _ = _ at hi
  rw [core_derivative, real_inner_smul_left, scalarTensor_pair_inner] at hi
  change (n + 1 : ℝ) * (inner ℝ (incrementCore s T n : GaussianL2) (incrementCore s r n : GaussianL2) *
    inner ℝ (incrementDirection s (s + T)) (incrementDirection (s + r) (s + u))) = _ at hi
  rw [incrementCore_inner, if_pos rfl, min_eq_right (show (r : ℝ) ≤ T from hru.trans huT),
    shifted_direction_terminal_inner s r u T hru huT] at hi
  exact hi.symm.trans (by ring)

def stepSum (s : ℝ≥0) (n : ℕ) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) : fullPredictable :=
  ∑ i : Fin m, step s n (τ i.castSucc) (τ i.succ)

theorem stepSum_coe (s : ℝ≥0) (n : ℕ) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) :
    (stepSum s n τ : TimeProbabilityL2) =
      partitionL2 (fun i => s + τ i) (fun i => (incrementCore s (τ i.castSucc) n : GaussianL2)) := by
  simp only [stepSum, Submodule.coe_sum, step, partitionL2, NNReal.coe_add]

theorem stepSum_norm_sq (s : ℝ≥0) (n : ℕ) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0)
    (hτ : Monotone τ) :
    ‖stepSum s n τ‖ ^ 2 = (n.factorial : ℝ) *
      ∑ i : Fin m, ((τ i.succ : ℝ) - τ i.castSucc) * (τ i.castSucc : ℝ) ^ n := by
  change ‖(stepSum s n τ : TimeProbabilityL2)‖ ^ 2 = _
  rw [stepSum_coe, partitionL2_norm_sq _ (fun i j hij => add_le_add le_rfl (hτ hij)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [incrementCore_norm_sq]
  simp only [NNReal.coe_add]
  ring

theorem terminal_sum_inner (s : ℝ≥0) (n : ℕ) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0)
    (hτ : Monotone τ) :
    inner ℝ (incrementCore s (τ (Fin.last m)) (n + 1) : GaussianL2) (itoIntegral (stepSum s n τ)) =
      (n + 1 : ℝ) * (n.factorial : ℝ) *
        ∑ i : Fin m, ((τ i.succ : ℝ) - τ i.castSucc) * (τ i.castSucc : ℝ) ^ n := by
  rw [stepSum, map_sum, inner_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [terminal_step_inner s n _ _ _ (hτ (Fin.castSucc_le_succ i)) (hτ (Fin.le_last _))]
  ring

theorem stochasticSum_error (s : ℝ≥0) (n : ℕ) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0)
    (hτ : Monotone τ) :
    ‖(incrementCore s (τ (Fin.last m)) (n + 1) : GaussianL2) -
        (n + 1 : ℝ) • itoIntegral (stepSum s n τ)‖ ^ 2 =
      ((n + 1).factorial : ℝ) * ((τ (Fin.last m) : ℝ) ^ (n + 1) -
        (n + 1 : ℝ) * ∑ i : Fin m, ((τ i.succ : ℝ) - τ i.castSucc) * (τ i.castSucc : ℝ) ^ n) := by
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, itoIntegral.norm_map,
    stepSum_norm_sq s n τ hτ, incrementCore_norm_sq, real_inner_smul_right,
    terminal_sum_inner s n τ hτ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring

end OperatorDerivativeRewrite.Foundation.GaussianShiftedHermite
