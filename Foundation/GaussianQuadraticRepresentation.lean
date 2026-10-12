import Foundation.GaussianBrownianQuadraticVariation
import Foundation.GaussianBrownianGeneratedSpace

/-! Constructive predictable representation of the centered Brownian square
by convergence of the actual left-point stochastic sums. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianQuadraticRepresentation
open InfiniteGaussian GaussianTimeProcess GaussianTimeHilbert GaussianTimeDivergence
open GaussianPredictableFull GaussianPredictableAdjoint GaussianSensitivityCore
open GaussianQuadraticIncrement GaussianBrownianQuadraticVariation SeparableHilbertEmbedding
attribute [local instance] timeHilbert_secondCountable
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe

def leftStepField {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) : fullPredictable :=
  ∑ i : Fin n, pastStep (τ i.castSucc) (τ i.succ) (fun _ : Fin 1 => τ i.castSucc)
    (fun _ => le_rfl) (MvPolynomial.X 0)

theorem integral_leftStepField_coeFn {n : ℕ}
    (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ) :
    itoIntegral (leftStepField τ) =ᵐ[gaussianProduct] fun ω =>
      ∑ i : Fin n, process (τ i.castSucc) ω *
        (process (τ i.succ) ω - process (τ i.castSucc) ω) := by
  have he : itoIntegral (leftStepField τ) = ∑ i : Fin n,
      incrementProductL2 (fun _ : Fin 1 => τ i.castSucc) (MvPolynomial.X 0)
        (τ i.castSucc) (τ i.succ) := by
    rw [leftStepField, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact ito_pastStep _ _ (hτ (Fin.castSucc_le_succ i)) _ _ _
  rw [he]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin n =>
    incrementProductL2 (fun _ : Fin 1 => τ i.castSucc) (MvPolynomial.X 0)
      (τ i.castSucc) (τ i.succ)), ae_all_iff.mpr (fun i : Fin n =>
        incrementProductL2_coeFn (fun _ : Fin 1 => τ i.castSucc) (MvPolynomial.X 0)
          (τ i.castSucc) (τ i.succ))] with ω hs hi
  rw [hs]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [MvPolynomial.eval_X] using hi i

def terminalSquare (T : ℝ≥0) : GaussianL2 :=
  centeredSquare (hilbertEmbedding TimeHilbert (timeVector T))

theorem terminalSquare_coeFn (T : ℝ≥0) :
    terminalSquare T =ᵐ[gaussianProduct] fun ω => (process T ω) ^ 2 - (T : ℝ) := by
  have h := centeredSquare_coeFn (hilbertEmbedding TimeHilbert (timeVector T))
  rw [(hilbertEmbedding TimeHilbert).norm_map, timeVector_norm_sq] at h
  exact h

/-- Finite telescoping with the actual Ito integral; the random square sum
is retained until its separately proved L2 limit is taken. -/
theorem leftStep_square_identity (T : ℝ≥0) (n : ℕ) :
    (2 : ℝ) • itoIntegral (leftStepField (uniformTime T n)) =
      terminalSquare T - (quadraticVariation (uniformTime T n) - (T : ℝ) • gaussianOne) := by
  let τ := uniformTime T n
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (2 : ℝ) (itoIntegral (leftStepField τ)),
    integral_leftStepField_coeFn τ (uniformTime_monotone T n),
    Lp.coeFn_sub (terminalSquare T) (quadraticVariation τ - (T : ℝ) • gaussianOne),
    Lp.coeFn_sub (quadraticVariation τ) ((T : ℝ) • gaussianOne),
    Lp.coeFn_smul (T : ℝ) gaussianOne, gaussianOne_coeFn, terminalSquare_coeFn T,
    quadraticVariation_coeFn τ (uniformTime_monotone T n), process_zero_ae]
    with ω h2 hi hsub hqsub hT h1 hf hq h0
  rw [h2, hsub]
  simp only [Pi.smul_apply, Pi.sub_apply, hi, hqsub, hT, h1, smul_eq_mul, mul_one, hf, hq]
  have ht := sum_fin_differences (fun i : Fin (n + 2) => (process (τ i) ω) ^ 2)
  have hτ0 : τ 0 = 0 := (uniformTime_endpoints T n).1
  have hτT : τ (Fin.last (n + 1)) = T := (uniformTime_endpoints T n).2
  rw [hτ0, hτT, h0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero] at ht
  have he : (∑ i : Fin (n + 1),
      ((process (τ i.succ) ω) ^ 2 - (process (τ i.castSucc) ω) ^ 2)) =
      2 * (∑ i : Fin (n + 1), process (τ i.castSucc) ω *
        (process (τ i.succ) ω - process (τ i.castSucc) ω)) +
      ∑ i : Fin (n + 1), (process (τ i.succ) ω - process (τ i.castSucc) ω) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  linarith

theorem leftStep_integral_tendsto (T : ℝ≥0) :
    Tendsto (fun n => itoIntegral (leftStepField (uniformTime T n))) atTop
      (𝓝 ((1 / 2 : ℝ) • terminalSquare T)) := by
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => terminalSquare T) atTop
    (𝓝 (terminalSquare T))).sub
    ((uniform_quadraticVariation_tendsto T).sub_const ((T : ℝ) • gaussianOne))
  have hs := ht.const_smul (1 / 2 : ℝ)
  simp only [sub_self, sub_zero] at hs
  convert hs using 1
  ext n
  rw [← leftStep_square_identity, smul_smul]
  norm_num

/-- Existence is derived from stochastic sums and the proved closed range;
it is not an assumption of predictable representation. -/
theorem terminalSquare_half_mem_integralRange (T : ℝ≥0) :
    (1 / 2 : ℝ) • terminalSquare T ∈ itoIntegral.toLinearMap.range :=
  GaussianBrownianGeneratedSpace.integralRange_isClosed.mem_of_tendsto
    (leftStep_integral_tendsto T) (Eventually.of_forall fun n =>
      ⟨leftStepField (uniformTime T n), rfl⟩)

def quadraticIntegrand (T : ℝ≥0) : fullPredictable :=
  predictableAdjoint ((1 / 2 : ℝ) • terminalSquare T)

theorem integral_quadraticIntegrand (T : ℝ≥0) :
    itoIntegral (quadraticIntegrand T) = (1 / 2 : ℝ) • terminalSquare T := by
  obtain ⟨u, hu⟩ := terminalSquare_half_mem_integralRange T
  change itoIntegral u = (1 / 2 : ℝ) • terminalSquare T at hu
  change itoIntegral (predictableAdjoint _) = _
  rw [← hu, predictableAdjoint_integral]

/-- One explicitly constructed predictable integrand is the L2 limit of the
left-endpoint Brownian fields. A joint representative is a separate question. -/
theorem leftStepField_tendsto (T : ℝ≥0) :
    Tendsto (fun n => leftStepField (uniformTime T n)) atTop (𝓝 (quadraticIntegrand T)) := by
  have h := predictableAdjoint.continuous.continuousAt.tendsto.comp (leftStep_integral_tendsto T)
  simpa only [Function.comp_def, predictableAdjoint_integral, quadraticIntegrand] using h

theorem quadratic_stochastic_identity (T : ℝ≥0) :
    (2 : ℝ) • itoIntegral (quadraticIntegrand T) + (T : ℝ) • gaussianOne =
      terminalSquare T + (T : ℝ) • gaussianOne := by
  rw [integral_quadraticIntegrand, smul_smul]
  norm_num

end OperatorDerivativeRewrite.Foundation.GaussianQuadraticRepresentation
